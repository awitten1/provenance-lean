/-
  DuckDB logical plan ingestion (minimal: SEQ_SCAN / FILTER / PROJECTION).

  Parses the JSON shape captured by `bench/capture.sh`: a single-element array
  wrapping a recursive `{name, children, extra_info}` tree. No semantics yet —
  translation to `Provenance.Query` happens elsewhere.
-/

import Lean.Data.Json
import Lean.Data.Json.Parser

namespace Provenance.Plan

open Lean (Json)

/-! ## Expressions

The textual expressions DuckDB emits in `Expressions`/`Filters` are tiny:
comparisons between a column reference and a literal (or another column),
optionally wrapped in parens, with no-op `CAST(<lit> AS <type>)` wrappers
around literals. AND-conjunction is *structural* — DuckDB pre-splits
conjuncts into JSON arrays — so we never see `AND` inside a single string.

We also reuse this parser for projection expressions, which in our current
corpus are bare column names (e.g. `"a"`, `"b"`).
-/

inductive Op
  | lt | le | gt | ge | eq | ne
  deriving Repr, DecidableEq, Inhabited

namespace Op
def toString : Op → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .eq => "=" | .ne => "<>"
instance : ToString Op := ⟨toString⟩
end Op

inductive Expr
  | col (name : String)
  | int (n : Int)
  | cmp (op : Op) (lhs rhs : Expr)
  deriving Repr, DecidableEq, Inhabited

namespace Expr

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Strip matched outer parens. Iterates: `((x))` → `(x)` → `x`. -/
private partial def stripOuterParens (s : String) : String := Id.run do
  let s := s.trim
  if s.length < 2 || s.front != '(' || s.back != ')' then return s
  let inner := s.toSubstring.drop 1 |>.dropRight 1 |>.toString
  -- The opening `(` matches the closing `)` only if depth stays > 0 over the
  -- interior; otherwise the parens are not a matched outer pair (e.g. "(a)+(b)").
  let mut depth := 1
  let mut ok := true
  for c in inner.toList do
    if depth == 0 then ok := false; break
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
  if ok then return stripOuterParens inner else return s

/-- Replace every `CAST(<atom> AS <type>)` with `<atom>`. -/
private partial def stripCasts (s : String) : String := Id.run do
  let chars := s.toList
  let n := chars.length
  let mut result : String := ""
  let mut i := 0
  while i < n do
    let prefixOk := i + 5 ≤ n ∧ String.ofList (chars.drop i |>.take 5) == "CAST("
    if prefixOk then
      let mut depth := 1
      let mut j := i + 5
      let mut endPos := n
      while j < n do
        let c := chars[j]!
        if c == '(' then depth := depth + 1
        else if c == ')' then
          depth := depth - 1
          if depth == 0 then endPos := j; j := n; continue
        j := j + 1
      let inside := String.ofList (chars.drop (i + 5) |>.take (endPos - (i + 5)))
      let atom := match inside.splitOn " AS " with
                  | a :: _ => a
                  | []     => inside
      result := result ++ atom
      i := endPos + 1
    else
      result := result.push chars[i]!
      i := i + 1
  return result

/-- Find the first top-level (paren-depth 0) occurrence of any of `ops`,
preferring longer matches at each position. Returns `(prefix, op, suffix)`. -/
private def splitOnTopOp (s : String) (ops : List String) :
    Option (String × String × String) := Id.run do
  let chars := s.toList
  let n := chars.length
  let mut depth := 0
  let mut i := 0
  while i < n do
    let c := chars[i]!
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    else if depth == 0 then
      for op in ops do
        if i + op.length ≤ n then
          let slice := String.ofList (chars.drop i |>.take op.length)
          if slice == op then
            let pre  := String.ofList (chars.take i)
            let post := String.ofList (chars.drop (i + op.length))
            return some (pre, op, post)
    i := i + 1
  return none

private def parseOperand (s : String) : Except String Expr := do
  let s := (stripOuterParens (stripCasts s)).trim
  if s.isEmpty then throw "empty operand"
  if (s.front.isDigit || s.front == '-') then
    match s.toInt? with
    | some n => return .int n
    | none   => throw s!"bad integer literal: '{s}'"
  else if s.all isIdentChar then
    return .col s
  else
    throw s!"unrecognized operand: '{s}'"

/-- Parse a single expression string. Falls back to operand-only if no
top-level comparison operator is found. -/
def parse (raw : String) : Except String Expr := do
  let s := stripOuterParens (stripCasts raw) |>.trim
  let ops := ["<=", ">=", "<>", "!=", "<", ">", "="]
  match splitOnTopOp s ops with
  | none => parseOperand s
  | some (lhs, op, rhs) =>
    let some op' := Op.parse? op | throw s!"unknown op: '{op}'"
    return .cmp op' (← parseOperand lhs) (← parseOperand rhs)
where
  Op.parse? : String → Option Op
    | "<"  => some .lt | "<=" => some .le
    | ">"  => some .gt | ">=" => some .ge
    | "="  => some .eq | "<>" => some .ne | "!=" => some .ne
    | _    => none

end Expr

/-! ## Logical plan -/

inductive LogicalPlan where
  | seqScan    (table : String)
  | filter     (preds : List Expr) (child : LogicalPlan)
  | projection (exprs : List Expr) (child : LogicalPlan)
  deriving Repr, DecidableEq, Inhabited

namespace LogicalPlan

/-- DuckDB writes each `extra_info` field as either a single string (for one
expression) or an array of strings (for many). Normalise to a list of
parsed `Expr`s. Empty string → empty list. -/
private def parseExprField? (info : Json) (key : String) : Except String (List Expr) := do
  match info.getObjVal? key with
  | .error _ => return []
  | .ok v =>
    match v with
    | .str s =>
      if s.trim.isEmpty then return []
      let e ← Expr.parse s
      return [e]
    | .arr a =>
      let xs ← a.toList.mapM fun j => do
        let s ← j.getStr?
        Expr.parse s
      return xs
    | _ => throw s!"field '{key}' is neither string nor array: {v.compress}"

/-- "memory.main.r" → "r". Strip the catalog/schema prefix DuckDB prepends. -/
private def shortTableName (qualified : String) : String :=
  match qualified.splitOn "." with
  | []      => qualified
  | [t]     => t
  | parts   => parts[parts.length - 1]!

/-- Recursively translate one node of the JSON plan tree.
Desugars scan-baked filters: a `SEQ_SCAN` carrying a non-empty `Filters`
field becomes `filter preds (seqScan table)`. -/
partial def fromJson? (j : Json) : Except String LogicalPlan := do
  let nm ← j.getObjValAs? String "name"
  let extra := (j.getObjVal? "extra_info").toOption.getD .null
  let kids := (j.getObjValAs? (Array Json) "children").toOption.getD #[]
  let kids ← kids.toList.mapM fromJson?
  match nm with
  | "SEQ_SCAN" =>
    let table := shortTableName (← extra.getObjValAs? String "Table")
    let preds ← parseExprField? extra "Filters"
    let scan := LogicalPlan.seqScan table
    return if preds.isEmpty then scan else LogicalPlan.filter preds scan
  | "FILTER" =>
    let [c] := kids | throw s!"FILTER expected 1 child, got {kids.length}"
    let preds ← parseExprField? extra "Expressions"
    return LogicalPlan.filter preds c
  | "PROJECTION" =>
    let [c] := kids | throw s!"PROJECTION expected 1 child, got {kids.length}"
    let exprs ← parseExprField? extra "Expressions"
    return LogicalPlan.projection exprs c
  | other => throw s!"unsupported plan node: {other}"

/-- Parse the top-level array DuckDB emits: a 1-element array wrapping the
plan root. -/
def fromTopJson? (j : Json) : Except String LogicalPlan := do
  let arr ← j.getArr?
  match arr with
  | #[root] => fromJson? root
  | _       => throw s!"expected single-element top array, got {arr.size} elements"

end LogicalPlan

/-! ## File-level helper -/

def loadPlan (path : System.FilePath) : IO LogicalPlan := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"json parse: {e}"
  | .ok j =>
    match LogicalPlan.fromTopJson? j with
    | .error e => throw <| IO.userError s!"plan decode: {e}"
    | .ok p    => return p

end Provenance.Plan
