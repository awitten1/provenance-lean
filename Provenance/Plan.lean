/-
  DuckDB logical plan ingestion.

  Parses two JSON shapes captured by `bench/capture.sh`:

  * A *schema* JSON, an array of `{table_name, column_name, ordinal_position,
    data_type}` rows from `information_schema.columns`.

  * A *plan* JSON, a single-element array wrapping a recursive
    `{name, children, extra_info}` tree.

  No semantics yet — translation to `Provenance.Query` happens elsewhere.
-/

import Lean.Data.Json
import Lean.Data.Json.Parser

namespace Provenance.Plan

open Lean (Json)

/-! ## Schema -/

structure Column where
  name : String
  ordinal : Nat
  dataType : String
  deriving Repr, Inhabited

structure TableSchema where
  name : String
  columns : Array Column
  deriving Repr, Inhabited

abbrev Schema := Array TableSchema

namespace Schema

def tableNamed? (s : Schema) (table : String) : Option TableSchema :=
  Array.find? (·.name == table) s

/-- Resolve `(table, column)` to the column's 0-based index. -/
def colIdx? (s : Schema) (table col : String) : Option Nat := do
  let t ← s.tableNamed? table
  t.columns.findIdx? (·.name == col)

private def columnFromJson (j : Json) : Except String (String × Column) := do
  let table ← j.getObjValAs? String "table_name"
  let name  ← j.getObjValAs? String "column_name"
  let ord   ← j.getObjValAs? Nat    "ordinal_position"
  let ty    ← j.getObjValAs? String "data_type"
  return (table, { name, ordinal := ord, dataType := ty })

/-- Build a `Schema` from the JSON dumped by `bench/capture.sh`. Rows are
already ordered by `(table_name, ordinal_position)` thanks to the SQL
`ORDER BY` in the dump, so a single pass preserves the right column order. -/
def fromJson? (j : Json) : Except String Schema := do
  let rows ← j.getArr?
  let mut tables : Array TableSchema := #[]
  for row in rows do
    let (table, col) ← columnFromJson row
    match tables.findIdx? (·.name == table) with
    | some i =>
      let t := tables[i]!
      tables := tables.set! i { t with columns := t.columns.push col }
    | none =>
      tables := tables.push { name := table, columns := #[col] }
  return tables

end Schema

/-! ## Expressions

The textual expressions DuckDB emits in `Expressions`/`Filters`/`Conditions`
are tiny: comparisons between a column reference and a literal (or another
column), optionally wrapped in parens, with no-op `CAST(<lit> AS <type>)`
wrappers around literals. AND-conjunction is *structural* — DuckDB pre-splits
conjuncts into JSON arrays — so we never see `AND` inside a single string.

We also reuse this parser for projection expressions, which in our current
corpus are bare column names (e.g. `"a"`, `"c"`).
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

/-- Free column names appearing in an expression. -/
def cols : Expr → List String
  | .col n => [n]
  | .int _ => []
  | .cmp _ l r => l.cols ++ r.cols

/-! ### Pragmatic string parser

Handles exactly the shapes seen in our captured corpus:
  * `(a > CAST(5 AS INTEGER))`, `a>5`, `(a = c)`, `a`, `5`

Limitations: no AND/OR/NOT (structural), no arithmetic, no string literals,
no nested CASTs.  Extend as new cases appear.
-/

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

/-- Replace every `CAST(<atom> AS <type>)` with `<atom>`, preserving anything
outside the cast wrapper. The matching close-paren is found by depth-counting,
so this handles nested parens *inside* the cast (we don't see those today, but
we get them for free). -/
private partial def stripCasts (s : String) : String := Id.run do
  let chars := s.toList
  let n := chars.length
  let mut result : String := ""
  let mut i := 0
  while i < n do
    let prefixOk := i + 5 ≤ n ∧ String.ofList (chars.drop i |>.take 5) == "CAST("
    if prefixOk then
      -- Find matching ')'.
      let mut depth := 1
      let mut j := i + 5
      let mut endPos := n  -- past-the-end if unmatched
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
  -- Try multi-char operators first so e.g. ">=" isn't read as ">".
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
  | seqScan        (table : String)
  | filter         (preds : List Expr) (child : LogicalPlan)
  | projection     (exprs : List Expr) (child : LogicalPlan)
  | crossProduct   (l r : LogicalPlan)
  | comparisonJoin (joinType : String) (conds : List Expr) (l r : LogicalPlan)
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
  | "CROSS_PRODUCT" =>
    let [l, r] := kids | throw s!"CROSS_PRODUCT expected 2 children, got {kids.length}"
    return LogicalPlan.crossProduct l r
  | "COMPARISON_JOIN" =>
    let [l, r] := kids | throw s!"COMPARISON_JOIN expected 2 children, got {kids.length}"
    let jt    ← extra.getObjValAs? String "Join Type"
    let conds ← parseExprField? extra "Conditions"
    return LogicalPlan.comparisonJoin jt conds l r
  | other => throw s!"unsupported plan node: {other}"

/-- Parse the top-level array DuckDB emits: a 1-element array wrapping the
plan root. -/
def fromTopJson? (j : Json) : Except String LogicalPlan := do
  let arr ← j.getArr?
  match arr with
  | #[root] => fromJson? root
  | _       => throw s!"expected single-element top array, got {arr.size} elements"

end LogicalPlan

/-! ## Syntactic equivalence under filter pushdown

A normal form: every filter is pushed maximally down towards its scan, with
AND-conjuncts split at every branching node by which side's columns each
predicate references. Two plans are `equiv?` iff their normal forms are
syntactically equal.

This is sound but incomplete. It catches plain filter-pushdown (queries
01–03 of the corpus). It will *not* validate plans involving equality
propagation (query 04 — see `VALIDATION.md`), since that derives new
predicates not present in `before`. -/

namespace LogicalPlan

/-- Output column names of a plan, in order. Assumes projection expressions
are bare column references (true for our corpus). -/
partial def outputCols (s : Schema) : LogicalPlan → List String
  | .seqScan t =>
    match s.tableNamed? t with
    | some ts => ts.columns.toList.map (·.name)
    | none    => []
  | .filter _ c               => outputCols s c
  | .projection es _          => es.flatMap Expr.cols
  | .crossProduct l r         => outputCols s l ++ outputCols s r
  | .comparisonJoin _ _ l r   => outputCols s l ++ outputCols s r

/-- Walk the plan, pushing each pending predicate as far down as possible.
At a branching node, predicates whose free columns lie entirely in one
side's output go down that side; predicates that span both sides stay
above the join as a `filter`. -/
private partial def normalizeAux (s : Schema) (pending : List Expr) :
    LogicalPlan → LogicalPlan
  | .seqScan t =>
    if pending.isEmpty then .seqScan t else .filter pending (.seqScan t)
  | .filter ps c =>
    normalizeAux s (pending ++ ps) c
  | .projection es c =>
    let projOuts := es.flatMap Expr.cols
    let (pushable, stuck) := pending.partition fun p => p.cols.all projOuts.contains
    let p := LogicalPlan.projection es (normalizeAux s pushable c)
    if stuck.isEmpty then p else .filter stuck p
  | .crossProduct l r =>
    let lcols := outputCols s l
    let rcols := outputCols s r
    let (lP, rest)  := pending.partition fun p => p.cols.all lcols.contains
    let (rP, stuck) := rest.partition    fun p => p.cols.all rcols.contains
    let p := LogicalPlan.crossProduct (normalizeAux s lP l) (normalizeAux s rP r)
    if stuck.isEmpty then p else .filter stuck p
  | .comparisonJoin jt cond l r =>
    let lcols := outputCols s l
    let rcols := outputCols s r
    let (lP, rest)  := pending.partition fun p => p.cols.all lcols.contains
    let (rP, stuck) := rest.partition    fun p => p.cols.all rcols.contains
    let p := LogicalPlan.comparisonJoin jt cond (normalizeAux s lP l) (normalizeAux s rP r)
    if stuck.isEmpty then p else .filter stuck p

def normalize (s : Schema) (plan : LogicalPlan) : LogicalPlan :=
  normalizeAux s [] plan

/-- Decide equivalence under filter pushdown by comparing normal forms. -/
def equiv? (s : Schema) (a b : LogicalPlan) : Bool :=
  decide (normalize s a = normalize s b)

end LogicalPlan

/-! ## File-level helpers -/

def loadSchema (path : System.FilePath) : IO Schema := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"json parse: {e}"
  | .ok j =>
    match Schema.fromJson? j with
    | .error e => throw <| IO.userError s!"schema decode: {e}"
    | .ok s    => return s

def loadPlan (path : System.FilePath) : IO LogicalPlan := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"json parse: {e}"
  | .ok j =>
    match LogicalPlan.fromTopJson? j with
    | .error e => throw <| IO.userError s!"plan decode: {e}"
    | .ok p    => return p

end Provenance.Plan
