import Mathlib.Data.Multiset.Filter

import Provenance.Database

variable {T: Type} [ValueType T]

inductive Term T n where
| const : T → Term T n
| index : Fin n → Term T n
| add   : Term T n → Term T n → Term T n
| sub   : Term T n → Term T n → Term T n
| mul   : Term T n → Term T n → Term T n

def Term.eval (term: Term T n) (tuple: Tuple T n) := match term with
  | const a    => a
  | index k    => tuple k
  | add t₁ t₂  => (t₁.eval tuple) + (t₂.eval tuple)
  | sub t₁ t₂  => (t₁.eval tuple) - (t₂.eval tuple)
  | mul t₁ t₂  => (t₁.eval tuple) * (t₂.eval tuple)

inductive BoolTerm (T) (n: ℕ) where
| EQ : Term T n → Term T n → BoolTerm T n
| NE : Term T n → Term T n → BoolTerm T n
| LE : Term T n → Term T n → BoolTerm T n
| LT : Term T n → Term T n → BoolTerm T n
| GE : Term T n → Term T n → BoolTerm T n
| GT : Term T n → Term T n → BoolTerm T n

def BoolTerm.eval (φ: BoolTerm T n) (tuple: Tuple T n) := match φ with
| EQ t₁ t₂ => (t₁.eval tuple) = (t₂.eval tuple)
| NE t₁ t₂ => (t₁.eval tuple) ≠ (t₂.eval tuple)
| LE t₁ t₂ => (t₁.eval tuple) ≤ (t₂.eval tuple)
| LT t₁ t₂ => (t₁.eval tuple) < (t₂.eval tuple)
| GE t₁ t₂ => (t₁.eval tuple) ≥ (t₂.eval tuple)
| GT t₁ t₂ => (t₁.eval tuple) > (t₂.eval tuple)

def BoolTerm.evalDecidable (φ: BoolTerm T n) : DecidablePred φ.eval :=
  λ t => by
    cases φ <;> rename_i x y <;> simp [BoolTerm.eval]
    . exact inferInstanceAs (Decidable (x.eval t = y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≠ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≤ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t < y.eval t))
    . exact inferInstanceAs (Decidable (y.eval t ≤ x.eval t))
    . exact inferInstanceAs (Decidable (y.eval t < x.eval t))

inductive Filter (T) (n: ℕ) where
| BT   : BoolTerm T n → Filter T n
| Not  : Filter T n → Filter T n
| And  : Filter T n → Filter T n → Filter T n
| Or   : Filter T n → Filter T n → Filter T n
| True : Filter T n

def Filter.eval (φ: Filter T n) (tuple: Tuple T n) := match φ with
| BT  φ     => φ.eval tuple
| Not φ     => ¬ (φ.eval tuple)
| And φ₁ φ₂ => (φ₁.eval tuple) ∧ (φ₂.eval tuple)
| Or  φ₁ φ₂ => (φ₁.eval tuple) ∨ (φ₂.eval tuple)
| True      => true

def Filter.evalDecidable (φ : Filter T n) : DecidablePred φ.eval :=
  λ t => match φ with
    | Filter.BT φ       => φ.evalDecidable t
    | Filter.Not φ      => match φ.evalDecidable t with
      | isTrue h  => isFalse (by simp [Filter.eval, h])
      | isFalse h => isTrue  (by simp [Filter.eval, h])
    | Filter.And φ₁ φ₂  => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h₁, isTrue h₂   => isTrue  (by simp [Filter.eval, h₁, h₂])
      | isFalse h, _ | _, isFalse h => isFalse (by simp [Filter.eval, h])
    | Filter.Or φ₁ φ₂   => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h, _ | _, isTrue h => isTrue (by simp [Filter.eval, h])
      | isFalse h₁, isFalse h₂    => isFalse (by simp [Filter.eval, h₁, h₂])
    | Filter.True       => isTrue (rfl)

inductive Query (T : Type) : ℕ → Type where
| Rel   : (n : ℕ) → Relation T n → Query T n
| Sel   : Filter T n → Query T n → Query T n
| Prod {n₁ n₂ n : ℕ} {hn : n₁ + n₂ = n} : Query T n₁ → Query T n₂ → Query T n
| Proj {n' n : ℕ} : Tuple (Term T n') n → Query T n' → Query T n

def Query.evaluate (q: Query T n) (d: Database T): Relation T n := match q with
| Query.Rel _ r => r
| Query.Sel φ q  => let r := evaluate q d
                    @Multiset.filter _ φ.eval φ.evalDecidable r
| @Query.Prod _ _ _ _ hn q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ := evaluate q₂ d
  (r₁ * r₂).cast hn
| @Query.Proj _ _ _ ts q =>
  let r := evaluate q d
  Multiset.map (fun t => fun k => (ts k).eval t) r

namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

#check Prod

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat.succ (MyNat.zero)

end Hidden
