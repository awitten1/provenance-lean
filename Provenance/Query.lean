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

abbrev Filter (T) (n: ℕ) := Tuple T n → Prop

namespace Filter

def and (φ ψ: Filter T n) : Filter T n :=
  fun tuple => φ tuple ∧ ψ tuple

instance andDecidable (φ ψ: Filter T n) [DecidablePred φ] [DecidablePred ψ] :
    DecidablePred (and φ ψ) :=
  fun tuple => by
    unfold and
    exact inferInstanceAs (Decidable (φ tuple ∧ ψ tuple))

def true : Filter T n :=
  fun _ => True

instance trueDecidable : DecidablePred (@true T n) :=
  fun tuple => by
    unfold true
    exact isTrue trivial

def ofBoolTerm (φ: BoolTerm T n) : Filter T n :=
  fun tuple => φ.eval tuple

instance ofBoolTermDecidable (φ: BoolTerm T n) : DecidablePred (ofBoolTerm φ) :=
  fun tuple => by
    unfold ofBoolTerm
    exact φ.evalDecidable tuple

end Filter

inductive Query (T : Type) : ℕ → Type where
| Rel   : (n : ℕ) → Relation T n → Query T n
| Sel   : (φ : Filter T n) → [DecidablePred φ] → Query T n → Query T n
| Prod {n₁ n₂ n : ℕ} {hn : n₁ + n₂ = n} : Query T n₁ → Query T n₂ → Query T n

def Query.toRelation (q: Query T n): Relation T n := match q with
| Query.Rel _ r => r
| @Query.Sel _ _ φ dec q => @Multiset.filter _ φ dec (Query.toRelation q)
| @Query.Prod _ _ _ _ hn q₁ q₂ => Relation.cast hn (Query.toRelation q₁ * Query.toRelation q₂)
