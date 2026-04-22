import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter

import Provenance.Query

/-!
# Query equivalence and relational-algebra transformations

This file defines semantic equivalence of relational-algebra queries over plain
(unannotated) databases and proves a small library of textbook query-optimizer
transformations with respect to *bag* (multiset) semantics.

Equivalence is parameterised by `Query.evaluate`, so two queries are equivalent
when they produce the same multiset of tuples on every database. This matches
the semantics a real SQL optimizer must preserve when duplicates are not
eliminated.

## Main definitions

* `Query.Equiv q₁ q₂` — `∀ d, q₁.evaluate d = q₂.evaluate d`

## Proven transformations

* `Query.sel_true` — `σ_True q ≡ q`
* `Query.sel_sel_and` — `σ_φ (σ_ψ q) ≡ σ_(φ ∧ ψ) q`
* `Query.sel_comm` — `σ_φ (σ_ψ q) ≡ σ_ψ (σ_φ q)`

## Next steps (not yet proven)

* Congruence: `q₁ ≡ q₂ → Sel φ q₁ ≡ Sel φ q₂`, and similar for each constructor
* Selection pushdown through `Prod` when the predicate only references one side
* Projection pushdown
* Union commutativity / associativity under bag semantics
* Join associativity
-/

variable {T: Type} [ValueType T]

/-- Semantic equivalence of two queries of the same arity under bag semantics. -/
def Query.Equiv (q₁ q₂: Query T n) : Prop :=
  ∀ d: Database T, q₁.evaluate d = q₂.evaluate d

infix:25 " ≋ " => Query.Equiv

namespace Query

@[refl]
theorem Equiv.refl (q: Query T n) : q ≋ q := fun _ => rfl

@[symm]
theorem Equiv.symm {q₁ q₂: Query T n} (h: q₁ ≋ q₂) : q₂ ≋ q₁ :=
  fun d => (h d).symm

@[trans]
theorem Equiv.trans {q₁ q₂ q₃: Query T n}
    (h₁₂: q₁ ≋ q₂) (h₂₃: q₂ ≋ q₃) : q₁ ≋ q₃ :=
  fun d => (h₁₂ d).trans (h₂₃ d)

instance : Trans (@Query.Equiv T _ n) (@Query.Equiv T _ n) (@Query.Equiv T _ n) where
  trans := Equiv.trans

/-! ### Transformations on `Sel` -/

/-- Selecting with `True` is a no-op. -/
theorem sel_true (q: Query T n) : Sel Filter.True q ≋ q := by
  intro d
  simp [evaluate, Filter.eval]

/-- A conjunction of selections is a single selection with an `And`. -/
theorem sel_sel_and (φ ψ: Filter T n) (q: Query T n) :
    Sel φ (Sel ψ q) ≋ Sel (Filter.And φ ψ) q := by
  intro d
  simp only [evaluate, Filter.eval, Multiset.filter_filter]
  congr!

/-- Adjacent selections commute. -/
theorem sel_comm (φ ψ: Filter T n) (q: Query T n) :
    Sel φ (Sel ψ q) ≋ Sel ψ (Sel φ q) := by
  intro d
  simp only [evaluate, Multiset.filter_filter]
  congr 1
  funext t
  exact propext And.comm

end Query
