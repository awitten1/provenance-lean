import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter

import Provenance.Query

/-!
# Query equivalence and a sample transformation

Two queries are *equivalent* when they produce the same multiset of tuples on every
database. This matches the semantics a real SQL optimizer must preserve under bag
(multiset) semantics, where duplicates are not eliminated.

## Main definitions

* `Query.Equiv q₁ q₂` — `∀ d, q₁.evaluate d = q₂.evaluate d`

## Proven transformations

* `Query.sel_sel_and` — `σ_φ (σ_ψ q) ≡ σ_(φ ∧ ψ) q`
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

/-- A conjunction of selections is a single selection with an `And`. -/
theorem sel_sel_and (φ ψ: Filter T n) (q: Query T n) :
    Sel φ (Sel ψ q) ≋ Sel (Filter.And φ ψ) q := by
  intro d
  simp only [evaluate, Filter.eval, Multiset.filter_filter]
  congr!

end Query
