import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Bind

import Provenance.Query

/-!
# Algebraic query equivalence

This file defines query equivalence by the relation algebra denoted by each
query expression. There is no database lookup: base relations are embedded
directly in `Query.Rel`.

## Main definitions

* `Query.Equiv q₁ q₂` — equality of the relations denoted by two same-arity
  query expressions

## Proven transformations

* `Query.sel_sel_and` — `σ_φ (σ_ψ q) ≋ σ_(φ ∧ ψ) q`
* `Query.sel_comm` — `σ_φ (σ_ψ q) ≋ σ_ψ (σ_φ q)`
* `Query.sel_prod_pushdown_left` — `σ_(castLE φ) (q₁ × q₂) ≋ (σ_φ q₁) × q₂`
  when `φ` only mentions left-side columns
* `Query.sel_join_pushdown_left` — `σ_(castLE ψ) (q₁ ⋈_φ q₂) ≋ (σ_ψ q₁) ⋈_φ q₂`
  when `ψ` only mentions left-side columns
-/

variable {T: Type} [ValueType T]
attribute [local instance] Filter.evalDecidable
set_option linter.unusedSectionVars false

namespace Term

/-- Lift a term to a larger arity along `h : n₁ ≤ n`. -/
def castLE (h: n₁ ≤ n) : Term T n₁ → Term T n
  | const c     => const c
  | index k     => index (k.castLE h)
  | add t₁ t₂   => add (t₁.castLE h) (t₂.castLE h)
  | sub t₁ t₂   => sub (t₁.castLE h) (t₂.castLE h)
  | mul t₁ t₂   => mul (t₁.castLE h) (t₂.castLE h)

/-- Evaluating a lifted term at a wide tuple agrees with evaluating the original
at the prefix of that tuple. -/
theorem castLE_eval (h: n₁ ≤ n) (t: Term T n₁) (u: Tuple T n) :
    (t.castLE h).eval u = t.eval (fun i => u (i.castLE h)) := by
  induction t with
  | const c => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ =>
    unfold castLE eval
    rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold castLE eval
    rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold castLE eval
    rw [ih₁, ih₂]

end Term

namespace BoolTerm

/-- Lift a boolean term to a larger arity along `h : n₁ ≤ n`. -/
def castLE (h: n₁ ≤ n) : BoolTerm T n₁ → BoolTerm T n
  | EQ a b => EQ (a.castLE h) (b.castLE h)
  | NE a b => NE (a.castLE h) (b.castLE h)
  | LE a b => LE (a.castLE h) (b.castLE h)
  | LT a b => LT (a.castLE h) (b.castLE h)
  | GE a b => GE (a.castLE h) (b.castLE h)
  | GT a b => GT (a.castLE h) (b.castLE h)

theorem castLE_eval (h: n₁ ≤ n) (φ: BoolTerm T n₁) (u: Tuple T n) :
    (φ.castLE h).eval u = φ.eval (fun i => u (i.castLE h)) := by
  cases φ <;> simp only [castLE, eval, Term.castLE_eval]

end BoolTerm

namespace Filter

/-- Lift a filter to a larger arity along `h : n₁ ≤ n`. -/
def castLE (h: n₁ ≤ n) : Filter T n₁ → Filter T n
  | BT bt      => BT (bt.castLE h)
  | Not φ      => Not (φ.castLE h)
  | And φ₁ φ₂  => And (φ₁.castLE h) (φ₂.castLE h)
  | Or  φ₁ φ₂  => Or  (φ₁.castLE h) (φ₂.castLE h)
  | True       => True

theorem castLE_eval (h: n₁ ≤ n) (φ: Filter T n₁) (u: Tuple T n) :
    (φ.castLE h).eval u = φ.eval (fun i => u (i.castLE h)) := by
  induction φ with
  | BT bt =>
    unfold castLE eval
    rw [BoolTerm.castLE_eval]
  | Not φ ih =>
    unfold castLE eval
    rw [ih]
  | And φ₁ φ₂ ih₁ ih₂ =>
    unfold castLE eval
    rw [ih₁, ih₂]
  | Or φ₁ φ₂ ih₁ ih₂ =>
    unfold castLE eval
    rw [ih₁, ih₂]
  | True => rfl

end Filter

namespace Query

def Equiv (q₁ q₂: Query T n) : Prop :=
  q₁.toRelation = q₂.toRelation

theorem Equiv.refl (q: Query T n) : Equiv q q := by
  rfl

theorem Equiv.symm' {q₁ q₂: Query T n} (h: Equiv q₁ q₂) : Equiv q₂ q₁ :=
  h.symm

theorem Equiv.trans' {q₁ q₂ q₃: Query T n}
    (h₁₂: Equiv q₁ q₂) (h₂₃: Equiv q₂ q₃) : Equiv q₁ q₃ :=
  h₁₂.trans h₂₃

theorem Equiv.sel {q₁ q₂: Query T n} (φ: Filter T n) :
    Equiv q₁ q₂ → Equiv (Sel φ q₁) (Sel φ q₂) := by
  intro h
  unfold Equiv Query.toRelation
  rw [h]

theorem Equiv.prod {n₁ n₂ n: ℕ} {hn: n₁ + n₂ = n}
    {q₁ q₁': Query T n₁} {q₂ q₂': Query T n₂} :
    Equiv q₁ q₁' → Equiv q₂ q₂' →
      Equiv (@Query.Prod T n₁ n₂ n hn q₁ q₂)
            (@Query.Prod T n₁ n₂ n hn q₁' q₂') := by
  intro h₁ h₂
  unfold Equiv Query.toRelation
  rw [h₁, h₂]

theorem sel_sel_and (φ ψ: Filter T n) (q: Query T n) :
    Equiv (Sel φ (Sel ψ q)) (Sel (Filter.And φ ψ) q) := by
  unfold Equiv Query.toRelation
  simp [Query.toRelation, Filter.eval, Multiset.filter_filter]

theorem sel_comm (φ ψ: Filter T n) (q: Query T n) :
    Equiv (Sel φ (Sel ψ q)) (Sel ψ (Sel φ q)) := by
  refine Equiv.trans' (sel_sel_and φ ψ q) ?_
  refine Equiv.trans' ?_ (Equiv.symm' (sel_sel_and ψ φ q))
  unfold Equiv Query.toRelation
  apply Multiset.filter_congr
  intro _ _
  simp only [Filter.eval]
  exact And.comm

lemma Multiset.filter_product_left {α β : Type*}
    (s : Multiset α) (t : Multiset β)
    (p : α → Prop) [DecidablePred p] :
    (Multiset.product s t).filter (fun ab => p ab.1)
      = Multiset.product (s.filter p) t := by
  show (s ×ˢ t).filter (fun ab => p ab.1) = (s.filter p) ×ˢ t
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.filter_add, ih]
    by_cases hp : p a
    · have hall : ∀ x ∈ t.map (Prod.mk a), p x.1 := by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩
        exact hp
      rw [Multiset.filter_eq_self.mpr hall,
          Multiset.filter_cons_of_pos _ hp, Multiset.cons_product]
    · have hnone : ∀ x ∈ t.map (Prod.mk a), ¬ p x.1 := by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩
        exact hp
      rw [Multiset.filter_eq_nil.mpr hnone, Multiset.zero_add,
          Multiset.filter_cons_of_neg _ hp]

private lemma Filter.castLE_eval_append
    {n₁ n₂: ℕ} (φ: Filter T n₁) (a: Tuple T n₁) (b: Tuple T n₂) :
    (φ.castLE (Nat.le_add_right n₁ n₂)).eval (Fin.append a b) = φ.eval a := by
  rw [Filter.castLE_eval]
  congr 1
  funext i
  show Fin.append a b (Fin.castAdd n₂ i) = a i
  exact Fin.append_left _ _ _

theorem sel_prod_pushdown_left
    {n₁ n₂ n: ℕ} (hn: n₁ + n₂ = n)
    (φ: Filter T n₁) (q₁: Query T n₁) (q₂: Query T n₂) :
    Equiv
      (Sel (φ.castLE (hn ▸ Nat.le_add_right n₁ n₂))
           (@Query.Prod T n₁ n₂ n hn q₁ q₂))
      (@Query.Prod T n₁ n₂ n hn (Sel φ q₁) q₂) := by
  unfold Equiv
  subst hn
  simp only [Query.toRelation, Relation.cast, HMul.hMul]
  rw [← Multiset.filter_product_left _ _ φ.eval, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro ab _
  exact (Filter.castLE_eval_append φ ab.1 ab.2).to_iff

/-!
The left-only assumption is carried by the type `φ : Filter T n₁`.
If `φ` were allowed to mention all product attributes, its type would be
`Filter T n`, and the pushed-down query below would not even typecheck:

```lean
example
    {n₁ n₂ n: ℕ} (hn: n₁ + n₂ = n)
    (φ: Filter T n) (q₁: Query T n₁) (q₂: Query T n₂) :
    Equiv
      (Sel φ (@Query.Prod T n₁ n₂ n hn q₁ q₂))
      (@Query.Prod T n₁ n₂ n hn (Sel φ q₁) q₂) := by
  -- Type error:
  --   φ has type `Filter T n`
  --   q₁ has type `Query T n₁`
  -- but `Sel φ q₁` requires a filter of type `Filter T n₁`.
  sorry
```

That is exactly the unsafe case: a `Filter T n` may inspect right-side
attributes, so it cannot be applied before the product to `q₁` alone.
-/

/-! ## Join pushdown corollary

A join `q₁ ⋈[φ] q₂` desugars to `σ_φ (q₁ × q₂)` (see `Query.lean`). When a
post-join filter `ψ` only mentions left columns, we can push it onto `q₁`. -/

theorem sel_join_pushdown_left
    {n₁ n₂ n: ℕ} (hn: n₁ + n₂ = n)
    (ψ: Filter T n₁) (φ: Filter T n)
    (q₁: Query T n₁) (q₂: Query T n₂) :
    Equiv
      (Sel (ψ.castLE (hn ▸ Nat.le_add_right n₁ n₂))
           (Sel φ (@Query.Prod T n₁ n₂ n hn q₁ q₂)))
      (Sel φ (@Query.Prod T n₁ n₂ n hn (Sel ψ q₁) q₂)) := by
  refine Equiv.trans' (sel_comm _ _ _) ?_
  exact Equiv.sel φ (sel_prod_pushdown_left hn ψ q₁ q₂)

end Query
