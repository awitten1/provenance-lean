import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Bind

import Provenance.Query

/-!
# Query equivalence and a sample transformation

Two queries are *equivalent* when they produce the same multiset of tuples on every
database. This matches the semantics a real SQL optimizer must preserve under bag
(multiset) semantics, where duplicates are not eliminated.

## Main definitions

* `Query.Equiv q₁ q₂` — `∀ d, q₁.evaluate d = q₂.evaluate d`

## Proven transformations

* `Query.sel_sel_and` — `σ_φ (σ_ψ q) = σ_(φ ∧ ψ) q`
* `Query.sel_comm` — `σ_φ (σ_ψ q) = σ_ψ (σ_φ q)`
* `Query.sel_prod_pushdown_left` — `σ_(castLE φ) (q₁ × q₂) = (σ_φ q₁) × q₂`
  when `φ` only mentions left-side columns
* `Query.sel_join_pushdown_left` — `σ_(castLE ψ) (q₁ ⋈_φ q₂) = (σ_ψ q₁) ⋈_φ q₂`
  when `ψ` only mentions left-side columns
-/

attribute [local instance] Filter.evalDecidable

variable {T: Type} [ValueType T]

/-- Semantic equivalence of two queries of the same arity under bag semantics. -/
def Query.Equiv (q₁ q₂: Query T n) : Prop :=
  ∀ d: Database T, q₁.evaluate d = q₂.evaluate d

namespace Query

@[refl]
theorem Equiv.refl (q: Query T n) : Query.Equiv q q := fun _ => rfl

@[symm]
theorem Equiv.symm {q₁ q₂: Query T n} (h: Query.Equiv q₁ q₂) : Query.Equiv q₂ q₁ :=
  fun d => (h d).symm

@[trans]
theorem Equiv.trans {q₁ q₂ q₃: Query T n}
    (h₁₂: Query.Equiv q₁ q₂) (h₂₃: Query.Equiv q₂ q₃) : Query.Equiv q₁ q₃ :=
  fun d => (h₁₂ d).trans (h₂₃ d)

/-- A conjunction of selections is a single selection with an `And`. -/
theorem sel_sel_and (φ ψ: Filter T n) (q: Query T n) :
    Query.Equiv (Sel φ (Sel ψ q)) (Sel (Filter.And φ ψ) q) := by
  intro d
  simp only [evaluate, Filter.eval, Multiset.filter_filter]

/-- Two consecutive selections commute. -/
theorem sel_comm (φ ψ: Filter T n) (q: Query T n) :
    Query.Equiv (Sel φ (Sel ψ q)) (Sel ψ (Sel φ q)) := by
  refine Equiv.trans (sel_sel_and φ ψ q) ?_
  refine Equiv.trans ?_ (Equiv.symm (sel_sel_and ψ φ q))
  intro d
  simp only [evaluate]
  apply Multiset.filter_congr
  intro _ _
  simp only [Filter.eval]
  exact And.comm

end Query

/-! ## Lifting terms and filters along an arity inequality

To state pushdown rules we need to lift a `Filter T n₁` to a `Filter T n` when
`n₁ ≤ n`. The lifted filter ignores the trailing `n − n₁` columns. Built up
constructor by constructor on `Term`, `BoolTerm`, then `Filter`. -/

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

/-! ## Filtering a Cartesian product on the left factor only -/

/-- Filtering a multiset product by a predicate that only inspects the left
component pushes the filter onto the left multiset. Not in Mathlib. -/
lemma Multiset.filter_product_left {α β : Type*}
    (s : Multiset α) (t : Multiset β)
    (p : α → Prop) [DecidablePred p] :
    (Multiset.product s t).filter (fun ab => p ab.1)
      = Multiset.product (s.filter p) t := by
  -- Bridge to the `×ˢ` notation that Mathlib's lemmas are stated against.
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

/-! ## Selection pushdown through Cartesian product -/

namespace Query

/-- Evaluating a lifted filter at an `n₁ + n₂` appended tuple only sees the
left half. -/
private lemma Filter.castLE_eval_append
    {n₁ n₂: ℕ} (φ: Filter T n₁) (a: Tuple T n₁) (b: Tuple T n₂) :
    (φ.castLE (Nat.le_add_right n₁ n₂)).eval (Fin.append a b) = φ.eval a := by
  rw [Filter.castLE_eval]
  congr 1
  funext i
  show Fin.append a b (Fin.castAdd n₂ i) = a i
  exact Fin.append_left _ _ _

/-- A left-only filter `φ` can be pushed through a Cartesian product onto the
left operand. -/
theorem sel_prod_pushdown_left
    {n₁ n₂ n: ℕ} (hn: n₁ + n₂ = n)
    (φ: Filter T n₁) (q₁: Query T n₁) (q₂: Query T n₂) :
    Query.Equiv
      (Sel (φ.castLE (hn ▸ Nat.le_add_right n₁ n₂))
           (@Query.Prod T n₁ n₂ n hn q₁ q₂))
      (@Query.Prod T n₁ n₂ n hn (Sel φ q₁) q₂) := by
  intro d
  subst hn
  simp only [evaluate, Relation.cast, HMul.hMul]
  rw [← Multiset.filter_product_left _ _ φ.eval, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro ab _
  exact (Filter.castLE_eval_append φ ab.1 ab.2).to_iff

/-! ## Join pushdown corollary

A join `q₁ ⋈[φ] q₂` desugars to `σ_φ (q₁ × q₂)` (see `Query.lean`). When a
post-join filter `ψ` only mentions left columns, we can push it onto `q₁`. -/

theorem sel_join_pushdown_left
    {n₁ n₂ n: ℕ} (hn: n₁ + n₂ = n)
    (ψ: Filter T n₁) (φ: Filter T n)
    (q₁: Query T n₁) (q₂: Query T n₂) :
    Query.Equiv
      (Sel (ψ.castLE (hn ▸ Nat.le_add_right n₁ n₂))
           (Sel φ (@Query.Prod T n₁ n₂ n hn q₁ q₂)))
      (Sel φ (@Query.Prod T n₁ n₂ n hn (Sel ψ q₁) q₂)) := by
  -- Two-step proof:
  --   σ_(castLE ψ) (σ_φ (q₁ × q₂))  =  σ_φ (σ_(castLE ψ) (q₁ × q₂))      (sel_comm)
  --                                 =  σ_φ ((σ_ψ q₁) × q₂)               (sel_prod_pushdown_left, under σ_φ)
  refine Equiv.trans (sel_comm _ _ _) ?_
  intro d
  -- Both sides are `Sel φ X` for different inner queries.
  -- Unfold the outer `Sel`, then push congrArg through.
  unfold Query.evaluate
  exact congrArg _ (sel_prod_pushdown_left hn ψ q₁ q₂ d)

end Query
