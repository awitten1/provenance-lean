import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fin.Tuple.Basic

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

/-- Substitute each index in a term by another term. -/
def Term.substitute (t: Term T m) (s: Tuple (Term T n) m) : Term T n := match t with
| .const a => .const a
| .index k => s k
| .add t₁ t₂ => .add (t₁.substitute s) (t₂.substitute s)
| .sub t₁ t₂ => .sub (t₁.substitute s) (t₂.substitute s)
| .mul t₁ t₂ => .mul (t₁.substitute s) (t₂.substitute s)

theorem Term.substitute_eval (t: Term T m) (s: Tuple (Term T n) m) (tuple: Tuple T n) :
    (t.substitute s).eval tuple = t.eval (fun k => (s k).eval tuple) := by
  induction t with
  | const a => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => simp [substitute, eval, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => simp [substitute, eval, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => simp [substitute, eval, ih₁, ih₂]

/-! ### Lifting a term/filter from arity `n₁` to arity `n` when `n₁ ≤ n` -/

def Term.castLE (h: n₁ ≤ n) (t: Term T n₁) : Term T n := match t with
| .const a => .const a
| .index k => .index (k.castLE h)
| .add t₁ t₂ => .add (t₁.castLE h) (t₂.castLE h)
| .sub t₁ t₂ => .sub (t₁.castLE h) (t₂.castLE h)
| .mul t₁ t₂ => .mul (t₁.castLE h) (t₂.castLE h)

theorem Term.castLE_eval (t: Term T n₁) (h: n₁ ≤ n) (tuple: Tuple T n) :
    (t.castLE h).eval tuple = t.eval (fun k => tuple (k.castLE h)) := by
  induction t with
  | const a => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => simp [castLE, eval, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => simp [castLE, eval, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => simp [castLE, eval, ih₁, ih₂]

def BoolTerm.castLE (h: n₁ ≤ n) (b: BoolTerm T n₁) : BoolTerm T n := match b with
| .EQ a b => .EQ (a.castLE h) (b.castLE h)
| .NE a b => .NE (a.castLE h) (b.castLE h)
| .LE a b => .LE (a.castLE h) (b.castLE h)
| .LT a b => .LT (a.castLE h) (b.castLE h)
| .GE a b => .GE (a.castLE h) (b.castLE h)
| .GT a b => .GT (a.castLE h) (b.castLE h)

theorem BoolTerm.castLE_eval (b: BoolTerm T n₁) (h: n₁ ≤ n) (tuple: Tuple T n) :
    (b.castLE h).eval tuple = b.eval (fun k => tuple (k.castLE h)) := by
  cases b <;> simp [castLE, eval, Term.castLE_eval]

def Filter.castLE (h: n₁ ≤ n) (φ: Filter T n₁) : Filter T n := match φ with
| .BT b => .BT (b.castLE h)
| .Not φ => .Not (φ.castLE h)
| .And φ₁ φ₂ => .And (φ₁.castLE h) (φ₂.castLE h)
| .Or φ₁ φ₂ => .Or (φ₁.castLE h) (φ₂.castLE h)
| .True => .True

theorem Filter.castLE_eval (φ: Filter T n₁) (h: n₁ ≤ n) (tuple: Tuple T n) :
    (φ.castLE h).eval tuple = φ.eval (fun k => tuple (k.castLE h)) := by
  induction φ with
  | BT b => simp [castLE, eval, BoolTerm.castLE_eval]
  | Not φ ih => simp [castLE, eval, ih]
  | And φ₁ φ₂ ih₁ ih₂ => simp [castLE, eval, ih₁, ih₂]
  | Or φ₁ φ₂ ih₁ ih₂ => simp [castLE, eval, ih₁, ih₂]
  | True => rfl

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

/-! ### Congruence lemmas

These let you replace a subquery with an equivalent one anywhere inside a larger query. -/

theorem Equiv.sel (φ: Filter T n) {q₁ q₂: Query T n} (h: q₁ ≋ q₂) :
    Sel φ q₁ ≋ Sel φ q₂ := by
  intro d
  simp only [evaluate, h d]

theorem Equiv.proj {m: ℕ} (ts: Tuple (Term T n) m) {q₁ q₂: Query T n} (h: q₁ ≋ q₂) :
    Proj ts q₁ ≋ Proj ts q₂ := by
  intro d
  simp only [evaluate, h d]

theorem Equiv.prod {n₁ n₂ n: ℕ} {hn: n₁+n₂=n}
    {q₁ q₁': Query T n₁} {q₂ q₂': Query T n₂}
    (h₁: q₁ ≋ q₁') (h₂: q₂ ≋ q₂') :
    (@Prod T n₁ n₂ n hn q₁ q₂) ≋ (@Prod T n₁ n₂ n hn q₁' q₂') := by
  intro d
  simp only [evaluate, h₁ d, h₂ d]

/-! ### Projection composition

Two stacked projections fuse into one by substituting the inner terms into the outer ones. -/

/-- `Π[ts₁] (Π[ts₂] q) ≋ Π[ts₁ ∘ ts₂] q`, where composition is index substitution. -/
theorem proj_proj {m₁ m₂: ℕ}
    (ts₁: Tuple (Term T m₂) m₁) (ts₂: Tuple (Term T n) m₂) (q: Query T n) :
    Proj ts₁ (Proj ts₂ q) ≋ Proj (fun k => (ts₁ k).substitute ts₂) q := by
  intro d
  simp only [evaluate, Multiset.map_map]
  apply congrArg (Multiset.map · _)
  funext t
  funext k
  exact (Term.substitute_eval (ts₁ k) ts₂ t).symm

end Query

/-! ### Helper: filtering on the first coordinate distributes over product -/

theorem Multiset.filter_product_left {α β: Type*}
    (p: α → Prop) [DecidablePred p] (s: Multiset α) (t: Multiset β) :
    (s.product t).filter (fun ab => p ab.1) = (s.filter p).product t := by
  induction s using Multiset.induction with
  | empty =>
    show Multiset.filter _ ((0 : Multiset α) ×ˢ t) = Multiset.product 0 t
    rw [Multiset.zero_product]
    rfl
  | cons a s ih =>
    show Multiset.filter _ ((a ::ₘ s) ×ˢ t) = _
    rw [Multiset.cons_product, Multiset.filter_add]
    show _ + (s.product t).filter (fun ab => p ab.1) = _
    rw [ih, Multiset.filter_map]
    by_cases h : p a
    · rw [Multiset.filter_cons_of_pos _ h]
      show _ = ((a ::ₘ s.filter p) ×ˢ t)
      rw [Multiset.cons_product]
      congr 1
      show Multiset.map (Prod.mk a) (t.filter (fun _ => p a)) = _
      simp [h]
    · rw [Multiset.filter_cons_of_neg _ h]
      show Multiset.map (Prod.mk a) (t.filter (fun _ => p a)) + _ = _
      simp [h]

namespace Query

section SelProdPushdown
attribute [local instance] Filter.evalDecidable

/-- Selection on the left operand of a product can be pushed inside.
`σ_{castLE φ} (q₁ × q₂) ≋ (σ_φ q₁) × q₂`. -/
theorem sel_prod_pushdown_left (φ: Filter T n₁) (q₁: Query T n₁) (q₂: Query T n₂) :
    Sel (φ.castLE (Nat.le_add_right n₁ n₂))
        (@Prod T n₁ n₂ (n₁+n₂) rfl q₁ q₂) ≋
      @Prod T n₁ n₂ (n₁+n₂) rfl (Sel φ q₁) q₂ := by
  intro d
  simp only [evaluate, Relation.cast, HMul.hMul]
  rw [Multiset.filter_map]
  congr 1
  set r₁ : Multiset (Tuple T n₁) := q₁.evaluate d
  set r₂ : Multiset (Tuple T n₂) := q₂.evaluate d
  trans Multiset.filter (fun ab : Tuple T n₁ × Tuple T n₂ => φ.eval ab.1)
          (r₁.product r₂)
  · apply Multiset.filter_congr
    intro ab _
    show (φ.castLE (Nat.le_add_right n₁ n₂)).eval (Fin.append ab.1 ab.2) ↔ φ.eval ab.1
    rw [Filter.castLE_eval]
    refine Iff.of_eq (congrArg _ ?_)
    funext k
    exact Fin.append_left' ab.1 ab.2 k
  · exact Multiset.filter_product_left φ.eval r₁ r₂

end SelProdPushdown

end Query

/-! ### TODO — remaining transformations for full SPJ coverage

* `sel_prod_pushdown_right`: the mirror image for the right operand.
  Needs a `Term.castLE_right` / `Filter.castLE_right` that maps `Fin n₂ → Fin (n₁+n₂)`
  via `Fin.natAdd`, plus the analogous multiset lemma for the right factor.

* `prod_comm`: `q₁ × q₂ ≋ Π[prodSwap] (q₂ × q₁)` where `prodSwap` permutes the
  `n₁+n₂` columns to match `n₂+n₁`. Needs `Multiset.product_swap` (exists in
  Mathlib) and Fin index arithmetic.
-/
