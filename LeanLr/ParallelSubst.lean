import LeanLr.Lang
import LeanLr.Operational

namespace STLC

-- TODO: maybe switch to ExtTreeMap?
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/stdpp/near/563551375
-- Finite map substitution (like gmap in Coq)
abbrev Subst := List (String × Expr)

def Subst.empty : Subst := []

def Subst.delete (x : String) (σ : Subst) : Subst :=
  σ.filter (fun p => p.1 ≠ x)

def Subst.insert (x : String) (e : Expr) (σ : Subst) : Subst :=
  (x, e) :: σ.delete x

def Subst.lookup (σ : Subst) (x : String) : Option Expr :=
  List.lookup x σ

def Subst.dom (σ : Subst) : List String :=
  σ.map (·.1)

def Subst.closed (X: List String) (σ: Subst) :=
  ∀ x e, σ.lookup x = some e → e.closed X

def Subst.isSubSubstOf (σ: Subst) (σ': Subst) :=
  ∀ x, x ∈ σ → x ∈ σ'

-- TODO:
notation :70 A "⊆" B => Subst.isSubSubstOf A B

-- Apply finite map substitution to expression
-- TODO: maybe we can define a substmap as `Expr.substMap`?
def substMap (σ : Subst) : Expr → Expr
  | Expr.var x => match List.lookup x σ with
    | some e => e
    | none => Expr.var x
  | Expr.lam (Binder.named x) e =>
      Expr.lam (Binder.named x) (substMap (σ.delete x) e)
  | Expr.lam Binder.anon e => Expr.lam Binder.anon (substMap σ e)
  | Expr.app e₁ e₂ => Expr.app (substMap σ e₁) (substMap σ e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ => Expr.plus (substMap σ e₁) (substMap σ e₂)

-- Helper: weakening for closed expressions
theorem closed_weaken {X Y : List String} {e : Expr} :
    e.closed X → (∀ x, x ∈ X → x ∈ Y) → e.closed Y := by
  intro hclosed hsub
  induction e generalizing X Y with
  | var x =>
    simp [Expr.closed] at hclosed ⊢
    exact hsub x hclosed
  | lam b e ih =>
    simp [Expr.closed] at hclosed ⊢
    apply ih hclosed
    intro z hz
    cases b with
    | anon => exact hsub z hz
    | named y =>
      simp [Binder.cons] at hz ⊢
      cases hz with
      | inl heq => left; exact heq
      | inr hmem => right; exact hsub z hmem
  | app e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hsub
    · exact ih₂ hclosed.2 hsub
  | litInt n =>
    simp [Expr.closed]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hsub
    · exact ih₂ hclosed.2 hsub

-- Helper: applying empty substitution is identity
theorem substMap_empty (e : Expr) : substMap Subst.empty e = e := by
  induction e with
  | var x => rfl
  | lam b e ih =>
    cases b with
    | anon => simp [substMap, ih]
    | named x =>
      simp [substMap, Subst.delete, Subst.empty]
      exact ih
  | app e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | litInt n => rfl
  | plus e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]

-- Helper lemma for lookup in delete
theorem lookup_delete_ne {σ : Subst} {x y : String} :
    x ≠ y → (σ.delete y).lookup x = σ.lookup x := by
  intro hne
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    unfold Subst.delete Subst.lookup
    simp only [List.lookup]
    by_cases hp : p.1 = y
    · -- p.1 = y, so p is filtered out
      rw [List.filter_cons_of_neg]
      · cases hbeq : (x == p.1)
        · exact ih
        · -- x = p.1, but p.1 = y and x ≠ y, contradiction
          have : x = p.1 := eq_of_beq hbeq
          subst this
          contradiction
      · simp [hp]
    · -- p.1 ≠ y, so p is kept
      rw [List.filter_cons_of_pos]
      · simp only [List.lookup]
        cases hbeq : (x == p.1)
        · exact ih
        · rfl
      · simp [hp]

theorem lookup_delete_eq {σ : Subst} {x : String} :
    (σ.delete x).lookup x = none := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    sorry

theorem lookup_insert_eq {σ : Subst} {x : String} {e : Expr} :
    (σ.insert x e).lookup x = some e := by
  sorry

theorem lookup_insert_ne {σ : Subst} {x y : String} {e : Expr} (h : x ≠ y) :
    (σ.insert y e).lookup x = σ.lookup x := by
  unfold Subst.insert Subst.lookup
  simp only [List.lookup]
  cases hbeq : (x == y)
  · exact lookup_delete_ne h
  · have : x = y := eq_of_beq hbeq
    contradiction

-- TODO: Complete this proof
-- Corresponds to Coq's subst_closed_nil
-- Issue: Lean's `subst` definition differs from Coq's in how it handles binders
-- Strategy: May need to restructure the proof or adjust the definition
-- See parallel_subst.v (this lemma is used but not shown in the file)
theorem subst_closed_nil {x : String} {es : Expr} {e : Expr} :
    e.closed [] = true → subst x es e = e := by
  sorry

-- TODO: Complete this proof
-- Corresponds to Coq's subst_map_closed'_2
-- Strategy: Induction on e, for variables show either lookup succeeds (giving closed expr)
--           or lookup fails (so x must be in X). For lambdas, use IH with extended context.
-- See parallel_subst.v lines 178-189
theorem substMapClosed {X : List String} {σ : Subst} {e : Expr} :
    e.closed (X ++ σ.dom) →
    σ.closed X →
    (substMap σ e).closed X := by
  sorry

-- TODO: Complete this proof
-- Corresponds to Coq's subst_subst_map
-- Key lemma showing interaction between normal substitution and parallel substitution
-- Strategy: Induction on e. For vars, use delete/insert properties and subst_closed_nil.
--           For lambdas, need to show delete/insert commute appropriately.
-- Requires: subst_closed_nil to be completed first
-- See parallel_subst.v lines 90-111
theorem subst_substMap_compose {x : String} {es : Expr} {θ : Subst} {e : Expr} :
    θ.closed [] →
    subst x es (substMap (θ.delete x) e) = substMap (Subst.insert x es θ) e := by
  sorry

-- TODO: Complete this proof
-- Corresponds to Coq's subst_closed_weaken
-- Weakening lemma for closed substitutions
-- Strategy: Use closed_weaken and properties of isSubSubstOf
-- See parallel_subst.v lines 82-87
theorem substClosedWeaken {X Y: List String} {σ1 σ2 : Subst} :
    (∀ x, x ∈ Y → x ∈ X) →
    (σ1.isSubSubstOf σ2) →
    σ2.closed Y →
    σ1.closed X := by
  sorry

end STLC
