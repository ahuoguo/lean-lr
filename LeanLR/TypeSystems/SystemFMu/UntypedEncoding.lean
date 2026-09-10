import LeanLR.TypeSystems.SystemFMu.Lang
import LeanLR.TypeSystems.SystemFMu.Notation
import LeanLR.TypeSystems.SystemFMu.Types
import LeanLR.TypeSystems.SystemFMu.Pure

/-!
# Encoding the untyped λ-calculus

`systemf_mu/untyped_encoding.v`. The recursive type `D = μ. (#0 → #0)` is a type of untyped
λ-terms: `roll` and `unroll` mediate between `D` and `D → D`, so every untyped term can be typed
at `D` — including the diverging `Ω`, which is why System F + μ is no longer strongly normalising.
-/

open Iris.Std

namespace SystemFMu

/-- The type of untyped λ-terms. -/
def D : Ty := .mu (.fn (.tVar 0) (.tVar 0))

/-- Unrolling `D` once gives `D → D`. -/
theorem D_unfold : Ty.subst1 (Ty.fn (.tVar 0) (.tVar 0)) D = Ty.fn D D := rfl

theorem D_wf (n : Nat) : TypeWf n D :=
  .mu_wf (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega)))

theorem typed_unroll_D {n : Nat} {Γ : TypingContext} {e : Expr} (h : SynTyped n Γ e D) :
    SynTyped n Γ (.unroll e) (Ty.fn D D) :=
  D_unfold ▸ SynTyped.typed_unroll n Γ e (Ty.fn (.tVar 0) (.tVar 0)) h

theorem typed_roll_D {n : Nat} {Γ : TypingContext} {e : Expr} (h : SynTyped n Γ e (Ty.fn D D)) :
    SynTyped n Γ (.roll e) D :=
  SynTyped.typed_roll n Γ e (Ty.fn (.tVar 0) (.tVar 0)) (D_unfold ▸ h)

/-- An untyped λ-abstraction, as a value of type `D`. -/
def lame (x : String) (e : Expr) : Val := .rollV (.lamV (.bNamed x) e)

/-- Untyped application: unroll the function before applying it. -/
def appe (e₁ e₂ : Expr) : Expr := .app (.unroll e₁) e₂

theorem lame_typed (n : Nat) (Γ : TypingContext) (x : String) (e : Expr)
    (h : SynTyped n (insert (M := TyMapStr) Γ x D) e D) :
    SynTyped n Γ (lame x e).toExpr D :=
  typed_roll_D (.typed_lam n Γ x e D D (D_wf n) h)

theorem app_typed (n : Nat) (Γ : TypingContext) (e₁ e₂ : Expr)
    (h₁ : SynTyped n Γ e₁ D) (h₂ : SynTyped n Γ e₂ D) :
    SynTyped n Γ (appe e₁ e₂) D :=
  .typed_app n Γ _ _ D D (typed_unroll_D h₁) h₂

theorem appe_step_l {e₁ e₁' : Expr} (v : Val) (h : ContextualStep e₁ e₁') :
    ContextualStep (appe e₁ v.toExpr) (appe e₁' v.toExpr) :=
  fill_contextual_step (K := [.unrollCtx, .appLCtx v]) h

theorem appe_step_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (appe e₁ e₂) (appe e₁ e₂') :=
  fill_contextual_step (K := [.appRCtx (.unroll e₁)]) h

theorem lame_step_beta (x : String) (e : Expr) (v : Val) :
    ContextualSteps (appe (lame x e).toExpr v.toExpr) (subst x v.toExpr e) := by
  refine .step (fill_contextual_step (K := [.appLCtx v])
    (base_contextual_step (.unrollS _ trivial))) ?_
  refine .step (base_contextual_step (.betaS _ _ _ (val_isVal v))) ?_
  exact .refl

/-! ## Divergence -/

/-- `ω` applies its (unrolled) argument to itself. -/
def ω : Expr := .roll (.lam (.bNamed "x") (.app (.unroll (.var "x")) (.var "x")))

/-- `Ω` diverges: it steps to itself in two steps. -/
def Ω : Expr := .app (.unroll ω) ω

theorem Ω_loops : ContextualSteps Ω Ω := by
  refine .step (fill_contextual_step (K := [.appLCtx (.rollV (.lamV (.bNamed "x")
    (.app (.unroll (.var "x")) (.var "x"))))])
    (base_contextual_step (.unrollS _ trivial))) ?_
  refine .step (base_contextual_step (.betaS _ _ _ trivial)) ?_
  exact .refl

theorem ω_typed : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) ω D :=
  lame_typed 0 _ "x" _
    (.typed_app 0 _ _ _ D D
      (typed_unroll_D
        (.typed_var 0 _ "x" D (LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl)))
      (.typed_var 0 _ "x" D (LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl)))

theorem Ω_typed : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) Ω D :=
  .typed_app 0 _ _ _ D D (typed_unroll_D ω_typed) ω_typed

end SystemFMu
