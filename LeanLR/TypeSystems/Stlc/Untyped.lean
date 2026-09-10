import LeanLR.TypeSystems.Stlc.Lang
import LeanLR.TypeSystems.Stlc.Notation
import LeanLR.TypeSystems.Stlc.Operational
import LeanLR.TypeSystems.Stlc.ParallelSubst

/-!
# The untyped λ-calculus

The language of `Stlc.Lang` is not re-defined without primitive addition; this file simply
restricts itself to variables, abstraction and application.

Everything here is about `Steps`, the reflexive-transitive closure of the small-step relation:
the diverging term `Ω`, the Scott encoding of the naturals, a fixed-point combinator, and
addition proved correct against it.

Where the Rocq development states a lemma for `(z s : val)` and relies on the `of_val` coercion,
this file takes `z s : Expr` together with `isValue`/`closed` hypotheses. The two are equivalent
(`val_isValue` supplies the hypothesis at every call site), but the `Expr` form lets `simp` reduce
substitutions into the concrete terms instead of getting stuck under `Val.toExpr`.
-/

namespace STLC.Untyped

open STLC

/-! ## Lifting reductions through application -/

/-- Reduction sequences lift to the argument of an application. -/
theorem steps_app_r (e₁ : Expr) {e₂ e₂' : Expr} (h : e₂ ↠* e₂') :
    Expr.app e₁ e₂ ↠* Expr.app e₁ e₂' := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.stepAppR hs) ih

/-- Reduction sequences lift to the function of an application, once the argument is a value. -/
theorem steps_app_l {e₁ e₁' : Expr} (e₂ : Expr) (hv : e₂.isValue = true) (h : e₁ ↠* e₁') :
    Expr.app e₁ e₂ ↠* Expr.app e₁' e₂ := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.stepAppL hv hs) ih

/-! ## Basic combinators -/

def I_val : Val := λᵥ: x, "x"
def F_val : Val := λᵥ: x y, "x"
def S_val : Val := λᵥ: x y, "y"

/-- `ω` applies its argument to itself. -/
def ω : Val := λᵥ: x, ("x" : Expr) "x"

/-- The diverging term. -/
def Ω : Expr := Expr.app ω.toExpr ω.toExpr

/-- `Ω` reduces to itself, so it diverges. -/
theorem Omega_step : Ω ↠ Ω := Step.stepBeta rfl

/-! ## Scott encoding of the naturals

A Scott numeral is its own `match`: `zero` selects its first argument, `succ n` applies its second
argument to `n`. -/

def zero : Val := λᵥ: x y, "x"

/-- The successor, taken at the meta level. -/
def succ (n : Expr) : Val := λᵥ: x y, ("y" : Expr) n

/-- The successor as a term of the language: a constructor rather than a meta-level function. -/
def Succ : Val := λᵥ: n x y, ("y" : Expr) "n"

/-- The Scott encoding of `n`. -/
def encNat : Nat → Val
  | 0 => zero
  | n + 1 => succ (encNat n).toExpr

/-! ### Unfolding equations

These keep `Val.toExpr` from being unfolded blindly: a `Val` variable such as `encNat n` has no
`Val.toExpr` normal form, so exposing the constructor shape of the *concrete* terms explicitly is
what lets `simp` reduce the substitutions around it. -/

theorem zero_toExpr : zero.toExpr = Expr.lam (.named "x") (Expr.lam (.named "y") (.var "x")) := rfl

theorem succ_toExpr (n : Expr) :
    (succ n).toExpr = Expr.lam (.named "x") (Expr.lam (.named "y") (Expr.app (.var "y") n)) := rfl

theorem Succ_toExpr :
    Succ.toExpr = Expr.lam (.named "n") (Expr.lam (.named "x")
      (Expr.lam (.named "y") (Expr.app (.var "y") (.var "n")))) := rfl

theorem encNat_zero_toExpr : (encNat 0).toExpr = zero.toExpr := rfl

theorem encNat_succ_toExpr (n : Nat) :
    (encNat (n + 1)).toExpr
      = Expr.lam (.named "x") (Expr.lam (.named "y")
          (Expr.app (.var "y") (encNat n).toExpr)) := rfl

theorem encNat_closed (n : Nat) : (encNat n).toExpr.closed [] = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encNat_succ_toExpr]
    simp only [Expr.closed, Binder.cons, Bool.and_eq_true]
    exact ⟨by decide, closed_weaken ih (by simp)⟩

/-- Applying `0` to a continuation pair selects the zero branch. -/
theorem enc_0_red {z s : Expr} (hzv : z.isValue = true) (hsv : s.isValue = true)
    (hz : z.closed [] = true) :
    Expr.app (Expr.app (encNat 0).toExpr z) s ↠* z := by
  rw [encNat_zero_toExpr, zero_toExpr]
  refine .step (.stepAppL hsv (.stepBeta hzv)) ?_
  simp +decide only [if_true, if_false, subst', subst]
  refine .step (.stepBeta hsv) ?_
  rw [show subst' (Binder.named "y") s z = z from subst_closed_nil hz]
  exact .refl

/-- Applying `n + 1` to a continuation pair applies the successor branch to `n`. -/
theorem enc_S_red (n : Nat) {z s : Expr} (hzv : z.isValue = true) (hsv : s.isValue = true) :
    Expr.app (Expr.app (encNat (n + 1)).toExpr z) s ↠* Expr.app s (encNat n).toExpr := by
  rw [encNat_succ_toExpr]
  refine .step (.stepAppL hsv (.stepBeta hzv)) ?_
  simp +decide only [if_false, subst', subst, subst_closed_nil (encNat_closed n)]
  refine .step (.stepBeta hsv) ?_
  simp +decide only [if_true, subst', subst, subst_closed_nil (encNat_closed n)]
  exact .refl

/-- `Succ` implements the successor on encoded naturals. -/
theorem Succ_red (n : Nat) : Expr.app Succ.toExpr (encNat n).toExpr ↠ (encNat (n + 1)).toExpr := by
  rw [Succ_toExpr, encNat_succ_toExpr]
  have h := Step.stepBeta (x := Binder.named "n")
    (e := Expr.lam (.named "x") (Expr.lam (.named "y") (Expr.app (.var "y") (.var "n"))))
    (e' := (encNat n).toExpr) (val_isValue _)
  simpa +decide only [if_true, if_false, subst', subst] using h

/-- Iterating `Succ` on `zero` builds the encoding of `n`. -/
theorem Succ_red_n (n : Nat) :
    (Nat.rec zero.toExpr (fun _ e => Expr.app Succ.toExpr e) n : Expr) ↠* (encNat n).toExpr := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact (steps_app_r Succ.toExpr ih).trans (Steps.single (Succ_red n))

/-! ## Recursion -/

/-- The pre-fixpoint combinator. -/
def Fix' : Val := λᵥ: z y, ("y" : Expr) (λ: x, ((("z" : Expr) "z") "y") "x")

/-- The fixed-point combinator applied to a functional `s`. -/
def Fix (s : Expr) : Val :=
  Val.lamV (.named "x") (Expr.app (Expr.app (Expr.app Fix'.toExpr Fix'.toExpr) s) (.var "x"))

theorem Fix'_toExpr :
    Fix'.toExpr = Expr.lam (.named "z") (Expr.lam (.named "y")
      (Expr.app (.var "y")
        (Expr.lam (.named "x")
          (Expr.app (Expr.app (Expr.app (.var "z") (.var "z")) (.var "y")) (.var "x"))))) := rfl

theorem Fix_toExpr (s : Expr) :
    (Fix s).toExpr
      = Expr.lam (.named "x")
          (Expr.app (Expr.app (Expr.app Fix'.toExpr Fix'.toExpr) s) (.var "x")) := rfl

private theorem Fix'_closed : Fix'.toExpr.closed [] = true := by decide

/-- `Fix s` satisfies the recursive unfolding equation: it hands `s` a copy of itself. -/
theorem Fix_step {s r : Expr} (hsv : s.isValue = true) (hrv : r.isValue = true)
    (hs : s.closed [] = true) :
    Expr.app (Fix s).toExpr r ↠* Expr.app (Expr.app s (Fix s).toExpr) r := by
  rw [Fix_toExpr]
  refine .step (.stepBeta hrv) ?_
  simp +decide only [if_true, subst', subst, subst_closed_nil hs, subst_closed_nil Fix'_closed]
  refine .step (.stepAppL hrv (.stepAppL hsv (.stepBeta (val_isValue Fix')))) ?_
  rw [Fix'_toExpr]
  simp +decide only [if_true, if_false, subst', subst]
  refine .step (.stepAppL hrv (.stepBeta hsv)) ?_
  simp +decide only [if_true, if_false, subst', subst]
  exact .refl

/-! ## Example: addition on Scott numerals -/

/-- The functional whose fixed point is addition. -/
def add_step : Val :=
  λᵥ: r, (λ: n m, ((("n" : Expr) "m") (λ: p, Succ.toExpr ((("r" : Expr) "p") "m"))))

def add : Val := Fix add_step.toExpr

theorem add_step_toExpr :
    add_step.toExpr
      = Expr.lam (.named "r")
          (Expr.lam (.named "n") (Expr.lam (.named "m")
            (Expr.app (Expr.app (.var "n") (.var "m"))
              (Expr.lam (.named "p")
                (Expr.app Succ.toExpr
                  (Expr.app (Expr.app (.var "r") (.var "p")) (.var "m"))))))) := rfl

private theorem add_step_closed : add_step.toExpr.closed [] = true := by decide

private theorem add_closed : add.toExpr.closed [] = true := by decide

private theorem Succ_closed : Succ.toExpr.closed [] = true := by decide

/-- The continuation `add` hands to a Scott numeral as its successor branch. -/
private def addK (m : Expr) : Expr :=
  Expr.lam (.named "p") (Expr.app Succ.toExpr (Expr.app (Expr.app add.toExpr (.var "p")) m))

/-- Unfolding `add` once exposes the `match` on its first argument. -/
private theorem add_unfold {n m : Expr} (hnv : n.isValue = true) (hmv : m.isValue = true)
    (hn : n.closed [] = true) (_hm : m.closed [] = true) :
    Expr.app (Expr.app add.toExpr n) m ↠* Expr.app (Expr.app n m) (addK m) := by
  show Expr.app (Expr.app (Fix add_step.toExpr).toExpr n) m ↠* _
  refine (steps_app_l m hmv
    (Fix_step (val_isValue add_step) hnv add_step_closed)).trans ?_
  refine .step (.stepAppL hmv (.stepAppL hnv (.stepBeta (val_isValue (Fix add_step.toExpr))))) ?_
  rw [add_step_toExpr]
  simp +decide only [if_true, if_false, addK, subst', subst, subst_closed_nil Succ_closed]
  refine .step (.stepAppL hmv (.stepBeta hnv)) ?_
  simp +decide only [if_true, if_false, subst', subst, subst_closed_nil Succ_closed]
  refine .step (.stepBeta hmv) ?_
  simp +decide only [if_true, if_false, subst', subst, subst_closed_nil Succ_closed,
    subst_closed_nil hn]
  exact .refl

theorem add_step_0 (m : Nat) :
    Expr.app (Expr.app add.toExpr (encNat 0).toExpr) (encNat m).toExpr ↠* (encNat m).toExpr := by
  refine (add_unfold (val_isValue _) (val_isValue _)
    (encNat_closed 0) (encNat_closed m)).trans ?_
  exact enc_0_red (val_isValue _) rfl (encNat_closed m)

theorem add_step_S (n m : Nat) :
    Expr.app (Expr.app add.toExpr (encNat (n + 1)).toExpr) (encNat m).toExpr
      ↠* Expr.app Succ.toExpr
        (Expr.app (Expr.app add.toExpr (encNat n).toExpr) (encNat m).toExpr) := by
  refine (add_unfold (val_isValue _) (val_isValue _)
    (encNat_closed (n + 1)) (encNat_closed m)).trans ?_
  refine (enc_S_red n (val_isValue _) rfl).trans ?_
  refine .step (.stepBeta (val_isValue _)) ?_
  simp +decide only [if_true, subst', subst, subst_closed_nil Succ_closed,
    subst_closed_nil add_closed, subst_closed_nil (encNat_closed m)]
  exact .refl

/-- `add` computes addition on Scott-encoded naturals. -/
theorem add_correct (n m : Nat) :
    Expr.app (Expr.app add.toExpr (encNat n).toExpr) (encNat m).toExpr
      ↠* (encNat (n + m)).toExpr := by
  induction n with
  | zero => simpa using add_step_0 m
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 from by omega]
    refine (add_step_S n m).trans ?_
    refine (steps_app_r Succ.toExpr ih).trans ?_
    exact Steps.single (Succ_red (n + m))

end STLC.Untyped
