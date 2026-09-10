import LeanLR.TypeSystems.StlcExtended.Maps

/-!
# Warmup: arithmetic expressions

The course's exercise sheet 0 (`type_systems/warmup/warmup.v`). Closed and open arithmetic
expressions, closedness, substitution, and evaluation against an environment — a miniature of
everything the later chapters do.

The finite map is `Iris.Std`'s `MapStr` rather than stdpp's `gmap`, as everywhere else in this
port.
-/

open Iris.Std

namespace Warmup

/-! ## Exercise 1: arithmetic -/

inductive Expr where
  | const (z : Int)
  | plus (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

/-- Addition of expressions. -/
infixl:65 " +ₑ " => Expr.plus
/-- Multiplication of expressions. -/
infixl:70 " *ₑ " => Expr.mul

def Expr.eval : Expr → Int
  | .const z => z
  | .plus e₁ e₂ => e₁.eval + e₂.eval
  | .mul e₁ e₂ => e₁.eval * e₂.eval

example : (Expr.plus (.const (-4)) (.const 5)).eval = 1 := by decide

theorem plus_eval_comm (e₁ e₂ : Expr) : (e₁ +ₑ e₂).eval = (e₂ +ₑ e₁).eval := by
  simp [Expr.eval, Int.add_comm]

theorem plus_syntax_not_comm :
    (Expr.plus (.const 0) (.const 1)) ≠ (Expr.plus (.const 1) (.const 0)) := by decide

/-! ## Exercise 2: open arithmetic expressions -/

inductive Expr' where
  | var (x : String)
  | const (z : Int)
  | plus (e₁ e₂ : Expr')
  | mul (e₁ e₂ : Expr')
  deriving Repr, DecidableEq

/-- `e.isClosed X` holds when every variable of `e` occurs in `X`. -/
def Expr'.isClosed (X : List String) : Expr' → Bool
  | .var x => x ∈ X
  | .const _ => true
  | .plus e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .mul e₁ e₂ => e₁.isClosed X && e₂.isClosed X

/-- `Prop`-valued form of `Expr'.isClosed`. -/
abbrev closed (X : List String) (e : Expr') : Prop := e.isClosed X = true

example : closed [] (.plus (.const 3) (.const 5)) := by decide

example : closed ["x", "y"] (.plus (.var "x") (.var "y")) := by decide

example : ¬ closed ["x"] (.plus (.var "x") (.var "y")) := by decide

theorem closed_mono {X Y : List String} {e : Expr'}
    (hsub : ∀ x, x ∈ X → x ∈ Y) (h : closed X e) : closed Y e := by
  induction e with
  | var x =>
    simp only [closed, Expr'.isClosed, decide_eq_true_eq] at h ⊢
    exact hsub x h
  | const _ => rfl
  | plus _ _ ih₁ ih₂ | mul _ _ ih₁ ih₂ =>
    simp only [closed, Expr'.isClosed, Bool.and_eq_true] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩

/-- Substitution of `e'` for `x` in `e`. -/
def Expr'.subst : Expr' → String → Expr' → Expr'
  | .var y, x, e' => if x = y then e' else .var y
  | .const z, _, _ => .const z
  | .plus e₁ e₂, x, e' => .plus (e₁.subst x e') (e₂.subst x e')
  | .mul e₁ e₂, x, e' => .mul (e₁.subst x e') (e₂.subst x e')

theorem subst_closed {X : List String} {e e' : Expr'} {x : String}
    (h : closed X e) (hx : x ∉ X) : e.subst x e' = e := by
  induction e with
  | var y =>
    simp only [closed, Expr'.isClosed, decide_eq_true_eq] at h
    simp only [Expr'.subst, ite_eq_right_iff]
    rintro rfl
    exact (hx h).elim
  | const _ => rfl
  | plus _ _ ih₁ ih₂ | mul _ _ ih₁ ih₂ =>
    simp only [closed, Expr'.isClosed, Bool.and_eq_true] at h
    simp only [Expr'.subst, ih₁ h.1, ih₂ h.2]

/-- Evaluation against an environment; unbound variables default to `0`. -/
def Expr'.eval (m : StlcExtended.MapStr Int) : Expr' → Int
  | .var x => (get? (M := StlcExtended.MapStr) m x).getD 0
  | .const z => z
  | .plus e₁ e₂ => e₁.eval m + e₂.eval m
  | .mul e₁ e₂ => e₁.eval m * e₂.eval m

/-- Substituting and then evaluating is evaluating in the extended environment. -/
theorem eval_subst_extend (m : StlcExtended.MapStr Int) (e : Expr') (x : String) (e' : Expr') :
    (e.subst x e').eval m
      = e.eval (insert (M := StlcExtended.MapStr) m x (e'.eval m)) := by
  induction e with
  | var y =>
    simp only [Expr'.subst, Expr'.eval, StlcExtended.get?_insert]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, Expr'.eval]
  | const _ => rfl
  | plus _ _ ih₁ ih₂ | mul _ _ ih₁ ih₂ => simp only [Expr'.subst, Expr'.eval, ih₁, ih₂]

end Warmup
