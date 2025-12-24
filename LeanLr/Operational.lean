import LeanLr.Lang

namespace STLC

def subst (x : String) (es : Expr) : Expr → Expr
  | Expr.var y => if x = y then es else Expr.var y
  | Expr.lam y e =>
      if Binder.named x = y then
        Expr.lam y e  -- Variable shadowing
      else
        Expr.lam y (subst x es e)
  | Expr.app e₁ e₂ =>
      Expr.app (subst x es e₁) (subst x es e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ =>
      Expr.plus (subst x es e₁) (subst x es e₂)

def subst' (b : Binder) (es : Expr): Expr → Expr :=
  match b with
  | Binder.named x => subst x es
  | _ => id

-- Notation for substitution
notation:90 e "[" x " := " es "]" => subst x es e

inductive BigStep : Expr → Val → Prop where
  | litInt : ∀ {n},
      BigStep (Expr.litInt n) (Val.litIntV n)

  | lam : ∀ {x e},
      BigStep (Expr.lam x e) (Val.lamV x e)

  | app : ∀ {e₁ e₂ x e v₂ v},
      BigStep e₁ (Val.lamV x e) →
      BigStep e₂ v₂ →
      BigStep (subst' x v₂.toExpr e) v →
      BigStep (Expr.app e₁ e₂) v

  | plus : ∀ {e₁ e₂ n₁ n₂},
      BigStep e₁ (Val.litIntV n₁) →
      BigStep e₂ (Val.litIntV n₂) →
      BigStep (Expr.plus e₁ e₂) (Val.litIntV (n₁ + n₂))

notation:50 e " ⇓ " v => BigStep e v

-- Helper: A value evaluates to itself
def val_evals_to_self (v : Val) : v.toExpr ⇓ v :=
  match v with
  | Val.litIntV _ => BigStep.litInt
  | Val.lamV _ _ => BigStep.lam

def terminates (e : Expr) : Prop :=
  ∃ v, e ⇓ v

theorem bigstep_deterministic {e : Expr} {v₁ v₂ : Val} (h₁ : e ⇓ v₁) (h₂ : e ⇓ v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | litInt => cases h₂; rfl
  | lam => cases h₂; rfl
  | app he₁ he₂ he₃ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | app he₁' he₂' he₃' =>
      have eq₁ := ih₁ he₁'
      injection eq₁ with h_x h_e
      have eq₂ := ih₂ he₂'
      subst h_x h_e eq₂
      exact ih₃ he₃'
  | plus hp₁ hp₂ ih₁ ih₂ =>
    cases h₂ with
    | plus hp₁' hp₂' =>
      have eq₁ := ih₁ hp₁'
      have eq₂ := ih₂ hp₂'
      injection eq₁ with heq₁
      injection eq₂ with heq₂
      cases heq₁; cases heq₂; rfl

end STLC
