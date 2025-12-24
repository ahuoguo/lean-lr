/-
  Simply Typed Lambda Calculus (STLC) - Language Definition
  Defines syntax, values, and basic operations
-/


namespace STLC

inductive Binder where
  | named : String → Binder
  | anon : Binder
  deriving Repr, DecidableEq

def Binder.cons (b : Binder) (ss : List String) : List String :=
  match b with
  | Binder.anon => ss
  | Binder.named s => s :: ss

notation :90 b " :b: " ss => Binder.cons b ss

-- Expressions
inductive Expr where
  | var : String → Expr
  | lam : Binder → Expr → Expr
  | app : Expr → Expr → Expr
  | litInt : Int → Expr
  | plus : Expr → Expr → Expr
  deriving Repr, DecidableEq

-- Values (subset of expressions)
inductive Val where
  | litIntV : Int → Val
  | lamV : Binder → Expr → Val
  deriving Repr

-- Convert value to expression
def Val.toExpr : Val → Expr
  | Val.litIntV n => Expr.litInt n
  | Val.lamV x e => Expr.lam x e

-- Check if an expression is a value
def Expr.isValue : Expr → Bool
  | Expr.litInt _ => true
  | Expr.lam _ _ => true
  | _ => false

-- Convert expression to value if possible
def Expr.toVal? : Expr → Option Val
  | Expr.litInt n => some (Val.litIntV n)
  | Expr.lam x e => some (Val.lamV x e)
  | _ => none

def Expr.closed (X : List String) : Expr → Bool
  | Expr.var x => x ∈ X
  | Expr.lam x e => Expr.closed (x :b: X) e
  | Expr.app e₁ e₂ => Expr.closed X e₁ && Expr.closed X e₂
  | Expr.litInt _ => true
  | Expr.plus e₁ e₂ => Expr.closed X e₁ && Expr.closed X e₂

end STLC
