/-
  Simply Typed Lambda Calculus (STLC) - Type System
  Defines types, typing contexts, and typing judgments
-/

import LeanLr.Lang
import Std.Data.HashMap
import LeanLr.Notation

namespace STLC

-- Types in STLC
inductive Ty where
  | int : Ty
  | fun : Ty → Ty → Ty
  deriving Repr, DecidableEq

-- Notation for function types
infixr:70 " ⇒ " => Ty.fun

-- TODO: easier representation as gmap? Also see comment for Subst
def Context := List (String × Ty)

def Context.empty : Context := []

def Context.delete (Γ : Context) (x : String) : Context :=
  Γ.filter (fun p => p.1 ≠ x)

def Context.insert (Γ : Context) (x : String) (A : Ty) : Context :=
  (x, A) :: Γ.delete x

def Context.lookup (Γ : Context) (x : String) : Option Ty :=
  List.lookup x Γ

def Context.dom (Γ : Context) : List String :=
  Γ.map (·.1)

inductive SynTyped : Context → Expr → Ty → Prop where
  | var : ∀ {Γ x A},
      Γ.lookup x = some A →
      SynTyped Γ (Expr.var x) A

  -- TODO: semantics course did not consider anonymous lambdas, we follow them
  | lam_named : ∀ {Γ x e A B},
      SynTyped (Γ.insert x A) e B →
      SynTyped Γ (Expr.lam (Binder.named x) e) (A ⇒ B)

  | app : ∀ {Γ e₁ e₂ A B},
      SynTyped Γ e₁ (A ⇒ B) →
      SynTyped Γ e₂ A →
      SynTyped Γ (e₁ e₂) B

  | litInt : ∀ {Γ n},
      SynTyped Γ (Expr.litInt n) Ty.int

  | plus : ∀ {Γ e₁ e₂},
      SynTyped Γ e₁ Ty.int →
      SynTyped Γ e₂ Ty.int →
      SynTyped Γ (e₁ +ₑ e₂) Ty.int

notation:74 Γ " ⊢ " e " : " A => SynTyped Γ e A

end STLC
