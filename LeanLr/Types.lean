/-
  Simply Typed Lambda Calculus (STLC) - Type System
  Defines types, typing contexts, and typing judgments
-/

import LeanLr.Lang
import Std.Data.ExtTreeMap
import LeanLr.Notation

namespace STLC

-- Types in STLC
inductive Ty where
  | int : Ty
  | fun : Ty → Ty → Ty
  deriving Repr, DecidableEq

-- Notation for function types
infixr:70 " ⇒ " => Ty.fun

-- Typing context using ExtTreeMap (like gmap in Coq)
abbrev Context := Std.ExtTreeMap String Ty compare

def Context.empty : Context := ∅

def Context.delete (Γ : Context) (x : String) : Context :=
  Γ.erase x

def Context.insert (Γ : Context) (x : String) (A : Ty) : Context :=
  (Γ.erase x).insert x A

-- TODO: have the `(<[x:=A]> Γ)` notation


def Context.lookup (Γ : Context) (x : String) : Option Ty :=
  Γ.get? x

def Context.dom (Γ : Context) : List String :=
  Γ.foldl (fun acc k _ => k :: acc) []

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
