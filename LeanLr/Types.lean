/-
  Simply Typed Lambda Calculus (STLC) - Type System
  Defines types, typing contexts, and typing judgments
-/

import LeanLr.Lang
import LeanLr.Notation

import Iris.Std.PartialMap
import Iris.Std.GenSets
import Iris.Std.GenSetsInstances
import Iris.Std.HeapInstances

open Iris.Std

namespace STLC
-- Types in STLC
inductive Ty where
  | int : Ty
  | fun : Ty → Ty → Ty
  deriving Repr, DecidableEq

-- Notation for function types
infixr:70 " ⇒ " => Ty.fun

-- The type constructor for our maps (like gmap string in Coq)
abbrev MapStr (V : Type) := Std.ExtTreeMap String V compare

-- Typing context
abbrev Context := MapStr Ty

-- Set type for domains
abbrev StringSet := Std.ExtTreeSet String compare

def Context.empty : Context := PartialMap.empty (M := MapStr) (V := Ty)

def Context.delete (Γ : Context) (x : String) : Context :=
  Iris.Std.delete (M := MapStr) Γ x

def Context.insert (Γ : Context) (x : String) (A : Ty) : Context :=
  Iris.Std.insert (M := MapStr) (Iris.Std.delete (M := MapStr) Γ x) x A

notation:90 Γ " <[ " x " := " A " ]> " => Context.insert Γ x A

def Context.lookup (Γ : Context) (x : String) : Option Ty :=
  Iris.Std.get? (M := MapStr) Γ x

def Context.domList (Γ : Context) : List String :=
  (FiniteMap.toList (M := MapStr) Γ).map Prod.fst

def Context.dom (Γ : Context) : StringSet :=
  FiniteMap.dom_set (M := MapStr) Γ


inductive SynTyped : Context → Expr → Ty → Prop where
  | var : ∀ {Γ x A},
      Γ.lookup x = some A →
      SynTyped Γ (Expr.var x) A

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
