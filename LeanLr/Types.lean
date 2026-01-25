/-
  Simply Typed Lambda Calculus (STLC) - Type System
  Defines types, typing contexts, and typing judgments
-/

import LeanLr.Lang
import Std.Data.ExtTreeMap
import LeanLr.Notation

import Iris.Std.FiniteMap
import Iris.Std.FiniteMapInst
import Iris.Std.FiniteSet
import Iris.Std.FiniteSetInst
import Iris.Std.FiniteMapDom

open Iris.Std

namespace STLC
-- Types in STLC
inductive Ty where
  | int : Ty
  | fun : Ty → Ty → Ty
  deriving Repr, DecidableEq

-- Notation for function types
infixr:70 " ⇒ " => Ty.fun

-- Typing context using FiniteMap interface (like gmap in Coq)
-- The underlying implementation is ExtTreeMap, but we use the abstract interface
abbrev Context := Std.ExtTreeMap String Ty compare

-- Type alias for the FiniteMap instance type
abbrev CtxMap := Std.ExtTreeMap String

abbrev StringSet := Std.TreeSet String compare

-- Use FiniteMap operations for Context
-- We use the FiniteMap instance for Std.ExtTreeMap

def Context.empty : Context :=
  (FiniteMap.empty : CtxMap Ty)

def Context.delete (Γ : Context) (x : String) : Context :=
  (FiniteMap.delete Γ x : CtxMap Ty)

def Context.insert (Γ : Context) (x : String) (A : Ty) : Context :=
  (FiniteMap.insert (FiniteMap.delete Γ x : CtxMap Ty) x A : CtxMap Ty)

-- TODO: have the `(<[x:=A]> Γ)` notation ≠
notation:90 Γ " <[ " x " := " A " ]> " => Context.insert Γ x A

def Context.lookup (Γ : Context) (x : String) : Option Ty :=
  FiniteMap.get? (M := CtxMap) Γ x

-- Return domain as a List (for compatibility with proofs using List operations)
def Context.domList (Γ : Context) : List String :=
  (FiniteMap.toList (M := CtxMap) Γ).map Prod.fst

-- Return domain as a FiniteSet (default) using FiniteMapDom
def Context.dom (Γ : Context) : StringSet :=
  domSet (M := CtxMap) (S := StringSet) Γ


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
