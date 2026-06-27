/-
  System F with recursive types and mutable state - Type System
  Types use De Bruijn indices for type variables.
  Ported from semantics-2025/theories/type_systems/systemf_mu_state/types.v
-/

import LeanLR.TypeSystems.SystemFMuState.Lang

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

open Iris.Std

namespace SystemFMuState

-- Types with De Bruijn indices for type variables
inductive Ty where
  | tVar (n : Nat)       -- type variable (De Bruijn index)
  | int                  -- integers
  | bool                 -- booleans
  | unit                 -- unit type
  | fn (A B : Ty)        -- function type A → B
  | all (A : Ty)         -- ∀ α. A (binds one type variable)
  | exist (A : Ty)       -- ∃ α. A (binds one type variable)
  | prod (A B : Ty)      -- product type A × B
  | sum (A B : Ty)       -- sum type A + B
  | mu (A : Ty)          -- recursive type μ α. A (binds one type variable)
  | ref (A : Ty)         -- reference type Ref A
  deriving Repr, DecidableEq


-- Type well-formedness: all type variables must be bound
-- n is the number of bound type variables in scope
inductive TypeWf : Nat → Ty → Prop where
  | tVar_wf : m < n → TypeWf n (.tVar m)
  | int_wf : TypeWf n .int
  | bool_wf : TypeWf n .bool
  | unit_wf : TypeWf n .unit
  | fn_wf : TypeWf n A → TypeWf n B → TypeWf n (.fn A B)
  | all_wf : TypeWf (n + 1) A → TypeWf n (.all A)
  | exist_wf : TypeWf (n + 1) A → TypeWf n (.exist A)
  | prod_wf : TypeWf n A → TypeWf n B → TypeWf n (.prod A B)
  | sum_wf : TypeWf n A → TypeWf n B → TypeWf n (.sum A B)
  | mu_wf : TypeWf (n + 1) A → TypeWf n (.mu A)
  | ref_wf : TypeWf n A → TypeWf n (.ref A)

-- Rename: shift type variable indices ≥ cutoff up by amount
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .tVar n => .tVar (f n)
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .fn A B => .fn (A.rename f) (B.rename f)
  | .all A => .all (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .exist A => .exist (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .prod A B => .prod (A.rename f) (B.rename f)
  | .sum A B => .sum (A.rename f) (B.rename f)
  | .mu A => .mu (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .ref A => .ref (A.rename f)

-- Type substitution: substitute type variable 0, shift rest down
def Ty.substTy (σ : Nat → Ty) : Ty → Ty
  | .tVar n => σ n
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .fn A B => .fn (A.substTy σ) (B.substTy σ)
  | .all A => .all (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .exist A => .exist (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .prod A B => .prod (A.substTy σ) (B.substTy σ)
  | .sum A B => .sum (A.substTy σ) (B.substTy σ)
  | .mu A => .mu (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .ref A => .ref (A.substTy σ)

-- Single type substitution: replace var 0 with B
def Ty.subst1 (B : Ty) (A : Ty) : Ty :=
  A.substTy (fun n => match n with | 0 => B | n+1 => .tVar n)

-- Typing context (maps variable names to types, like gmap string type)
abbrev TyMapStr (V : Type) := Std.ExtTreeMap String V compare
abbrev TypingContext := TyMapStr Ty

-- Heap typing (list of types indexed by location)
-- In the Coq version this is a list; we follow that
abbrev HeapContext := List Ty

-- Unary operator typing
inductive UnOpTyped : UnOp → Ty → Ty → Prop where
  | neg_typed : UnOpTyped .negOp .bool .bool
  | minus_typed : UnOpTyped .minusUnOp .int .int

-- Binary operator typing
inductive BinOpTyped : BinOp → Ty → Ty → Ty → Prop where
  | plus_typed : BinOpTyped .plusOp .int .int .int
  | minus_typed : BinOpTyped .minusOp .int .int .int
  | mult_typed : BinOpTyped .multOp .int .int .int
  | lt_typed : BinOpTyped .ltOp .int .int .bool
  | le_typed : BinOpTyped .leOp .int .int .bool
  | eq_typed : BinOpTyped .eqOp .int .int .bool

-- Syntactic typing judgment
-- n = number of type variables in scope (De Bruijn level)
-- Γ = typing context (variable name → type)
-- hctx = heap typing context (location index → type)
inductive SynTyped : Nat → TypingContext → HeapContext → Expr → Ty → Prop where
  | typed_lit_int n Γ hctx (z : Int) :
      SynTyped n Γ hctx (.lit (.litInt z)) .int
  | typed_lit_bool n Γ hctx (b : Bool) :
      SynTyped n Γ hctx (.lit (.litBool b)) .bool
  | typed_lit_unit n Γ hctx :
      SynTyped n Γ hctx (.lit .litUnit) .unit
  | typed_var n Γ hctx (x : String) A :
      get? (M := TyMapStr) Γ x = some A →
      SynTyped n Γ hctx (.var x) A
  | typed_lam n Γ hctx (x : String) e A B :
      TypeWf n A →
      SynTyped n (insert (M := TyMapStr) Γ x A) hctx e B →
      SynTyped n Γ hctx (.lam (.bNamed x) e) (.fn A B)
  | typed_app n Γ hctx e₁ e₂ A B :
      SynTyped n Γ hctx e₁ (.fn A B) →
      SynTyped n Γ hctx e₂ A →
      SynTyped n Γ hctx (.app e₁ e₂) B
  | typed_tLam n Γ hctx e A :
      SynTyped (n + 1) Γ hctx e A →
      SynTyped n Γ hctx (.tLam e) (.all A)
  | typed_tApp n Γ hctx e A B :
      TypeWf n B →
      SynTyped n Γ hctx e (.all A) →
      SynTyped n Γ hctx (.tApp e) (A.subst1 B)
  | typed_pack n Γ hctx e A B :
      TypeWf n B →
      TypeWf (n + 1) A →
      SynTyped n Γ hctx e (A.subst1 B) →
      SynTyped n Γ hctx (.pack e) (.exist A)
  | typed_unpack n Γ hctx (x : String) e₁ e₂ A B :
      TypeWf n B →
      SynTyped n Γ hctx e₁ (.exist A) →
      SynTyped (n + 1) (insert (M := TyMapStr) Γ x A) hctx e₂ B →
      SynTyped n Γ hctx (.unpack (.bNamed x) e₁ e₂) B
  | typed_pair n Γ hctx e₁ e₂ A B :
      SynTyped n Γ hctx e₁ A →
      SynTyped n Γ hctx e₂ B →
      SynTyped n Γ hctx (.pair e₁ e₂) (.prod A B)
  | typed_fst n Γ hctx e A B :
      SynTyped n Γ hctx e (.prod A B) →
      SynTyped n Γ hctx (.fst e) A
  | typed_snd n Γ hctx e A B :
      SynTyped n Γ hctx e (.prod A B) →
      SynTyped n Γ hctx (.snd e) B
  | typed_injL n Γ hctx e A B :
      TypeWf n B →
      SynTyped n Γ hctx e A →
      SynTyped n Γ hctx (.injL e) (.sum A B)
  | typed_injR n Γ hctx e A B :
      TypeWf n A →
      SynTyped n Γ hctx e B →
      SynTyped n Γ hctx (.injR e) (.sum A B)
  | typed_case n Γ hctx e e₁ e₂ A B C :
      SynTyped n Γ hctx e (.sum A B) →
      SynTyped n Γ hctx e₁ (.fn A C) →
      SynTyped n Γ hctx e₂ (.fn B C) →
      SynTyped n Γ hctx (.case e e₁ e₂) C
  | typed_unOp n Γ hctx op e A B :
      UnOpTyped op A B →
      SynTyped n Γ hctx e A →
      SynTyped n Γ hctx (.unOp op e) B
  | typed_binOp n Γ hctx op e₁ e₂ A B C :
      BinOpTyped op A B C →
      SynTyped n Γ hctx e₁ A →
      SynTyped n Γ hctx e₂ B →
      SynTyped n Γ hctx (.binOp op e₁ e₂) C
  | typed_if n Γ hctx e₀ e₁ e₂ A :
      SynTyped n Γ hctx e₀ .bool →
      SynTyped n Γ hctx e₁ A →
      SynTyped n Γ hctx e₂ A →
      SynTyped n Γ hctx (.ite e₀ e₁ e₂) A
  | typed_roll n Γ hctx e A :
      SynTyped n Γ hctx e (A.subst1 (.mu A)) →
      SynTyped n Γ hctx (.roll e) (.mu A)
  | typed_unroll n Γ hctx e A :
      SynTyped n Γ hctx e (.mu A) →
      SynTyped n Γ hctx (.unroll e) (A.subst1 (.mu A))
  -- State operations
  | typed_new n Γ hctx e A :
      SynTyped n Γ hctx e A →
      SynTyped n Γ hctx (.new e) (.ref A)
  | typed_load n Γ hctx e A :
      SynTyped n Γ hctx e (.ref A) →
      SynTyped n Γ hctx (.load e) A
  | typed_store n Γ hctx e₁ e₂ A :
      SynTyped n Γ hctx e₁ (.ref A) →
      SynTyped n Γ hctx e₂ A →
      SynTyped n Γ hctx (.store e₁ e₂) .unit

end SystemFMuState
