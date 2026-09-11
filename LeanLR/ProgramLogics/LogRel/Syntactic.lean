import LeanLR.ProgramLogics.LogRel.Notation

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# Syntactic typing for the heap_lang embedding

`program_logics/logrel/syntactic.v`. The types are those of System F with recursive types and
references, over heap_lang expressions; type variables are De Bruijn indices, so `Ty.rename`,
`Ty.substTy` and the equations they satisfy stand in for Autosubst.

The type system deliberately does *not* satisfy preservation: nothing below the `Exp.val`
constructor is typed, because substitution does not descend below it. That costs nothing here —
the logical relation substitutes all values first, and a `Exp.rec_` reduces to a closed
`Val.rec_` in one step.
-/

open Iris.HeapLang Iris.Std

namespace ProgramLogics.LogRel

/-! ## Types -/

/-- Types, with type variables as De Bruijn indices. `all`, `exist` and `mu` each bind one type
variable in their body. -/
inductive Ty where
  | tVar (n : Nat)
  | int
  | bool
  | unit
  | all (A : Ty)
  | exist (A : Ty)
  | fn (A B : Ty)
  | mu (A : Ty)
  | ref (A : Ty)
  | prod (A B : Ty)
  | sum (A B : Ty)
  deriving Repr, DecidableEq

/-! ## Renaming and substitution -/

/-- Renames the free type variables of a type along `f`, lifting `f` under each binder. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .tVar n => .tVar (f n)
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .all A => .all (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .exist A => .exist (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .fn A B => .fn (A.rename f) (B.rename f)
  | .mu A => .mu (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .ref A => .ref (A.rename f)
  | .prod A B => .prod (A.rename f) (B.rename f)
  | .sum A B => .sum (A.rename f) (B.rename f)

/-- Applies the type substitution `σ` to the free type variables of a type, lifting `σ` under each
binder. -/
def Ty.substTy (σ : Nat → Ty) : Ty → Ty
  | .tVar n => σ n
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .all A =>
    .all (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .exist A =>
    .exist (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .fn A B => .fn (A.substTy σ) (B.substTy σ)
  | .mu A => .mu (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .ref A => .ref (A.substTy σ)
  | .prod A B => .prod (A.substTy σ) (B.substTy σ)
  | .sum A B => .sum (A.substTy σ) (B.substTy σ)

/-- `A.subst1 B` is `A[0 := B]`: replaces type variable `0` in `A` by `B` and shifts the rest
down. -/
def Ty.subst1 (A B : Ty) : Ty :=
  A.substTy (fun n => match n with | 0 => B | n+1 => .tVar n)

/-! ## Composition equations

Autosubst's `SubstLemmas` instance, by hand. -/

theorem Ty.rename_ext (A : Ty) :
    ∀ (f g : Nat → Nat), (∀ n, f n = g n) → A.rename f = A.rename g := by
  induction A with
  | tVar n => intro f g h; simp only [Ty.rename, h n]
  | int | bool | unit => intro _ _ _; rfl
  | ref _ ih => intro f g h; simp only [Ty.rename, ih f g h]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    intro f g h
    simp only [Ty.rename, ihA f g h, ihB f g h]
  | all _ ih | exist _ ih | mu _ ih =>
    intro f g h
    refine congrArg _ (ih _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [h m]

theorem Ty.substTy_ext (A : Ty) :
    ∀ (σ τ : Nat → Ty), (∀ n, σ n = τ n) → A.substTy σ = A.substTy τ := by
  induction A with
  | tVar n => intro σ τ h; simp only [Ty.substTy, h n]
  | int | bool | unit => intro _ _ _; rfl
  | ref _ ih => intro σ τ h; simp only [Ty.substTy, ih σ τ h]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    intro σ τ h
    simp only [Ty.substTy, ihA σ τ h, ihB σ τ h]
  | all _ ih | exist _ ih | mu _ ih =>
    intro σ τ h
    refine congrArg _ (ih _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [h m]

theorem Ty.rename_rename (A : Ty) (f g : Nat → Nat) :
    (A.rename g).rename f = A.rename (fun n => f (g n)) := by
  induction A generalizing f g with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.rename, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.rename, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, ih]
    exact congrArg _ (Ty.rename_ext _ _ _ fun n => by cases n <;> rfl)

theorem Ty.rename_substTy (A : Ty) (σ : Nat → Ty) (g : Nat → Nat) :
    (A.rename g).substTy σ = A.substTy (fun n => σ (g n)) := by
  induction A generalizing σ g with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.rename, Ty.substTy, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ fun n => by cases n <;> rfl)

theorem Ty.substTy_rename (A : Ty) (σ : Nat → Ty) (f : Nat → Nat) :
    (A.substTy σ).rename f = A.substTy (fun n => (σ n).rename f) := by
  induction A generalizing σ f with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.rename, Ty.substTy, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    refine congrArg _ (Ty.substTy_ext _ _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [Ty.rename_rename]

theorem Ty.substTy_id (A : Ty) : A.substTy (fun n => .tVar n) = A := by
  induction A with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.substTy, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.substTy]
    refine congrArg _ ?_
    rw [Ty.substTy_ext _ _ (fun n => .tVar n) fun n => by cases n <;> rfl]
    exact ih

/-- Lifting a substitution under a binder commutes with composition. -/
theorem Ty.up_substTy_comm (σ τ : Nat → Ty) : ∀ n,
    ((fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1)) n).substTy
      (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (τ n).rename (· + 1))
    = (fun n => match n with | 0 => Ty.tVar 0 | n+1 => ((σ n).substTy τ).rename (· + 1)) n := by
  intro n
  cases n with
  | zero => rfl
  | succ m =>
    show ((σ m).rename (· + 1)).substTy
        (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (τ n).rename (· + 1))
      = ((σ m).substTy τ).rename (· + 1)
    rw [Ty.rename_substTy, Ty.substTy_rename]

theorem Ty.substTy_substTy (A : Ty) (σ τ : Nat → Ty) :
    (A.substTy σ).substTy τ = A.substTy (fun n => (σ n).substTy τ) := by
  induction A generalizing σ τ with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.substTy, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ (Ty.up_substTy_comm σ τ))

/-! ## Operator typing -/

inductive BinOpTyped : BinOp → Ty → Ty → Ty → Prop where
  | plus_op_typed : BinOpTyped .plus .int .int .int
  | minus_op_typed : BinOpTyped .minus .int .int .int
  | mul_op_typed : BinOpTyped .mult .int .int .int
  | lt_op_typed : BinOpTyped .lt .int .int .bool
  | le_op_typed : BinOpTyped .le .int .int .bool
  | eq_op_typed : BinOpTyped .eq .int .int .bool

inductive UnOpTyped : UnOp → Ty → Ty → Prop where
  | neg_op_typed : UnOpTyped .neg .bool .bool
  | minus_un_op_typed : UnOpTyped .minus .int .int

/-! ## Well-formedness -/

/-- `TypeWf n A` says every type variable of `A` is bound: free indices are below `n`. -/
inductive TypeWf : Nat → Ty → Prop where
  | type_wf_TVar : m < n → TypeWf n (.tVar m)
  | type_wf_Int : TypeWf n .int
  | type_wf_Bool : TypeWf n .bool
  | type_wf_Unit : TypeWf n .unit
  | type_wf_TForall : TypeWf (n + 1) A → TypeWf n (.all A)
  | type_wf_TExists : TypeWf (n + 1) A → TypeWf n (.exist A)
  | type_wf_Fun : TypeWf n A → TypeWf n B → TypeWf n (.fn A B)
  | type_wf_Prod : TypeWf n A → TypeWf n B → TypeWf n (.prod A B)
  | type_wf_Sum : TypeWf n A → TypeWf n B → TypeWf n (.sum A B)
  | type_wf_mu : TypeWf (n + 1) A → TypeWf n (.mu A)
  | type_wf_ref : TypeWf n A → TypeWf n (.ref A)

/-! ## Typing contexts -/

/-- Finite maps keyed by term-variable names. -/
abbrev TyMapStr (V : Type) := Std.ExtTreeMap String V compare

/-- Assigns types to the term variables in scope. -/
abbrev TypingContext := TyMapStr Ty

/-- Shifts every type in the context up by one type variable, as the typing rules must whenever
they descend under a type-variable binder. Rocq writes it `⤉ Γ`. -/
def shiftCtx (Γ : TypingContext) : TypingContext :=
  Iris.Std.PartialMap.map (M := TyMapStr) (fun A : Ty => A.rename (· + 1)) Γ

theorem shiftCtx_get? (Γ : TypingContext) (x : String) :
    get? (M := TyMapStr) (shiftCtx Γ) x
      = (get? (M := TyMapStr) Γ x).map (fun A => A.rename (· + 1)) :=
  Iris.Std.LawfulPartialMap.get?_map

/-! ## Syntactic typing

Rocq writes `SynTyped n Γ e A` as `TY n; Γ ⊢ e : A`. -/

inductive SynTyped : Nat → TypingContext → Exp → Ty → Prop where
  | typed_var (n : Nat) (Γ : TypingContext) (x : String) (A : Ty) :
      get? (M := TyMapStr) Γ x = some A →
      SynTyped n Γ (.var x) A
  | typed_lam (n : Nat) (Γ : TypingContext) (x : String) (e : Exp) (A B : Ty) :
      SynTyped n (insert (M := TyMapStr) Γ x A) e B →
      TypeWf n A →
      SynTyped n Γ (.rec_ .anon (.named x) e) (.fn A B)
  | typed_lam_anon (n : Nat) (Γ : TypingContext) (e : Exp) (A B : Ty) :
      SynTyped n Γ e B →
      TypeWf n A →
      SynTyped n Γ (.rec_ .anon .anon e) (.fn A B)
  | typed_tlam (n : Nat) (Γ : TypingContext) (e : Exp) (A : Ty) :
      SynTyped (n + 1) (shiftCtx Γ) e A →
      SynTyped n Γ (tLam e) (.all A)
  | typed_tapp (n : Nat) (Γ : TypingContext) (A B : Ty) (e : Exp) :
      SynTyped n Γ e (.all A) →
      TypeWf n B →
      SynTyped n Γ (tApp e) (A.subst1 B)
  | typed_pack (n : Nat) (Γ : TypingContext) (A B : Ty) (e : Exp) :
      TypeWf n B →
      TypeWf (n + 1) A →
      SynTyped n Γ e (A.subst1 B) →
      SynTyped n Γ (pack e) (.exist A)
  | typed_unpack (n : Nat) (Γ : TypingContext) (A B : Ty) (e e' : Exp) (x : String) :
      TypeWf n B →
      SynTyped n Γ e (.exist A) →
      SynTyped (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x A) e' (B.rename (· + 1)) →
      SynTyped n Γ (unpack e (.named x) e') B
  | typed_int (n : Nat) (Γ : TypingContext) (z : Int) :
      SynTyped n Γ hl(#z) .int
  | typed_bool (n : Nat) (Γ : TypingContext) (b : Bool) :
      SynTyped n Γ hl(#b) .bool
  | typed_unit (n : Nat) (Γ : TypingContext) :
      SynTyped n Γ hl(#()) .unit
  | typed_if (n : Nat) (Γ : TypingContext) (e₀ e₁ e₂ : Exp) (A : Ty) :
      SynTyped n Γ e₀ .bool →
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ A →
      SynTyped n Γ (.if e₀ e₁ e₂) A
  | typed_app (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (A B : Ty) :
      SynTyped n Γ e₁ (.fn A B) →
      SynTyped n Γ e₂ A →
      SynTyped n Γ (.app e₁ e₂) B
  | typed_binop (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (op : BinOp) (A B C : Ty) :
      BinOpTyped op A B C →
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ B →
      SynTyped n Γ (.binop op e₁ e₂) C
  | typed_unop (n : Nat) (Γ : TypingContext) (e : Exp) (op : UnOp) (A B : Ty) :
      UnOpTyped op A B →
      SynTyped n Γ e A →
      SynTyped n Γ (.unop op e) B
  | typed_pair (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (A B : Ty) :
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ B →
      SynTyped n Γ (.pair e₁ e₂) (.prod A B)
  | typed_fst (n : Nat) (Γ : TypingContext) (e : Exp) (A B : Ty) :
      SynTyped n Γ e (.prod A B) →
      SynTyped n Γ (.fst e) A
  | typed_snd (n : Nat) (Γ : TypingContext) (e : Exp) (A B : Ty) :
      SynTyped n Γ e (.prod A B) →
      SynTyped n Γ (.snd e) B
  | typed_injl (n : Nat) (Γ : TypingContext) (e : Exp) (A B : Ty) :
      TypeWf n B →
      SynTyped n Γ e A →
      SynTyped n Γ (.injL e) (.sum A B)
  | typed_injr (n : Nat) (Γ : TypingContext) (e : Exp) (A B : Ty) :
      TypeWf n A →
      SynTyped n Γ e B →
      SynTyped n Γ (.injR e) (.sum A B)
  | typed_case (n : Nat) (Γ : TypingContext) (e e₁ e₂ : Exp) (A B C : Ty) :
      SynTyped n Γ e (.sum B C) →
      SynTyped n Γ e₁ (.fn B A) →
      SynTyped n Γ e₂ (.fn C A) →
      SynTyped n Γ (.case e e₁ e₂) A
  | typed_roll (n : Nat) (Γ : TypingContext) (e : Exp) (A : Ty) :
      SynTyped n Γ e (A.subst1 (.mu A)) →
      SynTyped n Γ (roll e) (.mu A)
  | typed_unroll (n : Nat) (Γ : TypingContext) (e : Exp) (A : Ty) :
      SynTyped n Γ e (.mu A) →
      SynTyped n Γ (unroll e) (A.subst1 (.mu A))
  | typed_load (n : Nat) (Γ : TypingContext) (e : Exp) (A : Ty) :
      SynTyped n Γ e (.ref A) →
      SynTyped n Γ (.load e) A
  | typed_store (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (A : Ty) :
      SynTyped n Γ e₁ (.ref A) →
      SynTyped n Γ e₂ A →
      SynTyped n Γ (.store e₁ e₂) .unit
  | typed_new (n : Nat) (Γ : TypingContext) (e : Exp) (A : Ty) :
      SynTyped n Γ e A →
      SynTyped n Γ hl(ref(&e)) (.ref A)

end ProgramLogics.LogRel
