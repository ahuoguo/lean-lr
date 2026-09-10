import LeanLR.TypeSystems.SystemF.Lang

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# System F with recursive types and mutable state: type system

Types use De Bruijn indices for type variables, so type substitution is spelled out by hand:
`Ty.rename`, `Ty.substTy` and the composition equations they satisfy.
-/

open Iris.Std

namespace SystemF

/-! ## Types -/

/-- Types, with type variables as De Bruijn indices. `all`, `exist` and `mu` each bind one type
variable in their body. -/
inductive Ty where
  | tVar (n : Nat)
  | int
  | bool
  | unit
  | fn (A B : Ty)
  | all (A : Ty)
  | exist (A : Ty)
  | prod (A B : Ty)
  | sum (A B : Ty)
  deriving Repr, DecidableEq

/-- `TypeWf n A` says every type variable of `A` is bound: free indices are below `n`, the number
of type variables in scope. -/
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

/-! ## Renaming and substitution -/

/-- Renames the free type variables of a type along `f`, lifting `f` under each binder. -/
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

/-- Applies the type substitution `σ` to the free type variables of a type, lifting `σ` under each
binder. -/
def Ty.substTy (σ : Nat → Ty) : Ty → Ty
  | .tVar n => σ n
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .fn A B => .fn (A.substTy σ) (B.substTy σ)
  | .all A =>
    .all (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .exist A =>
    .exist (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .prod A B => .prod (A.substTy σ) (B.substTy σ)
  | .sum A B => .sum (A.substTy σ) (B.substTy σ)

/-- `A.subst1 B` is `A[0 := B]`: replaces type variable `0` in `A` by `B` and shifts the rest
down. -/
def Ty.subst1 (A B : Ty) : Ty :=
  A.substTy (fun n => match n with | 0 => B | n+1 => .tVar n)

/-! ## Composition equations

The standard renaming/substitution equations, proved by hand since there is no Autosubst. -/

/-- Renaming only depends on the renaming function pointwise. -/
theorem Ty.rename_ext (A : Ty) :
    ∀ (f g : Nat → Nat), (∀ n, f n = g n) → A.rename f = A.rename g := by
  induction A with
  | tVar n => intro f g h; simp only [Ty.rename, h n]
  | int | bool | unit => intro _ _ _; rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    intro f g h
    simp only [Ty.rename, ihA f g h, ihB f g h]
  | all _ ih | exist _ ih =>
    intro f g h
    refine congrArg _ (ih _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [h m]

/-- Substitution only depends on the substitution function pointwise. -/
theorem Ty.substTy_ext (A : Ty) :
    ∀ (σ τ : Nat → Ty), (∀ n, σ n = τ n) → A.substTy σ = A.substTy τ := by
  induction A with
  | tVar n => intro σ τ h; simp only [Ty.substTy, h n]
  | int | bool | unit => intro _ _ _; rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    intro σ τ h
    simp only [Ty.substTy, ihA σ τ h, ihB σ τ h]
  | all _ ih | exist _ ih =>
    intro σ τ h
    refine congrArg _ (ih _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [h m]

/-- Renaming composes: renaming by `g` and then by `f` is renaming by `f ∘ g`. -/
theorem Ty.rename_rename (A : Ty) (f g : Nat → Nat) :
    (A.rename g).rename f = A.rename (fun n => f (g n)) := by
  induction A generalizing f g with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.rename, ihA, ihB]
  | all _ ih | exist _ ih =>
    simp only [Ty.rename, ih]
    exact congrArg _ (Ty.rename_ext _ _ _ fun n => by cases n <;> rfl)

/-- Renaming followed by substitution fuses into a single substitution. -/
theorem Ty.rename_substTy (A : Ty) (σ : Nat → Ty) (g : Nat → Nat) :
    (A.rename g).substTy σ = A.substTy (fun n => σ (g n)) := by
  induction A generalizing σ g with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ fun n => by cases n <;> rfl)

/-- Substitution followed by renaming pushes the renaming into the substitution. -/
theorem Ty.substTy_rename (A : Ty) (σ : Nat → Ty) (f : Nat → Nat) :
    (A.substTy σ).rename f = A.substTy (fun n => (σ n).rename f) := by
  induction A generalizing σ f with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    refine congrArg _ (Ty.substTy_ext _ _ _ fun n => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [Ty.rename_rename]

/-- The identity substitution acts as the identity. -/
theorem Ty.substTy_id (A : Ty) : A.substTy (fun n => .tVar n) = A := by
  induction A with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih =>
    simp only [Ty.substTy]
    refine congrArg _ ?_
    rw [Ty.substTy_ext _ _ (fun n => .tVar n) fun n => by cases n <;> rfl]
    exact ih

/-- Lifting a substitution under a binder commutes with composition: lifting `σ` and then lifting
`τ` agrees pointwise with lifting the composite of `σ` and `τ`. -/
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

/-- Substitutions compose. -/
theorem Ty.substTy_substTy (A : Ty) (σ τ : Nat → Ty) :
    (A.substTy σ).substTy τ = A.substTy (fun n => (σ n).substTy τ) := by
  induction A generalizing σ τ with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih =>
    simp only [Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ (Ty.up_substTy_comm σ τ))

/-! ## Well-formedness -/

/-- Lifting a renaming under a binder keeps it bounded: it sends indices below `n + 1` to indices
below `n' + 1`. -/
private theorem lift_rename_lt {f : Nat → Nat} {n n' : Nat} (hf : ∀ m, m < n → f m < n') :
    ∀ m, m < n + 1 → (match m with | 0 => 0 | m+1 => (f m) + 1) < n' + 1 := by
  intro m hm
  match m with
  | 0 => exact Nat.zero_lt_succ n'
  | m+1 => exact Nat.succ_lt_succ (hf m (Nat.lt_of_succ_lt_succ hm))

/-- Renaming preserves well-formedness, provided `f` maps indices below `n` to indices below
`n'`. -/
theorem TypeWf.rename (f : Nat → Nat) (n n' : Nat) (A : Ty)
    (hf : ∀ m, m < n → f m < n') (hA : TypeWf n A) : TypeWf n' (A.rename f) := by
  induction hA generalizing f n' with
  | tVar_wf hlt => exact .tVar_wf (hf _ hlt)
  | int_wf => exact .int_wf
  | bool_wf => exact .bool_wf
  | unit_wf => exact .unit_wf
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA f n' hf) (ihB f n' hf)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA f n' hf) (ihB f n' hf)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA f n' hf) (ihB f n' hf)
  | all_wf _ ih => exact .all_wf (ih _ (n' + 1) (lift_rename_lt hf))
  | exist_wf _ ih => exact .exist_wf (ih _ (n' + 1) (lift_rename_lt hf))

/-- Lifting a substitution under a binder keeps it well-formed: it sends indices below `n + 1` to
types well-formed at `n' + 1`. -/
private theorem lift_substTy_wf {σ : Nat → Ty} {n n' : Nat}
    (hσ : ∀ m, m < n → TypeWf n' (σ m)) :
    ∀ m, m < n + 1 →
      TypeWf (n' + 1) (match m with | 0 => .tVar 0 | m+1 => (σ m).rename (· + 1)) := by
  intro m hm
  match m with
  | 0 => exact .tVar_wf (Nat.zero_lt_succ n')
  | m+1 =>
    refine TypeWf.rename (· + 1) n' (n' + 1) (σ m) (fun j hj => Nat.succ_lt_succ hj) ?_
    exact hσ m (Nat.lt_of_succ_lt_succ hm)

/-- Substitution preserves well-formedness, provided `σ` sends indices below `n` to types that are
well-formed at `n'`. -/
theorem TypeWf.substTy (σ : Nat → Ty) (n n' : Nat) (A : Ty)
    (hσ : ∀ m, m < n → TypeWf n' (σ m)) (hA : TypeWf n A) : TypeWf n' (A.substTy σ) := by
  induction hA generalizing σ n' with
  | tVar_wf hlt => exact hσ _ hlt
  | int_wf => exact .int_wf
  | bool_wf => exact .bool_wf
  | unit_wf => exact .unit_wf
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | all_wf _ ih => exact .all_wf (ih _ (n' + 1) (lift_substTy_wf hσ))
  | exist_wf _ ih => exact .exist_wf (ih _ (n' + 1) (lift_substTy_wf hσ))

/-- Single substitution preserves well-formedness: in `A.subst1 B`, the body `A` is well-formed at
`m + 1` and the replacement `B` at `m`. -/
theorem TypeWf.subst1 (A B : Ty) (m : Nat) (hA : TypeWf (m + 1) A) (hB : TypeWf m B) :
    TypeWf m (A.subst1 B) := by
  unfold Ty.subst1
  refine TypeWf.substTy _ (m + 1) m A (fun n hn => ?_) hA
  match n with
  | 0 => exact hB
  | n+1 => exact .tVar_wf (Nat.lt_of_succ_lt_succ hn)

/-- `TypeWf` is monotone in the number of type variables in scope. -/
theorem TypeWf.mono {A : Ty} {n : Nat} (h : TypeWf n A) (m : Nat) (hle : n ≤ m) : TypeWf m A := by
  induction h generalizing m with
  | tVar_wf hlt => exact .tVar_wf (Nat.lt_of_lt_of_le hlt hle)
  | int_wf => exact .int_wf
  | bool_wf => exact .bool_wf
  | unit_wf => exact .unit_wf
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA m hle) (ihB m hle)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA m hle) (ihB m hle)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA m hle) (ihB m hle)
  | all_wf _ ih => exact .all_wf (ih (m + 1) (Nat.succ_le_succ hle))
  | exist_wf _ ih => exact .exist_wf (ih (m + 1) (Nat.succ_le_succ hle))

/-! ## Typing contexts -/

/-- Finite maps keyed by term-variable names. -/
abbrev TyMapStr (V : Type) := Std.ExtTreeMap String V compare

/-- Assigns types to the term variables in scope. -/
abbrev TypingContext := TyMapStr Ty

/-- Shifts every type in the context up by one type variable. This is applied whenever the typing
rules descend under a type-variable binder (`SynTyped.typed_tLam`, `SynTyped.typed_unpack`): the
context was written outside the binder, so its variable indices must be shifted to remain
meaningful inside it.

Without the shift, `typed_tLam` would let a context type mention the newly bound variable and
`compat_tLam` would be unsound: for `Γ = {x : tVar 0}` and `e = x`, the semantic value relation
for `.all (tVar 0)` demands the body relate at *every* interpretation `τ` of variable `0`, while
the context only supplies the relation at `δ 0`. -/
def shiftCtx (Γ : TypingContext) : TypingContext :=
  Std.ExtTreeMap.map (fun _ A => A.rename (· + 1)) Γ

/-- Looking up a shifted context shifts the type found. -/
theorem shiftCtx_get? (Γ : TypingContext) (x : String) :
    get? (M := TyMapStr) (shiftCtx Γ) x
      = (get? (M := TyMapStr) Γ x).map (fun A => A.rename (· + 1)) := by
  simp [shiftCtx, get?, Std.ExtTreeMap.getElem?_map]

/-- Shifting commutes with extending the context. -/
theorem shiftCtx_insert (Γ : TypingContext) (x : String) (A : Ty) :
    shiftCtx (insert (M := TyMapStr) Γ x A)
      = insert (M := TyMapStr) (shiftCtx Γ) x (A.rename (· + 1)) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  have h₁ := shiftCtx_get? (insert (M := TyMapStr) Γ x A) y
  by_cases hxy : x = y
  · subst hxy
    rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at h₁
    have h₂ : get? (M := TyMapStr)
        (insert (M := TyMapStr) (shiftCtx Γ) x (A.rename (· + 1))) x
        = some (A.rename (· + 1)) := LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl
    simpa [get?] using h₁.trans h₂.symm
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at h₁
    have h₂ : get? (M := TyMapStr)
        (insert (M := TyMapStr) (shiftCtx Γ) x (A.rename (· + 1))) y
        = get? (M := TyMapStr) (shiftCtx Γ) y :=
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy
    rw [shiftCtx_get?] at h₂
    simpa [get?] using h₁.trans h₂.symm

/-- Shifting preserves which variables are bound. -/
theorem shiftCtx_get?_ne_none (Γ : TypingContext) (x : String) :
    get? (M := TyMapStr) (shiftCtx Γ) x ≠ none ↔ get? (M := TyMapStr) Γ x ≠ none := by
  rw [shiftCtx_get?]
  cases get? (M := TyMapStr) Γ x <;> simp

/-! ## Typing judgment -/

/-- `UnOpTyped op A B` says `op` sends an argument of type `A` to a result of type `B`. -/
inductive UnOpTyped : UnOp → Ty → Ty → Prop where
  | neg_typed : UnOpTyped .negOp .bool .bool
  | minus_typed : UnOpTyped .minusUnOp .int .int

/-- `BinOpTyped op A B C` says `op` sends arguments of types `A` and `B` to a result of type
`C`. -/
inductive BinOpTyped : BinOp → Ty → Ty → Ty → Prop where
  | plus_typed : BinOpTyped .plusOp .int .int .int
  | minus_typed : BinOpTyped .minusOp .int .int .int
  | mult_typed : BinOpTyped .multOp .int .int .int
  | lt_typed : BinOpTyped .ltOp .int .int .bool
  | le_typed : BinOpTyped .leOp .int .int .bool
  | eq_typed : BinOpTyped .eqOp .int .int .bool

/-- `SynTyped n Γ e A` is the syntactic typing judgment: `e` has type `A` with `n` type
variables in scope and term variables typed by `Γ`. -/
inductive SynTyped : Nat → TypingContext → Expr → Ty → Prop where
  | typed_lit_int n Γ (z : Int) :
      SynTyped n Γ (.lit (.litInt z)) .int
  | typed_lit_bool n Γ (b : Bool) :
      SynTyped n Γ (.lit (.litBool b)) .bool
  | typed_lit_unit n Γ :
      SynTyped n Γ (.lit .litUnit) .unit
  | typed_var n Γ (x : String) A :
      get? (M := TyMapStr) Γ x = some A →
      SynTyped n Γ (.var x) A
  | typed_lam n Γ (x : String) e A B :
      TypeWf n A →
      SynTyped n (insert (M := TyMapStr) Γ x A) e B →
      SynTyped n Γ (.lam (.bNamed x) e) (.fn A B)
  | typed_lam_anon n Γ e A B :
      TypeWf n A →
      SynTyped n Γ e B →
      SynTyped n Γ (.lam .bAnon e) (.fn A B)
  | typed_app n Γ e₁ e₂ A B :
      SynTyped n Γ e₁ (.fn A B) →
      SynTyped n Γ e₂ A →
      SynTyped n Γ (.app e₁ e₂) B
  | typed_tLam n Γ e A :
      -- The context is shifted as we descend under the type variable binder.
      SynTyped (n + 1) (shiftCtx Γ) e A →
      SynTyped n Γ (.tLam e) (.all A)
  | typed_tApp n Γ e A B :
      TypeWf n B →
      SynTyped n Γ e (.all A) →
      SynTyped n Γ (.tApp e) (A.subst1 B)
  | typed_pack n Γ e A B :
      TypeWf n B →
      TypeWf (n + 1) A →
      SynTyped n Γ e (A.subst1 B) →
      SynTyped n Γ (.pack e) (.exist A)
  | typed_unpack n Γ (x : String) e₁ e₂ A B :
      TypeWf n B →
      SynTyped n Γ e₁ (.exist A) →
      -- `Γ` and the result type `B` are shifted; `A` already lives under this binder.
      SynTyped (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x A) e₂
        (B.rename (· + 1)) →
      SynTyped n Γ (.unpack (.bNamed x) e₁ e₂) B
  | typed_pair n Γ e₁ e₂ A B :
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ B →
      SynTyped n Γ (.pair e₁ e₂) (.prod A B)
  | typed_fst n Γ e A B :
      SynTyped n Γ e (.prod A B) →
      SynTyped n Γ (.fst e) A
  | typed_snd n Γ e A B :
      SynTyped n Γ e (.prod A B) →
      SynTyped n Γ (.snd e) B
  | typed_injL n Γ e A B :
      TypeWf n B →
      SynTyped n Γ e A →
      SynTyped n Γ (.injL e) (.sum A B)
  | typed_injR n Γ e A B :
      TypeWf n A →
      SynTyped n Γ e B →
      SynTyped n Γ (.injR e) (.sum A B)
  | typed_case n Γ e e₁ e₂ A B C :
      SynTyped n Γ e (.sum A B) →
      SynTyped n Γ e₁ (.fn A C) →
      SynTyped n Γ e₂ (.fn B C) →
      SynTyped n Γ (.case e e₁ e₂) C
  | typed_unOp n Γ op e A B :
      UnOpTyped op A B →
      SynTyped n Γ e A →
      SynTyped n Γ (.unOp op e) B
  | typed_binOp n Γ op e₁ e₂ A B C :
      BinOpTyped op A B C →
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ B →
      SynTyped n Γ (.binOp op e₁ e₂) C
  | typed_if n Γ e₀ e₁ e₂ A :
      SynTyped n Γ e₀ .bool →
      SynTyped n Γ e₁ A →
      SynTyped n Γ e₂ A →
      SynTyped n Γ (.ite e₀ e₁ e₂) A
end SystemF
