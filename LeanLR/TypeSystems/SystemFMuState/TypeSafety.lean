import LeanLR.TypeSystems.SystemFMuState.Lang
import LeanLR.TypeSystems.SystemFMuState.Execution
import LeanLR.TypeSystems.SystemFMuState.ParallelSubst

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# System F + μ + state: syntactic type safety

`systemf_mu_state/types.v`, the state chapter's *second* type system: unlike
`SystemFMuState/Types.lean`, `ref A` is unrestricted and the judgment carries a heap context `Θ`
typing every allocated location, so `typed_loc` can type a location and preservation can extend
`Θ`. It therefore lives in `SystemFMuState.Syn`, alongside the logical relation's type language.
-/

open Iris.Std

namespace SystemFMuState.Syn

/-! ## Types -/

/-- Types, with type variables as De Bruijn indices. Unlike the logical relation's type language,
`ref` holds an arbitrary type. -/
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
  | mu (A : Ty)
  | ref (A : Ty)
  deriving Repr, DecidableEq

/-- `TypeWf n A` says every type variable of `A` is bound: free indices are below `n`. -/
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
  | .mu A => .mu (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
  | .ref A => .ref (A.rename f)

/-- Applies the type substitution `σ`, lifting `σ` under each binder. -/
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
  | .mu A => .mu (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
  | .ref A => .ref (A.substTy σ)

/-- `A.subst1 B` is `A[0 := B]`. -/
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

/-- Substitution only depends on the substitution function pointwise. -/
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

/-- Renaming composes: renaming by `g` and then by `f` is renaming by `f ∘ g`. -/
theorem Ty.rename_rename (A : Ty) (f g : Nat → Nat) :
    (A.rename g).rename f = A.rename (fun n => f (g n)) := by
  induction A generalizing f g with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB => simp only [Ty.rename, ihA, ihB]
  | ref _ ih => simp only [Ty.rename, ih]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, ih]
    exact congrArg _ (Ty.rename_ext _ _ _ fun n => by cases n <;> rfl)

/-- Renaming followed by substitution fuses into a single substitution. -/
theorem Ty.rename_substTy (A : Ty) (σ : Nat → Ty) (g : Nat → Nat) :
    (A.rename g).substTy σ = A.substTy (fun n => σ (g n)) := by
  induction A generalizing σ g with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | ref _ ih => simp only [Ty.rename, Ty.substTy, ih]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ fun n => by cases n <;> rfl)

/-- Substitution followed by renaming pushes the renaming into the substitution. -/
theorem Ty.substTy_rename (A : Ty) (σ : Nat → Ty) (f : Nat → Nat) :
    (A.substTy σ).rename f = A.substTy (fun n => (σ n).rename f) := by
  induction A generalizing σ f with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | ref _ ih => simp only [Ty.rename, Ty.substTy, ih]
  | all _ ih | exist _ ih | mu _ ih =>
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
  | ref _ ih => simp only [Ty.substTy, ih]
  | all _ ih | exist _ ih | mu _ ih =>
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
  | ref _ ih => simp only [Ty.substTy, ih]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ (Ty.up_substTy_comm σ τ))

/-- Unrolling a substituted recursive type is the same as substituting into the unrolling. This is
the general-`σ` analogue of `Ty.subst1_mu_rename_comm`, needed for the `mu` case of the semantic
substitution lemma. -/
theorem Ty.subst1_mu_substTy_comm (A : Ty) (σ : Nat → Ty) :
    Ty.subst1 (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))
      (.mu (A.substTy (fun n => match n with | 0 => .tVar 0 | n+1 => (σ n).rename (· + 1)))) =
    (Ty.subst1 A (.mu A)).substTy σ := by
  unfold Ty.subst1
  rw [Ty.substTy_substTy, Ty.substTy_substTy]
  refine Ty.substTy_ext _ _ _ fun n => ?_
  cases n with
  | zero => rfl
  | succ m =>
    show ((σ m).rename (· + 1)).substTy _ = (Ty.tVar m).substTy σ
    rw [Ty.rename_substTy]
    exact Ty.substTy_id (σ m)

/-- Unrolling a renamed recursive type is the same as renaming the unrolling. The renaming on the
left is the lifting of `f` under the `mu` binder (`0 ↦ 0`, `n+1 ↦ f n + 1`). -/
theorem Ty.subst1_mu_rename_comm (A : Ty) (f : Nat → Nat) :
    Ty.subst1 (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))
      (.mu (A.rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1))) =
    (Ty.subst1 A (.mu A)).rename f := by
  unfold Ty.subst1
  rw [Ty.rename_substTy, Ty.substTy_rename]
  refine Ty.substTy_ext _ _ _ fun n => ?_
  cases n <;> rfl

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
  | ref_wf _ ih => exact .ref_wf (ih f n' hf)
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA f n' hf) (ihB f n' hf)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA f n' hf) (ihB f n' hf)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA f n' hf) (ihB f n' hf)
  | all_wf _ ih => exact .all_wf (ih _ (n' + 1) (lift_rename_lt hf))
  | exist_wf _ ih => exact .exist_wf (ih _ (n' + 1) (lift_rename_lt hf))
  | mu_wf _ ih => exact .mu_wf (ih _ (n' + 1) (lift_rename_lt hf))

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
  | ref_wf _ ih => exact .ref_wf (ih σ n' hσ)
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA σ n' hσ) (ihB σ n' hσ)
  | all_wf _ ih => exact .all_wf (ih _ (n' + 1) (lift_substTy_wf hσ))
  | exist_wf _ ih => exact .exist_wf (ih _ (n' + 1) (lift_substTy_wf hσ))
  | mu_wf _ ih => exact .mu_wf (ih _ (n' + 1) (lift_substTy_wf hσ))

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
  | ref_wf _ ih => exact .ref_wf (ih m hle)
  | fn_wf _ _ ihA ihB => exact .fn_wf (ihA m hle) (ihB m hle)
  | prod_wf _ _ ihA ihB => exact .prod_wf (ihA m hle) (ihB m hle)
  | sum_wf _ _ ihA ihB => exact .sum_wf (ihA m hle) (ihB m hle)
  | all_wf _ ih => exact .all_wf (ih (m + 1) (Nat.succ_le_succ hle))
  | exist_wf _ ih => exact .exist_wf (ih (m + 1) (Nat.succ_le_succ hle))
  | mu_wf _ ih => exact .mu_wf (ih (m + 1) (Nat.succ_le_succ hle))

/-- Unrolling a recursive type preserves well-formedness. -/
theorem TypeWf.subst1_mu (A : Ty) (m : Nat) (hwf : TypeWf m (.mu A)) :
    TypeWf m (Ty.subst1 A (.mu A)) :=
  match hwf with
  | .mu_wf h => TypeWf.subst1 A (.mu A) m h hwf

/-! ## Typing contexts -/

/-- Finite maps keyed by term-variable names. -/
abbrev TyMapStr (V : Type) := Std.ExtTreeMap String V compare

/-- Assigns types to the term variables in scope. -/
abbrev TypingContext := TyMapStr Ty

/-- Shifts every type in the context up by one type variable. -/
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

/-- Applies a type substitution to every type in the context; -/
def substCtx (σ : Nat → Ty) (Γ : TypingContext) : TypingContext :=
  Std.ExtTreeMap.map (fun _ A => A.substTy σ) Γ

theorem substCtx_get? (σ : Nat → Ty) (Γ : TypingContext) (x : String) :
    get? (M := TyMapStr) (substCtx σ Γ) x
      = (get? (M := TyMapStr) Γ x).map (fun A => A.substTy σ) := by
  simp [substCtx, get?, Std.ExtTreeMap.getElem?_map]

theorem substCtx_insert (σ : Nat → Ty) (Γ : TypingContext) (x : String) (A : Ty) :
    substCtx σ (insert (M := TyMapStr) Γ x A)
      = insert (M := TyMapStr) (substCtx σ Γ) x (A.substTy σ) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  have h₁ := substCtx_get? σ (insert (M := TyMapStr) Γ x A) y
  by_cases hxy : x = y
  · subst hxy
    rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at h₁
    have h₂ : get? (M := TyMapStr)
        (insert (M := TyMapStr) (substCtx σ Γ) x (A.substTy σ)) x
        = some (A.substTy σ) := LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl
    simpa [get?] using h₁.trans h₂.symm
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at h₁
    have h₂ : get? (M := TyMapStr)
        (insert (M := TyMapStr) (substCtx σ Γ) x (A.substTy σ)) y
        = get? (M := TyMapStr) (substCtx σ Γ) y :=
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy
    rw [substCtx_get?] at h₂
    simpa [get?] using h₁.trans h₂.symm

theorem substCtx_empty (σ : Nat → Ty) :
    substCtx σ (PartialMap.empty (M := TyMapStr) (V := Ty))
      = PartialMap.empty (M := TyMapStr) (V := Ty) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  have h₁ := substCtx_get? σ (PartialMap.empty (M := TyMapStr) (V := Ty)) y
  rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) y] at h₁
  have h₂ : get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none :=
    LawfulPartialMap.get?_empty (M := TyMapStr) y
  simpa [get?] using h₁.trans h₂.symm

theorem shiftCtx_empty :
    shiftCtx (PartialMap.empty (M := TyMapStr) (V := Ty))
      = PartialMap.empty (M := TyMapStr) (V := Ty) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  have h₁ := shiftCtx_get? (PartialMap.empty (M := TyMapStr) (V := Ty)) y
  rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) y] at h₁
  have h₂ : get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none :=
    LawfulPartialMap.get?_empty (M := TyMapStr) y
  simpa [get?] using h₁.trans h₂.symm

/-! ## Heap contexts

Heaps here are total functions `Loc → Option Val`, so heap contexts are too and all their
operations are pointwise. -/

/-- Assigns a type to every allocated location. -/
def HeapContext := Loc → Option Ty

/-- The empty heap context. -/
def HeapContext.empty : HeapContext := fun _ => none

/-- Records the type of one more location. -/
def HeapContext.insert (Θ : HeapContext) (l : Loc) (A : Ty) : HeapContext :=
  fun l' => if l' = l then some A else Θ l'

@[simp] theorem HeapContext.insert_eq (Θ : HeapContext) (l : Loc) (A : Ty) :
    Θ.insert l A l = some A := by simp [HeapContext.insert]

theorem HeapContext.insert_ne (Θ : HeapContext) {l l' : Loc} (A : Ty) (h : l' ≠ l) :
    Θ.insert l A l' = Θ l' := by simp [HeapContext.insert, h]

/-- Inclusion of heap contexts, pointwise. -/
def HeapSubseteq (Θ Θ' : HeapContext) : Prop := ∀ l A, Θ l = some A → Θ' l = some A

@[inherit_doc] scoped infix:50 " ⊑ₕ " => HeapSubseteq

theorem HeapSubseteq.refl (Θ : HeapContext) : Θ ⊑ₕ Θ := fun _ _ h => h

theorem HeapSubseteq.trans {Θ Θ' Θ'' : HeapContext} (h₁ : Θ ⊑ₕ Θ') (h₂ : Θ' ⊑ₕ Θ'') :
    Θ ⊑ₕ Θ'' := fun l A h => h₂ l A (h₁ l A h)

def shiftHeapCtx (Θ : HeapContext) : HeapContext := fun l => (Θ l).map (Ty.rename (· + 1))

def substHeapCtx (σ : Nat → Ty) (Θ : HeapContext) : HeapContext :=
  fun l => (Θ l).map (Ty.substTy σ)

/-! ## Typing judgment -/

/-- `UnOpTyped op A B` says `op` sends an argument of type `A` to a result of type `B`. -/
inductive UnOpTyped : UnOp → Ty → Ty → Prop where
  | neg_typed : UnOpTyped .negOp .bool .bool
  | minus_typed : UnOpTyped .minusUnOp .int .int

/-- `BinOpTyped op A B C` says `op` sends arguments of types `A` and `B` to a result of type `C`. -/
inductive BinOpTyped : BinOp → Ty → Ty → Ty → Prop where
  | plus_typed : BinOpTyped .plusOp .int .int .int
  | minus_typed : BinOpTyped .minusOp .int .int .int
  | mult_typed : BinOpTyped .multOp .int .int .int
  | lt_typed : BinOpTyped .ltOp .int .int .bool
  | le_typed : BinOpTyped .leOp .int .int .bool
  | eq_typed : BinOpTyped .eqOp .int .int .bool

/-- `SynTyped Θ n Γ e A` is Rocq's `TY Θ; n; Γ ⊢ e : A`. The heap context `Θ` is an index rather
than a parameter, since `typed_tLam` and `typed_unpack` shift it; it is left implicit in the
constructors, where it is always determined by the conclusion. -/
inductive SynTyped : HeapContext → Nat → TypingContext → Expr → Ty → Prop where
  | typed_lit_int {Θ} n Γ (z : Int) :
      SynTyped Θ n Γ (.lit (.litInt z)) .int
  | typed_lit_bool {Θ} n Γ (b : Bool) :
      SynTyped Θ n Γ (.lit (.litBool b)) .bool
  | typed_lit_unit {Θ} n Γ :
      SynTyped Θ n Γ (.lit .litUnit) .unit
  | typed_var {Θ} n Γ (x : String) A :
      get? (M := TyMapStr) Γ x = some A →
      SynTyped Θ n Γ (.var x) A
  | typed_lam {Θ} n Γ (x : String) e A B :
      TypeWf n A →
      SynTyped Θ n (insert (M := TyMapStr) Γ x A) e B →
      SynTyped Θ n Γ (.lam (.bNamed x) e) (.fn A B)
  | typed_lam_anon {Θ} n Γ e A B :
      TypeWf n A →
      SynTyped Θ n Γ e B →
      SynTyped Θ n Γ (.lam .bAnon e) (.fn A B)
  | typed_app {Θ} n Γ e₁ e₂ A B :
      SynTyped Θ n Γ e₁ (.fn A B) →
      SynTyped Θ n Γ e₂ A →
      SynTyped Θ n Γ (.app e₁ e₂) B
  | typed_tLam {Θ} n Γ e A :
      SynTyped (shiftHeapCtx Θ) (n + 1) (shiftCtx Γ) e A →
      SynTyped Θ n Γ (.tLam e) (.all A)
  | typed_tApp {Θ} n Γ e A B :
      TypeWf n B →
      SynTyped Θ n Γ e (.all A) →
      SynTyped Θ n Γ (.tApp e) (A.subst1 B)
  | typed_pack {Θ} n Γ e A B :
      TypeWf n B →
      TypeWf (n + 1) A →
      SynTyped Θ n Γ e (A.subst1 B) →
      SynTyped Θ n Γ (.pack e) (.exist A)
  | typed_unpack {Θ} n Γ (x : String) e₁ e₂ A B :
      TypeWf n B →
      SynTyped Θ n Γ e₁ (.exist A) →
      SynTyped (shiftHeapCtx Θ) (n + 1)
        (insert (M := TyMapStr) (shiftCtx Γ) x A) e₂ (B.rename (· + 1)) →
      SynTyped Θ n Γ (.unpack (.bNamed x) e₁ e₂) B
  | typed_pair {Θ} n Γ e₁ e₂ A B :
      SynTyped Θ n Γ e₁ A →
      SynTyped Θ n Γ e₂ B →
      SynTyped Θ n Γ (.pair e₁ e₂) (.prod A B)
  | typed_fst {Θ} n Γ e A B :
      SynTyped Θ n Γ e (.prod A B) →
      SynTyped Θ n Γ (.fst e) A
  | typed_snd {Θ} n Γ e A B :
      SynTyped Θ n Γ e (.prod A B) →
      SynTyped Θ n Γ (.snd e) B
  | typed_injL {Θ} n Γ e A B :
      TypeWf n B →
      SynTyped Θ n Γ e A →
      SynTyped Θ n Γ (.injL e) (.sum A B)
  | typed_injR {Θ} n Γ e A B :
      TypeWf n A →
      SynTyped Θ n Γ e B →
      SynTyped Θ n Γ (.injR e) (.sum A B)
  | typed_case {Θ} n Γ e e₁ e₂ A B C :
      SynTyped Θ n Γ e (.sum A B) →
      SynTyped Θ n Γ e₁ (.fn A C) →
      SynTyped Θ n Γ e₂ (.fn B C) →
      SynTyped Θ n Γ (.case e e₁ e₂) C
  | typed_unOp {Θ} n Γ op e A B :
      UnOpTyped op A B →
      SynTyped Θ n Γ e A →
      SynTyped Θ n Γ (.unOp op e) B
  | typed_binOp {Θ} n Γ op e₁ e₂ A B C :
      BinOpTyped op A B C →
      SynTyped Θ n Γ e₁ A →
      SynTyped Θ n Γ e₂ B →
      SynTyped Θ n Γ (.binOp op e₁ e₂) C
  | typed_if {Θ} n Γ e₀ e₁ e₂ A :
      SynTyped Θ n Γ e₀ .bool →
      SynTyped Θ n Γ e₁ A →
      SynTyped Θ n Γ e₂ A →
      SynTyped Θ n Γ (.ite e₀ e₁ e₂) A
  | typed_roll {Θ} n Γ e A :
      SynTyped Θ n Γ e (Ty.subst1 A (.mu A)) →
      SynTyped Θ n Γ (.roll e) (.mu A)
  | typed_unroll {Θ} n Γ e A :
      SynTyped Θ n Γ e (.mu A) →
      SynTyped Θ n Γ (.unroll e) (Ty.subst1 A (.mu A))
  | typed_loc {Θ} n Γ (l : Loc) A :
      Θ l = some A →
      SynTyped Θ n Γ (.lit (.litLoc l)) (.ref A)
  | typed_load {Θ} n Γ e A :
      SynTyped Θ n Γ e (.ref A) →
      SynTyped Θ n Γ (.load e) A
  | typed_store {Θ} n Γ e₁ e₂ A :
      SynTyped Θ n Γ e₁ (.ref A) →
      SynTyped Θ n Γ e₂ A →
      SynTyped Θ n Γ (.store e₁ e₂) .unit
  | typed_new {Θ} n Γ e A :
      SynTyped Θ n Γ e A →
      SynTyped Θ n Γ (.new e) (.ref A)

/-! ## Contexts

Inclusion is pointwise; the two context maps needed — `shiftCtx` and `substCtx` — are direct. -/

/-- Context inclusion: `Δ` types every variable `Γ` types, at the same type. -/
def CtxSubseteq (Γ Δ : TypingContext) : Prop :=
  ∀ x A, get? (M := TyMapStr) Γ x = some A → get? (M := TyMapStr) Δ x = some A

@[inherit_doc] scoped infix:50 " ⊑ " => CtxSubseteq

theorem CtxSubseteq.refl (Γ : TypingContext) : Γ ⊑ Γ := fun _ _ h => h

theorem CtxSubseteq.trans {Γ Δ Ξ : TypingContext} (h₁ : Γ ⊑ Δ) (h₂ : Δ ⊑ Ξ) : Γ ⊑ Ξ :=
  fun x A h => h₂ x A (h₁ x A h)

/-- The empty context is included in every context. -/
theorem CtxSubseteq.empty_le (Γ : TypingContext) :
    PartialMap.empty (M := TyMapStr) (V := Ty) ⊑ Γ := by
  intro x A h
  rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) x] at h
  exact absurd h (by simp)

/-- Inclusion is preserved by extending both contexts at the same variable. Rocq's
`insert_mono`. -/
theorem CtxSubseteq.insert_mono {Γ Δ : TypingContext} (x : String) (A : Ty) (h : Γ ⊑ Δ) :
    insert (M := TyMapStr) Γ x A ⊑ insert (M := TyMapStr) Δ x A := by
  intro y B hy
  by_cases hxy : x = y
  · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy] at hy ⊢
    exact hy
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hy ⊢
    exact h y B hy

/-- Inclusion is preserved by shifting. -/
theorem renaming_inclusion {Γ Δ : TypingContext} (h : Γ ⊑ Δ) : shiftCtx Γ ⊑ shiftCtx Δ := by
  intro x A hx
  rw [shiftCtx_get?] at hx ⊢
  cases hget : get? (M := TyMapStr) Γ x with
  | none => rw [hget] at hx; exact absurd hx (by simp)
  | some B =>
    rw [hget] at hx
    rw [h x B hget]
    exact hx

/-- Applies a type substitution to every type in the context. -/

theorem fmap_up_subst (σ : Nat → Ty) (Γ : TypingContext) :
    shiftCtx (substCtx σ Γ)
      = substCtx (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))
          (shiftCtx Γ) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  show get? (M := TyMapStr) (shiftCtx (substCtx σ Γ)) y
      = get? (M := TyMapStr)
          (substCtx (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))
            (shiftCtx Γ)) y
  rw [shiftCtx_get?, substCtx_get?, substCtx_get?, shiftCtx_get?]
  cases hget : get? (M := TyMapStr) Γ y with
  | none => rfl
  | some A =>
    simp only [Option.map_some, Ty.substTy_rename, Ty.rename_substTy]

/-! ## `free_vars` and `bounded` -/

/-- The free type variables of a type, as a predicate on indices. -/
def Ty.freeVars : Ty → Nat → Prop
  | .tVar n => fun m => m = n
  | .int | .bool | .unit => fun _ => False
  | .fn A B => fun n => A.freeVars n ∨ B.freeVars n
  | .prod A B => fun n => A.freeVars n ∨ B.freeVars n
  | .sum A B => fun n => A.freeVars n ∨ B.freeVars n
  | .all A => fun n => A.freeVars (n + 1)
  | .exist A => fun n => A.freeVars (n + 1)
  | .mu A => fun n => A.freeVars (n + 1)
  | .ref A => fun n => A.freeVars n

/-- A type is `bounded n` when all its free variables are below `n`. -/
def Ty.bounded (n : Nat) (A : Ty) : Prop := ∀ x, A.freeVars x → x < n

/-- Well-formedness is exactly boundedness. -/
theorem type_wf_bounded (n : Nat) (A : Ty) : TypeWf n A ↔ Ty.bounded n A := by
  constructor
  · intro h
    induction h with
    | tVar_wf hlt =>
      intro x hx
      simp only [Ty.freeVars] at hx
      subst hx
      exact hlt
    | int_wf | bool_wf | unit_wf => intro x hx; exact hx.elim
    | ref_wf _ ih => exact ih
    | fn_wf _ _ ihA ihB | prod_wf _ _ ihA ihB | sum_wf _ _ ihA ihB =>
      intro x hx
      rcases hx with hx | hx
      · exact ihA x hx
      · exact ihB x hx
    | all_wf _ ih | exist_wf _ ih | mu_wf _ ih =>
      intro x hx
      have := ih (x + 1) hx
      omega
  · intro h
    induction A generalizing n with
    | tVar m => exact .tVar_wf (h m rfl)
    | int => exact .int_wf
    | bool => exact .bool_wf
    | unit => exact .unit_wf
    | fn A B ihA ihB =>
      exact .fn_wf (ihA n fun x hx => h x (Or.inl hx)) (ihB n fun x hx => h x (Or.inr hx))
    | prod A B ihA ihB =>
      exact .prod_wf (ihA n fun x hx => h x (Or.inl hx)) (ihB n fun x hx => h x (Or.inr hx))
    | sum A B ihA ihB =>
      exact .sum_wf (ihA n fun x hx => h x (Or.inl hx)) (ihB n fun x hx => h x (Or.inr hx))
    | ref A ih => exact .ref_wf (ih n h)
    | all A ih =>
      refine .all_wf (ih (n + 1) fun x hx => ?_)
      match x with
      | 0 => omega
      | x+1 => have := h x hx; omega
    | exist A ih =>
      refine .exist_wf (ih (n + 1) fun x hx => ?_)
      match x with
      | 0 => omega
      | x+1 => have := h x hx; omega
    | mu A ih =>
      refine .mu_wf (ih (n + 1) fun x hx => ?_)
      match x with
      | 0 => omega
      | x+1 => have := h x hx; omega

theorem free_vars_rename (A : Ty) (x : Nat) (f : Nat → Nat) (h : A.freeVars x) :
    (A.rename f).freeVars (f x) := by
  induction A generalizing x f with
  | tVar m => simpa [Ty.freeVars, Ty.rename] using congrArg f h
  | int | bool | unit => exact h.elim
  | ref A ih => exact ih x f h
  | fn A B ihA ihB | prod A B ihA ihB | sum A B ihA ihB =>
    rcases h with h | h
    · exact Or.inl (ihA x f h)
    · exact Or.inr (ihB x f h)
  | all A ih | exist A ih | mu A ih =>
    exact ih (x + 1) _ h

/-- If a substituted type is bounded, then the substitution is bounded
at every free variable of the original. -/
theorem free_vars_subst (x n : Nat) (A : Ty) (σ : Nat → Ty)
    (hbd : Ty.bounded n (A.substTy σ)) (hfree : A.freeVars x) : Ty.bounded n (σ x) := by
  induction A generalizing x n σ with
  | tVar m =>
    simp only [Ty.freeVars] at hfree
    subst hfree
    exact hbd
  | int | bool | unit => exact hfree.elim
  | ref A ih => exact ih x n σ hbd hfree
  | fn A B ihA ihB | prod A B ihA ihB | sum A B ihA ihB =>
    rcases hfree with hfree | hfree
    · exact ihA x n σ (fun y hy => hbd y (Or.inl hy)) hfree
    · exact ihB x n σ (fun y hy => hbd y (Or.inr hy)) hfree
  | all A ih | exist A ih | mu A ih =>
    have hbd' : Ty.bounded (n + 1)
        (A.substTy (fun k => match k with | 0 => Ty.tVar 0 | k+1 => (σ k).rename (· + 1))) := by
      intro z hz
      match z with
      | 0 => omega
      | z+1 => have := hbd z hz; omega
    have := ih (x + 1) (n + 1) _ hbd' hfree
    intro y hy
    have h' := this (y + 1) (free_vars_rename (σ x) y (· + 1) hy)
    omega

/-- The converse of `TypeWf.subst1_mu`. -/
theorem type_wf_rec_type (n : Nat) (A : Ty) (h : TypeWf n (Ty.subst1 A (.mu A))) :
    TypeWf (n + 1) A := by
  rw [type_wf_bounded] at h ⊢
  intro x hfree
  have hb := free_vars_subst x n A _ h hfree
  match x with
  | 0 => omega
  | x+1 =>
    have := hb x (by simp [Ty.freeVars])
    omega

/-! ## Well-formed contexts -/

/-- Every type in the context is well-formed. -/
def CtxWf (n : Nat) (Γ : TypingContext) : Prop :=
  ∀ x A, get? (M := TyMapStr) Γ x = some A → TypeWf n A

theorem ctx_wf_empty (n : Nat) : CtxWf n (PartialMap.empty (M := TyMapStr) (V := Ty)) := by
  intro x A h
  rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) x] at h
  exact absurd h (by simp)

theorem ctx_wf_insert (n : Nat) (Γ : TypingContext) (x : String) (A : Ty)
    (hΓ : CtxWf n Γ) (hA : TypeWf n A) : CtxWf n (insert (M := TyMapStr) Γ x A) := by
  intro y B hy
  by_cases hxy : x = y
  · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy] at hy
    injection hy with hy
    exact hy ▸ hA
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hy
    exact hΓ y B hy

/-- Shifting a well-formed context makes it well-formed one level up. -/
theorem ctx_wf_up (n : Nat) (Γ : TypingContext) (hΓ : CtxWf n Γ) : CtxWf (n + 1) (shiftCtx Γ) := by
  intro x A hx
  rw [shiftCtx_get?] at hx
  cases hget : get? (M := TyMapStr) Γ x with
  | none => rw [hget] at hx; exact absurd hx (by simp)
  | some B =>
    rw [hget] at hx
    injection hx with hx
    subst hx
    exact TypeWf.rename (· + 1) n (n + 1) B (fun m hm => Nat.succ_lt_succ hm) (hΓ x B hget)

/-! ## Well-formed heap contexts -/

def HeapCtxWf (n : Nat) (Θ : HeapContext) : Prop := ∀ l A, Θ l = some A → TypeWf n A

theorem heap_ctx_wf_empty (n : Nat) : HeapCtxWf n HeapContext.empty := by
  intro l A h
  exact absurd h (by simp [HeapContext.empty])

theorem heap_ctx_wf_insert (n : Nat) (Θ : HeapContext) (l : Loc) (A : Ty)
    (hΘ : HeapCtxWf n Θ) (hA : TypeWf n A) : HeapCtxWf n (Θ.insert l A) := by
  intro l' B hl'
  by_cases hll : l' = l
  · rw [hll, HeapContext.insert_eq] at hl'
    injection hl' with hl'
    exact hl' ▸ hA
  · rw [HeapContext.insert_ne Θ A hll] at hl'
    exact hΘ l' B hl'

theorem heap_ctx_wf_up (n : Nat) (Θ : HeapContext) (hΘ : HeapCtxWf n Θ) :
    HeapCtxWf (n + 1) (shiftHeapCtx Θ) := by
  intro l A hl
  simp only [shiftHeapCtx] at hl
  cases hget : Θ l with
  | none => rw [hget] at hl; exact absurd hl (by simp)
  | some B =>
    rw [hget] at hl
    injection hl with hl
    subst hl
    exact TypeWf.rename (· + 1) n (n + 1) B (fun m hm => Nat.succ_lt_succ hm) (hΘ l B hget)

theorem renaming_heap_ctx_inclusion {Θ Θ' : HeapContext} (h : Θ ⊑ₕ Θ') :
    shiftHeapCtx Θ ⊑ₕ shiftHeapCtx Θ' := by
  intro l A hl
  simp only [shiftHeapCtx] at hl ⊢
  cases hget : Θ l with
  | none => rw [hget] at hl; exact absurd hl (by simp)
  | some B => rw [hget] at hl; rw [h l B hget]; exact hl

theorem fmap_up_subst_heap_ctx (σ : Nat → Ty) (Θ : HeapContext) :
    shiftHeapCtx (substHeapCtx σ Θ)
      = substHeapCtx (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))
          (shiftHeapCtx Θ) := by
  funext l
  simp only [shiftHeapCtx, substHeapCtx, Option.map_map]
  cases Θ l with
  | none => rfl
  | some A => simp only [Option.map_some, Function.comp, Ty.substTy_rename, Ty.rename_substTy]

/-! ## Weakening -/

theorem typed_weakening {Θ Θ' : HeapContext} {n m : Nat} {Γ Δ : TypingContext} {e : Expr}
    {A : Ty} (ht : SynTyped Θ n Γ e A) (hsub : Γ ⊑ Δ) (hle : n ≤ m) (hΘ : Θ ⊑ₕ Θ') :
    SynTyped Θ' m Δ e A := by
  induction ht generalizing Δ m Θ' with
  | typed_lit_int n Γ z => exact .typed_lit_int m Δ z
  | typed_lit_bool n Γ b => exact .typed_lit_bool m Δ b
  | typed_lit_unit n Γ => exact .typed_lit_unit m Δ
  | typed_var n Γ x A hx => exact .typed_var m Δ x A (hsub x A hx)
  | typed_lam n Γ x e A B hA _ ih =>
    exact .typed_lam m Δ x e A B (hA.mono m hle) (ih (hsub.insert_mono x A) hle hΘ)
  | typed_lam_anon n Γ e A B hA _ ih =>
    exact .typed_lam_anon m Δ e A B (hA.mono m hle) (ih hsub hle hΘ)
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_app m Δ e₁ e₂ A B (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_tLam n Γ e A _ ih =>
    exact .typed_tLam m Δ e A
      (ih (renaming_inclusion hsub) (Nat.succ_le_succ hle) (renaming_heap_ctx_inclusion hΘ))
  | typed_tApp n Γ e A B hB _ ih =>
    exact .typed_tApp m Δ e A B (hB.mono m hle) (ih hsub hle hΘ)
  | typed_pack n Γ e A B hB hA _ ih =>
    exact .typed_pack m Δ e A B (hB.mono m hle) (hA.mono (m + 1) (Nat.succ_le_succ hle))
      (ih hsub hle hΘ)
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ ih₁ ih₂ =>
    exact .typed_unpack m Δ x e₁ e₂ A B (hB.mono m hle) (ih₁ hsub hle hΘ)
      (ih₂ ((renaming_inclusion hsub).insert_mono x A) (Nat.succ_le_succ hle)
        (renaming_heap_ctx_inclusion hΘ))
  | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_pair m Δ e₁ e₂ A B (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_fst n Γ e A B _ ih => exact .typed_fst m Δ e A B (ih hsub hle hΘ)
  | typed_snd n Γ e A B _ ih => exact .typed_snd m Δ e A B (ih hsub hle hΘ)
  | typed_injL n Γ e A B hB _ ih => exact .typed_injL m Δ e A B (hB.mono m hle) (ih hsub hle hΘ)
  | typed_injR n Γ e A B hA _ ih => exact .typed_injR m Δ e A B (hA.mono m hle) (ih hsub hle hΘ)
  | typed_case n Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂ =>
    exact .typed_case m Δ e e₁ e₂ A B C (ih hsub hle hΘ) (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_unOp n Γ op e A B hop _ ih => exact .typed_unOp m Δ op e A B hop (ih hsub hle hΘ)
  | typed_binOp n Γ op e₁ e₂ A B C hop _ _ ih₁ ih₂ =>
    exact .typed_binOp m Δ op e₁ e₂ A B C hop (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_if n Γ e₀ e₁ e₂ A _ _ _ ih₀ ih₁ ih₂ =>
    exact .typed_if m Δ e₀ e₁ e₂ A (ih₀ hsub hle hΘ) (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_roll n Γ e A _ ih => exact .typed_roll m Δ e A (ih hsub hle hΘ)
  | typed_unroll n Γ e A _ ih => exact .typed_unroll m Δ e A (ih hsub hle hΘ)
  | typed_loc n Γ l A hl => exact .typed_loc m Δ l A (hΘ l A hl)
  | typed_load n Γ e A _ ih => exact .typed_load m Δ e A (ih hsub hle hΘ)
  | typed_store n Γ e₁ e₂ A _ _ ih₁ ih₂ =>
    exact .typed_store m Δ e₁ e₂ A (ih₁ hsub hle hΘ) (ih₂ hsub hle hΘ)
  | typed_new n Γ e A _ ih => exact .typed_new m Δ e A (ih hsub hle hΘ)

/-! ## Well-formedness of the typed type -/

theorem syn_typed_wf {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ n Γ e A) : CtxWf n Γ → HeapCtxWf n Θ → TypeWf n A := by
  induction ht with
  | typed_lit_int _ _ _ => intro _ _; exact .int_wf
  | typed_lit_bool _ _ _ => intro _ _; exact .bool_wf
  | typed_lit_unit _ _ => intro _ _; exact .unit_wf
  | typed_var n Γ x A hx => intro hΓ _; exact hΓ x A hx
  | typed_lam n Γ x e A B hA _ ih =>
    intro hΓ hΘ; exact .fn_wf hA (ih (ctx_wf_insert n Γ x A hΓ hA) hΘ)
  | typed_lam_anon n Γ e A B hA _ ih => intro hΓ hΘ; exact .fn_wf hA (ih hΓ hΘ)
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ _ =>
    intro hΓ hΘ
    match ih₁ hΓ hΘ with
    | .fn_wf _ hB => exact hB
  | typed_tLam n Γ e A _ ih =>
    intro hΓ hΘ; exact .all_wf (ih (ctx_wf_up n Γ hΓ) (heap_ctx_wf_up n _ hΘ))
  | typed_tApp n Γ e A B hB _ ih =>
    intro hΓ hΘ
    match ih hΓ hΘ with
    | .all_wf hA => exact TypeWf.subst1 A B n hA hB
  | typed_pack n Γ e A B _ hA _ _ => intro _ _; exact .exist_wf hA
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ _ _ => intro _ _; exact hB
  | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    intro hΓ hΘ; exact .prod_wf (ih₁ hΓ hΘ) (ih₂ hΓ hΘ)
  | typed_fst n Γ e A B _ ih =>
    intro hΓ hΘ
    match ih hΓ hΘ with
    | .prod_wf hA _ => exact hA
  | typed_snd n Γ e A B _ ih =>
    intro hΓ hΘ
    match ih hΓ hΘ with
    | .prod_wf _ hB => exact hB
  | typed_injL n Γ e A B hB _ ih => intro hΓ hΘ; exact .sum_wf (ih hΓ hΘ) hB
  | typed_injR n Γ e A B hA _ ih => intro hΓ hΘ; exact .sum_wf hA (ih hΓ hΘ)
  | typed_case n Γ e e₁ e₂ A B C _ _ _ _ ih₁ _ =>
    intro hΓ hΘ
    match ih₁ hΓ hΘ with
    | .fn_wf _ hA => exact hA
  | typed_unOp n Γ op e A B hop _ _ =>
    intro _ _; cases hop <;> first | exact .bool_wf | exact .int_wf
  | typed_binOp n Γ op e₁ e₂ A B C hop _ _ _ _ =>
    intro _ _; cases hop <;> first | exact .int_wf | exact .bool_wf
  | typed_if n Γ e₀ e₁ e₂ A _ _ _ _ ih₁ _ => intro hΓ hΘ; exact ih₁ hΓ hΘ
  | typed_roll n Γ e A _ ih => intro hΓ hΘ; exact .mu_wf (type_wf_rec_type n A (ih hΓ hΘ))
  | typed_unroll n Γ e A _ ih =>
    intro hΓ hΘ
    match ih hΓ hΘ with
    | .mu_wf hA => exact TypeWf.subst1 A (.mu A) n hA (.mu_wf hA)
  | typed_loc n Γ l A hl => intro _ hΘ; exact .ref_wf (hΘ l A hl)
  | typed_load n Γ e A _ ih =>
    intro hΓ hΘ
    match ih hΓ hΘ with
    | .ref_wf hA => exact hA
  | typed_store n Γ e₁ e₂ A _ _ _ _ => intro _ _; exact .unit_wf
  | typed_new n Γ e A _ ih => intro hΓ hΘ; exact .ref_wf (ih hΓ hΘ)

/-! ## Type substitution is insensitive outside the scope -/

theorem type_wf_subst_dom {σ τ : Nat → Ty} {n : Nat} {A : Ty} (hA : TypeWf n A)
    (h : ∀ m, m < n → σ m = τ m) : A.substTy σ = A.substTy τ := by
  induction hA generalizing σ τ with
  | tVar_wf hlt => exact h _ hlt
  | int_wf | bool_wf | unit_wf => rfl
  | ref_wf _ ih => simp only [Ty.substTy, ih h]
  | fn_wf _ _ ihA ihB | prod_wf _ _ ihA ihB | sum_wf _ _ ihA ihB =>
    simp only [Ty.substTy, ihA h, ihB h]
  | all_wf _ ih | exist_wf _ ih | mu_wf _ ih =>
    refine congrArg _ (ih fun m hm => ?_)
    match m with
    | 0 => rfl
    | m+1 => exact congrArg (Ty.rename (· + 1)) (h m (Nat.lt_of_succ_lt_succ hm))

/-- Renaming is the substitution built from variables. -/
theorem Ty.rename_eq_substTy (A : Ty) (f : Nat → Nat) :
    A.rename f = A.substTy (fun n => .tVar (f n)) := by
  induction A generalizing f with
  | tVar _ | int | bool | unit => rfl
  | ref _ ih => simp only [Ty.rename, Ty.substTy, ih]
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih | mu _ ih =>
    simp only [Ty.rename, Ty.substTy, ih]
    exact congrArg _ (Ty.substTy_ext _ _ _ fun n => by cases n <;> rfl)

/-- A closed type is unaffected by substitution. -/
theorem type_wf_closed (A : Ty) (σ : Nat → Ty) (h : TypeWf 0 A) : A.substTy σ = A := by
  rw [type_wf_subst_dom (σ := σ) (τ := fun n => .tVar n) h (fun m hm => absurd hm (by omega))]
  exact Ty.substTy_id A

/-- A closed type is unaffected by renaming. -/
theorem type_wf_closed_rename (A : Ty) (f : Nat → Nat) (h : TypeWf 0 A) : A.rename f = A := by
  rw [Ty.rename_eq_substTy]
  exact type_wf_closed A _ h

/-- A heap context of closed types is unaffected by substitution. -/
theorem heap_ctx_closed (Θ : HeapContext) (σ : Nat → Ty) (hΘ : HeapCtxWf 0 Θ) :
    substHeapCtx σ Θ = Θ := by
  funext l
  simp only [substHeapCtx]
  cases hget : Θ l with
  | none => rfl
  | some A => simp only [Option.map_some, type_wf_closed A σ (hΘ l A hget)]

/-- A heap context of closed types is unaffected by shifting. -/
theorem heap_ctx_closed_shift (Θ : HeapContext) (hΘ : HeapCtxWf 0 Θ) : shiftHeapCtx Θ = Θ := by
  funext l
  simp only [shiftHeapCtx]
  cases hget : Θ l with
  | none => rfl
  | some A => simp only [Option.map_some, type_wf_closed_rename A (· + 1) (hΘ l A hget)]

/-! ## Typed expressions are closed -/

theorem syn_typed_closed {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    {X : List String} (ht : SynTyped Θ n Γ e A)
    (hX : ∀ x, get? (M := TyMapStr) Γ x ≠ none → x ∈ X) : closed X e := by
  induction ht generalizing X with
  | typed_lit_int _ _ _ | typed_lit_bool _ _ _ | typed_lit_unit _ _ | typed_loc _ _ _ _ _ =>
    rfl
  | typed_var n Γ x A hx =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq]
    exact hX x (by rw [hx]; simp)
  | typed_lam n Γ x e A B hA _ ih =>
    refine ih fun y hy => ?_
    by_cases hxy : x = y
    · exact hxy ▸ List.Mem.head _
    · refine List.Mem.tail _ (hX y ?_)
      rwa [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hy
  | typed_lam_anon n Γ e A B hA _ ih => exact ih hX
  | typed_tLam n Γ e A _ ih =>
    exact ih fun y hy => hX y ((shiftCtx_get?_ne_none Γ y).mp hy)
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    refine ⟨ih₁ hX, ih₂ fun y hy => ?_⟩
    by_cases hxy : x = y
    · exact hxy ▸ List.Mem.head _
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hy
      exact List.Mem.tail _ (hX y ((shiftCtx_get?_ne_none Γ y).mp hy))
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ ih₂ | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂
  | typed_store n Γ e₁ e₂ A _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ hX, ih₂ hX⟩
  | typed_binOp n Γ op e₁ e₂ A B C _ _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ hX, ih₂ hX⟩
  | typed_tApp n Γ e A B _ _ ih | typed_pack n Γ e A B _ _ _ ih
  | typed_fst n Γ e A B _ ih | typed_snd n Γ e A B _ ih
  | typed_injL n Γ e A B _ _ ih | typed_injR n Γ e A B _ _ ih
  | typed_unOp n Γ op e A B _ _ ih
  | typed_load n Γ e A _ ih | typed_new n Γ e A _ ih
  | typed_roll n Γ e A _ ih | typed_unroll n Γ e A _ ih => exact ih hX
  | typed_case n Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂
  | typed_if n Γ e A e₁ e₂ _ _ _ ih ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨⟨ih hX, ih₁ hX⟩, ih₂ hX⟩

/-! ## Derived typing rules -/

/-- The typing rule for the `match` sugar. -/
theorem typed_match {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e e₁ e₂ : Expr}
    {x₁ x₂ : String} {A B C : Ty} (hB : TypeWf n B) (hC : TypeWf n C)
    (ht : SynTyped Θ n Γ e (.sum B C))
    (h₁ : SynTyped Θ n (insert (M := TyMapStr) Γ x₁ B) e₁ A)
    (h₂ : SynTyped Θ n (insert (M := TyMapStr) Γ x₂ C) e₂ A) :
    SynTyped Θ n Γ (.case e (.lam (.bNamed x₁) e₁) (.lam (.bNamed x₂) e₂)) A :=
  .typed_case n Γ e _ _ B C A ht (.typed_lam n Γ x₁ e₁ B A hB h₁)
    (.typed_lam n Γ x₂ e₂ C A hC h₂)

theorem typed_unroll' {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped Θ n Γ e (.mu A)) (heq : B = Ty.subst1 A (.mu A)) :
    SynTyped Θ n Γ (.unroll e) B :=
  heq ▸ .typed_unroll n Γ e A ht

theorem typed_tapp' {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A B C : Ty}
    (ht : SynTyped Θ n Γ e (.all A)) (hB : TypeWf n B) (heq : C = A.subst1 B) :
    SynTyped Θ n Γ (.tApp e) C :=
  heq ▸ .typed_tApp n Γ e A B hB ht

/-! ## Map algebra for typing contexts -/

private theorem ctx_ext {Γ Δ : TypingContext}
    (h : ∀ k, get? (M := TyMapStr) Γ k = get? (M := TyMapStr) Δ k) : Γ = Δ :=
  LawfulPartialMap.equiv_iff_eq.mp h

/-- A later insertion at the same variable wins. -/
theorem insert_insert_eq (Γ : TypingContext) (x : String) (A B : Ty) :
    insert (M := TyMapStr) (insert (M := TyMapStr) Γ x A) x B = insert (M := TyMapStr) Γ x B := by
  refine ctx_ext fun k => ?_
  by_cases hxk : x = k
  · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxk,
      LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxk]
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk,
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk,
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk]

/-- Insertions at distinct variables commute. -/
theorem insert_comm (Γ : TypingContext) {x y : String} (hxy : x ≠ y) (A B : Ty) :
    insert (M := TyMapStr) (insert (M := TyMapStr) Γ x A) y B
      = insert (M := TyMapStr) (insert (M := TyMapStr) Γ y B) x A := by
  refine ctx_ext fun k => ?_
  by_cases hyk : y = k
  · subst hyk
    rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl,
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy,
      LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl]
  · by_cases hxk : x = k
    · subst hxk
      rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hyk,
        LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl,
        LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl]
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hyk,
        LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk,
        LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk,
        LawfulPartialMap.get?_insert_ne (M := TyMapStr) hyk]

/-! ## Typing inversion

Every inversion generalises the type before `cases`, since the rules whose conclusion type is a
substitution (`typed_tApp`, `typed_unroll`) would otherwise block dependent elimination. -/

theorem var_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {x : String} {A : Ty}
    (h : SynTyped Θ n Γ (.var x) A) : get? (M := TyMapStr) Γ x = some A := by
  cases h
  assumption

theorem lam_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {x : String} {e : Expr}
    {C : Ty}
    (h : SynTyped Θ n Γ (.lam (.bNamed x) e) C) :
    ∃ A B, C = .fn A B ∧ TypeWf n A ∧ SynTyped Θ n (insert (M := TyMapStr) Γ x A) e B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem lam_anon_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped Θ n Γ (.lam .bAnon e) C) :
    ∃ A B, C = .fn A B ∧ TypeWf n A ∧ SynTyped Θ n Γ e B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem app_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.app e₁ e₂) B) :
    ∃ A, SynTyped Θ n Γ e₁ (.fn A B) ∧ SynTyped Θ n Γ e₂ A := by
  cases h
  exact ⟨_, by assumption, by assumption⟩

theorem if_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e₀ e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.ite e₀ e₁ e₂) B) :
    SynTyped Θ n Γ e₀ .bool ∧ SynTyped Θ n Γ e₁ B ∧ SynTyped Θ n Γ e₂ B := by
  cases h
  exact ⟨by assumption, by assumption, by assumption⟩

theorem binop_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {op : BinOp}
    {e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.binOp op e₁ e₂) B) :
    ∃ A₁ A₂, BinOpTyped op A₁ A₂ B ∧ SynTyped Θ n Γ e₁ A₁ ∧ SynTyped Θ n Γ e₂ A₂ := by
  cases h
  exact ⟨_, _, by assumption, by assumption, by assumption⟩

theorem unop_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {op : UnOp} {e : Expr}
    {B : Ty}
    (h : SynTyped Θ n Γ (.unOp op e) B) :
    ∃ A, UnOpTyped op A B ∧ SynTyped Θ n Γ e A := by
  cases h
  exact ⟨_, by assumption, by assumption⟩

theorem type_app_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.tApp e) B) :
    ∃ A C, B = A.subst1 C ∧ TypeWf n C ∧ SynTyped Θ n Γ e (.all A) := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem type_lam_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.tLam e) B) :
    ∃ A, B = .all A ∧ SynTyped (shiftHeapCtx Θ) (n + 1) (shiftCtx Γ) e A := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem type_pack_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.pack e) B) :
    ∃ A C, B = .exist A ∧ SynTyped Θ n Γ e (A.subst1 C) ∧ TypeWf n C ∧ TypeWf (n + 1) A := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption, by assumption⟩

theorem type_unpack_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {b : Binder}
    {e e' : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.unpack b e e') B) :
    ∃ A x', b = .bNamed x' ∧ TypeWf n B ∧ SynTyped Θ n Γ e (.exist A) ∧
      SynTyped (shiftHeapCtx Θ) (n + 1)
        (insert (M := TyMapStr) (shiftCtx Γ) x' A) e' (B.rename (· + 1)) := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption, by assumption⟩

theorem pair_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {C : Ty}
    (h : SynTyped Θ n Γ (.pair e₁ e₂) C) :
    ∃ A B, C = .prod A B ∧ SynTyped Θ n Γ e₁ A ∧ SynTyped Θ n Γ e₂ B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem fst_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (h : SynTyped Θ n Γ (.fst e) A) : ∃ B, SynTyped Θ n Γ e (.prod A B) := by
  cases h
  exact ⟨_, by assumption⟩

theorem snd_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.snd e) B) : ∃ A, SynTyped Θ n Γ e (.prod A B) := by
  cases h
  exact ⟨_, by assumption⟩

theorem injl_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped Θ n Γ (.injL e) C) :
    ∃ A B, C = .sum A B ∧ SynTyped Θ n Γ e A ∧ TypeWf n B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem injr_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped Θ n Γ (.injR e) C) :
    ∃ A B, C = .sum A B ∧ SynTyped Θ n Γ e B ∧ TypeWf n A := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem case_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e e₁ e₂ : Expr} {A : Ty}
    (h : SynTyped Θ n Γ (.case e e₁ e₂) A) :
    ∃ B C, SynTyped Θ n Γ e (.sum B C) ∧ SynTyped Θ n Γ e₁ (.fn B A) ∧
      SynTyped Θ n Γ e₂ (.fn C A) := by
  cases h
  exact ⟨_, _, by assumption, by assumption, by assumption⟩

theorem roll_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.roll e) B) :
    ∃ A, B = .mu A ∧ SynTyped Θ n Γ e (Ty.subst1 A (.mu A)) := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem unroll_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.unroll e) B) :
    ∃ A, B = Ty.subst1 A (.mu A) ∧ SynTyped Θ n Γ e (.mu A) := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem loc_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {l : Loc} {B : Ty}
    (h : SynTyped Θ n Γ (.lit (.litLoc l)) B) : ∃ A, B = .ref A ∧ Θ l = some A := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem new_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.new e) B) : ∃ A, B = .ref A ∧ SynTyped Θ n Γ e A := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem load_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.load e) B) : SynTyped Θ n Γ e (.ref B) := by
  cases h
  assumption

theorem store_inversion {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped Θ n Γ (.store e₁ e₂) B) :
    ∃ A, B = .unit ∧ SynTyped Θ n Γ e₁ (.ref A) ∧ SynTyped Θ n Γ e₂ A := by
  cases h
  exact ⟨_, rfl, by assumption, by assumption⟩

/-! ## Canonical values -/

theorem canonical_values_arr {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped Θ n Γ e (.fn A B)) (hv : Expr.isVal e) :
    ∃ (x : Binder) (e' : Expr), e = .lam x e' := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .fn A B →
      ∃ (x : Binder) (e' : Expr), e = .lam x e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, _, rfl⟩

theorem canonical_values_forall {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ n Γ e (.all A)) (hv : Expr.isVal e) : ∃ e', e = .tLam e' := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .all A → ∃ e', e = .tLam e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_exists {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ n Γ e (.exist A)) (hv : Expr.isVal e) : ∃ e', e = .pack e' := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .exist A → ∃ e', e = .pack e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_int {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped Θ n Γ e .int) (hv : Expr.isVal e) : ∃ z : Int, e = .lit (.litInt z) := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .int → ∃ z : Int, e = .lit (.litInt z) by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_bool {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped Θ n Γ e .bool) (hv : Expr.isVal e) : ∃ b : Bool, e = .lit (.litBool b) := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .bool → ∃ b : Bool, e = .lit (.litBool b) by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_unit {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped Θ n Γ e .unit) (hv : Expr.isVal e) : e = .lit .litUnit := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .unit → e = .lit .litUnit by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | rfl

theorem canonical_values_prod {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped Θ n Γ e (.prod A B)) (hv : Expr.isVal e) :
    ∃ e₁ e₂, e = .pair e₁ e₂ ∧ Expr.isVal e₁ ∧ Expr.isVal e₂ := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .prod A B →
      ∃ e₁ e₂, e = .pair e₁ e₂ ∧ Expr.isVal e₁ ∧ Expr.isVal e₂ by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, _, rfl, hv.1, hv.2⟩

theorem canonical_values_sum {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped Θ n Γ e (.sum A B)) (hv : Expr.isVal e) :
    (∃ e', e = .injL e' ∧ Expr.isVal e') ∨ (∃ e', e = .injR e' ∧ Expr.isVal e') := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .sum A B →
      (∃ e', e = .injL e' ∧ Expr.isVal e') ∨ (∃ e', e = .injR e' ∧ Expr.isVal e') by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact Or.inl ⟨_, rfl, hv⟩
      | exact Or.inr ⟨_, rfl, hv⟩

theorem canonical_values_rec {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ n Γ e (.mu A)) (hv : Expr.isVal e) :
    ∃ e', e = .roll e' ∧ Expr.isVal e' := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .mu A →
      ∃ e', e = .roll e' ∧ Expr.isVal e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl, hv⟩

theorem canonical_values_ref {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ n Γ e (.ref A)) (hv : Expr.isVal e) :
    ∃ l : Loc, e = .lit (.litLoc l) ∧ Θ l = some A := by
  suffices h : ∀ T : Ty, SynTyped Θ n Γ e T → T = .ref A →
      ∃ l : Loc, e = .lit (.litLoc l) ∧ Θ l = some A by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | (injection hT with hT; subst hT; exact ⟨_, rfl, by assumption⟩)

/-! ## Substitutivity for term variables -/

theorem typed_substitutivity {Θ : HeapContext} {n : Nat} {Γ : TypingContext} {e e' : Expr}
    {x : String} {A B : Ty} (hΘwf : HeapCtxWf 0 Θ)
    (he' : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A)
    (ht : SynTyped Θ n (insert (M := TyMapStr) Γ x A) e B) :
    SynTyped Θ n Γ (subst x e' e) B := by
  have hAwf : TypeWf 0 A := syn_typed_wf he' (ctx_wf_empty 0) hΘwf
  suffices h : ∀ (e : Expr) (n : Nat) (Γ : TypingContext) (B : Ty),
      SynTyped Θ n (insert (M := TyMapStr) Γ x A) e B → SynTyped Θ n Γ (subst x e' e) B by
    exact h e n Γ B ht
  clear ht
  intro e
  induction e with
  | lit l =>
    intro n Γ B ht
    simp only [subst]
    cases ht <;>
      solve
        | exact .typed_lit_int _ _ _
        | exact .typed_lit_bool _ _ _
        | exact .typed_lit_unit _ _
        | exact .typed_loc _ _ _ _ (by assumption)
  | var y =>
    intro n Γ B ht
    have hlook := var_inversion ht
    simp only [subst]
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at hlook
      injection hlook with hlook
      subst hlook
      rw [if_pos rfl]
      exact typed_weakening he' (CtxSubseteq.empty_le Γ) (Nat.zero_le n) (HeapSubseteq.refl Θ)
    · rw [if_neg hxy]
      rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hlook
      exact .typed_var n Γ y B hlook
  | lam b e ih =>
    intro n Γ B ht
    cases b with
    | bAnon =>
      obtain ⟨A', C, rfl, hwf, hty⟩ := lam_anon_inversion ht
      simp only [subst, if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))]
      exact .typed_lam_anon n Γ _ A' C hwf (ih n Γ C hty)
    | bNamed y =>
      obtain ⟨A', C, rfl, hwf, hty⟩ := lam_inversion ht
      simp only [subst]
      by_cases hxy : x = y
      · subst hxy
        rw [insert_insert_eq] at hty
        rw [if_pos rfl]
        exact .typed_lam n Γ x e A' C hwf hty
      · rw [if_neg (fun h => hxy (by cases h; rfl))]
        rw [insert_comm Γ hxy A A'] at hty
        exact .typed_lam n Γ y _ A' C hwf (ih n (insert (M := TyMapStr) Γ y A') C hty)
  | app e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion ht
    simp only [subst]
    exact .typed_app n Γ _ _ A₁ B (ih₁ n Γ _ ht₁) (ih₂ n Γ A₁ ht₂)
  | unOp op e ih =>
    intro n Γ B ht
    obtain ⟨A₁, hop, ht₁⟩ := unop_inversion ht
    simp only [subst]
    exact .typed_unOp n Γ op _ A₁ B hop (ih n Γ A₁ ht₁)
  | binOp op e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₁, A₂, hop, ht₁, ht₂⟩ := binop_inversion ht
    simp only [subst]
    exact .typed_binOp n Γ op _ _ A₁ A₂ B hop (ih₁ n Γ A₁ ht₁) (ih₂ n Γ A₂ ht₂)
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨ht₀, ht₁, ht₂⟩ := if_inversion ht
    simp only [subst]
    exact .typed_if n Γ _ _ _ B (ih₀ n Γ .bool ht₀) (ih₁ n Γ B ht₁) (ih₂ n Γ B ht₂)
  | tApp e ih =>
    intro n Γ B ht
    obtain ⟨A₂, C, rfl, hwf, hty⟩ := type_app_inversion ht
    simp only [subst]
    exact .typed_tApp n Γ _ A₂ C hwf (ih n Γ (.all A₂) hty)
  | tLam e ih =>
    intro n Γ B ht
    obtain ⟨A₂, rfl, hty⟩ := type_lam_inversion ht
    rw [heap_ctx_closed_shift Θ hΘwf, shiftCtx_insert,
      type_wf_closed_rename A (· + 1) hAwf] at hty
    simp only [subst]
    refine .typed_tLam n Γ _ A₂ ?_
    rw [heap_ctx_closed_shift Θ hΘwf]
    exact ih (n + 1) (shiftCtx Γ) A₂ hty
  | pack e ih =>
    intro n Γ B ht
    obtain ⟨A₂, C, rfl, hty, hwfC, hwfA⟩ := type_pack_inversion ht
    simp only [subst]
    exact .typed_pack n Γ _ A₂ C hwfC hwfA (ih n Γ (A₂.subst1 C) hty)
  | unpack b e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₂, x', rfl, hwfB, hty₁, hty₂⟩ := type_unpack_inversion ht
    rw [heap_ctx_closed_shift Θ hΘwf, shiftCtx_insert,
      type_wf_closed_rename A (· + 1) hAwf] at hty₂
    simp only [subst]
    by_cases hxy : x = x'
    · subst hxy
      rw [insert_insert_eq] at hty₂
      rw [if_pos rfl]
      refine .typed_unpack n Γ x _ e₂ A₂ B hwfB (ih₁ n Γ (.exist A₂) hty₁) ?_
      rw [heap_ctx_closed_shift Θ hΘwf]
      exact hty₂
    · rw [if_neg (fun h => hxy (by cases h; rfl))]
      rw [insert_comm _ hxy A A₂] at hty₂
      refine .typed_unpack n Γ x' _ _ A₂ B hwfB (ih₁ n Γ (.exist A₂) hty₁) ?_
      rw [heap_ctx_closed_shift Θ hΘwf]
      exact ih₂ (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x' A₂) (B.rename (· + 1)) hty₂
  | pair e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₁, A₂, rfl, ht₁, ht₂⟩ := pair_inversion ht
    simp only [subst]
    exact .typed_pair n Γ _ _ A₁ A₂ (ih₁ n Γ A₁ ht₁) (ih₂ n Γ A₂ ht₂)
  | fst e ih =>
    intro n Γ B ht
    obtain ⟨A₂, hty⟩ := fst_inversion ht
    simp only [subst]
    exact .typed_fst n Γ _ B A₂ (ih n Γ (.prod B A₂) hty)
  | snd e ih =>
    intro n Γ B ht
    obtain ⟨A₁, hty⟩ := snd_inversion ht
    simp only [subst]
    exact .typed_snd n Γ _ A₁ B (ih n Γ (.prod A₁ B) hty)
  | injL e ih =>
    intro n Γ B ht
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injl_inversion ht
    simp only [subst]
    exact .typed_injL n Γ _ A₁ A₂ hwf (ih n Γ A₁ hty)
  | injR e ih =>
    intro n Γ B ht
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injr_inversion ht
    simp only [subst]
    exact .typed_injR n Γ _ A₁ A₂ hwf (ih n Γ A₂ hty)
  | case e e₁ e₂ ih ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion ht
    simp only [subst]
    exact .typed_case n Γ _ _ _ A₁ A₂ B (ih n Γ (.sum A₁ A₂) hty)
      (ih₁ n Γ (.fn A₁ B) hty₁) (ih₂ n Γ (.fn A₂ B) hty₂)
  | roll e ih =>
    intro n Γ B ht
    obtain ⟨A₂, rfl, hty⟩ := roll_inversion ht
    simp only [subst]
    exact .typed_roll n Γ _ A₂ (ih n Γ (Ty.subst1 A₂ (.mu A₂)) hty)
  | unroll e ih =>
    intro n Γ B ht
    obtain ⟨A₂, rfl, hty⟩ := unroll_inversion ht
    simp only [subst]
    exact .typed_unroll n Γ _ A₂ (ih n Γ (.mu A₂) hty)

  | load e ih =>
    intro n Γ B ht
    have hty := load_inversion ht
    simp only [subst]
    exact .typed_load n Γ _ B (ih n Γ (.ref B) hty)
  | store e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₁, rfl, ht₁, ht₂⟩ := store_inversion ht
    simp only [subst]
    exact .typed_store n Γ _ _ A₁ (ih₁ n Γ (.ref A₁) ht₁) (ih₂ n Γ A₁ ht₂)
  | new e ih =>
    intro n Γ B ht
    obtain ⟨A₁, rfl, hty⟩ := new_inversion ht
    simp only [subst]
    exact .typed_new n Γ _ A₁ (ih n Γ A₁ hty)

/-! ## Progress -/

/-- Heaps here are total functions rather than finite maps, so finiteness — what guarantees that
`new` can find a fresh location — has to be stated explicitly. -/
def HeapBounded (h : Heap) : Prop := ∃ n : Int, ∀ l : Loc, n ≤ l.loc → h l = none

theorem heapBounded_empty : HeapBounded Heap.empty := ⟨0, fun _ _ => rfl⟩

theorem heapBounded_fresh {h : Heap} (hb : HeapBounded h) : ∃ l, h l = none := by
  obtain ⟨n, hn⟩ := hb
  exact ⟨⟨n⟩, hn ⟨n⟩ (Int.le_refl n)⟩

theorem heapBounded_insert {h : Heap} {l : Loc} {v : Val} (hb : HeapBounded h) :
    HeapBounded (Heap.insert h l v) := by
  obtain ⟨n, hn⟩ := hb
  refine ⟨if n ≤ l.loc then l.loc + 1 else n, fun l' hl' => ?_⟩
  have hne : l' ≠ l := by
    intro heq
    subst heq
    split at hl' <;> omega
  have hbound : n ≤ l'.loc := by split at hl' <;> omega
  simp only [Heap.insert, if_neg hne]
  exact hn l' hbound

/-- Every location the heap context types is allocated, and holds a value of
that type. -/
def HeapType (h : Heap) (Θ : HeapContext) : Prop :=
  ∀ l A, Θ l = some A → ∃ v : Val, h l = some v ∧
    SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) v.toExpr A

/-- One evaluation-context frame of `fill_contextual_step`. -/
private theorem step_frame (Ki : EctxItem) {e e' : Expr} {h h' : Heap}
    (hs : ContextualStep (e, h) (e', h')) :
    ContextualStep (fillItem Ki e, h) (fillItem Ki e', h') :=
  fill_contextual_step (K := [Ki]) hs

theorem typed_progress {Θ : HeapContext} {e : Expr} {A : Ty} {h : Heap}
    (hb : HeapBounded h) (hheap : HeapType h Θ)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) :
    Expr.isVal e ∨ reducible e h := by
  suffices hgen : ∀ (Θ' : HeapContext) (n : Nat) (Γ : TypingContext) (e : Expr) (A : Ty),
      SynTyped Θ' n Γ e A → HeapType h Θ' →
      Γ = PartialMap.empty (M := TyMapStr) (V := Ty) → Expr.isVal e ∨ reducible e h by
    exact hgen Θ 0 _ e A ht hheap rfl
  clear ht hheap
  intro Θ' n Γ e A ht
  induction ht with
  | typed_lit_int _ _ _ | typed_lit_bool _ _ _ | typed_lit_unit _ _ | typed_loc _ _ _ _ _
  | typed_lam _ _ _ _ _ _ _ _ | typed_lam_anon _ _ _ _ _ _ _ | typed_tLam _ _ _ _ _ =>
    intro _ _
    exact Or.inl trivial
  | typed_var n Γ x A hx =>
    intro hheap hΓ
    subst hΓ
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
      LawfulPartialMap.get?_empty (M := TyMapStr) x] at hx
    exact absurd hx (by simp)
  | typed_app n Γ e₁ e₂ A B ht₁ ht₂ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₂ hheap hΓ with hv₂ | hred₂
    · rcases ih₁ hheap hΓ with hv₁ | hred₁
      · obtain ⟨y, body, rfl⟩ := canonical_values_arr (hΓ ▸ ht₁) hv₁
        exact Or.inr ⟨_, _, base_contextual_step (.betaS y body e₂ h hv₂)⟩
      · obtain ⟨v₂, rfl⟩ := isVal_exists hv₂
        obtain ⟨e₁', h', hstep⟩ := hred₁
        exact Or.inr ⟨_, _, step_frame (.appLCtx v₂) hstep⟩
    · obtain ⟨e₂', h', hstep⟩ := hred₂
      exact Or.inr ⟨_, _, step_frame (.appRCtx e₁) hstep⟩
  | typed_tApp n Γ e A B hwf ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨e', rfl⟩ := canonical_values_forall (hΓ ▸ ht') hv
      exact Or.inr ⟨_, _, base_contextual_step (.tBetaS e' h)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .tAppCtx hstep⟩
  | typed_pack n Γ e A B hwfB hwfA ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .packCtx hstep⟩
  | typed_unpack n Γ x e₁ e₂ A B hwfB ht₁ ht₂ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₁ hheap hΓ with hv₁ | hred₁
    · obtain ⟨e'', rfl⟩ := canonical_values_exists (hΓ ▸ ht₁) hv₁
      exact Or.inr ⟨_, _, base_contextual_step (.unpackS (.bNamed x) e'' e₂ h hv₁)⟩
    · obtain ⟨e₁', h', hstep⟩ := hred₁
      exact Or.inr ⟨_, _, step_frame (.unpackCtx (.bNamed x) e₂) hstep⟩
  | typed_if n Γ e₀ e₁ e₂ A ht₀ ht₁ ht₂ ih₀ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₀ hheap hΓ with hv₀ | hred₀
    · obtain ⟨b, rfl⟩ := canonical_values_bool (hΓ ▸ ht₀) hv₀
      cases b
      · exact Or.inr ⟨_, _, base_contextual_step (.ifFalseS e₁ e₂ h)⟩
      · exact Or.inr ⟨_, _, base_contextual_step (.ifTrueS e₁ e₂ h)⟩
    · obtain ⟨e₀', h', hstep⟩ := hred₀
      exact Or.inr ⟨_, _, step_frame (.ifCtx e₁ e₂) hstep⟩
  | typed_binOp n Γ op e₁ e₂ A B C hop ht₁ ht₂ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₂ hheap hΓ with hv₂ | hred₂
    · rcases ih₁ hheap hΓ with hv₁ | hred₁
      · cases hop <;>
          (obtain ⟨z₁, rfl⟩ := canonical_values_int (hΓ ▸ ht₁) hv₁
           obtain ⟨z₂, rfl⟩ := canonical_values_int (hΓ ▸ ht₂) hv₂
           exact Or.inr ⟨_, _, base_contextual_step
             (.binOpS _ _ _ (.litV (.litInt z₁)) (.litV (.litInt z₂)) _ _ rfl rfl rfl)⟩)
      · obtain ⟨v₂, rfl⟩ := isVal_exists hv₂
        obtain ⟨e₁', h', hstep⟩ := hred₁
        exact Or.inr ⟨_, _, step_frame (.binOpLCtx op v₂) hstep⟩
    · obtain ⟨e₂', h', hstep⟩ := hred₂
      exact Or.inr ⟨_, _, step_frame (.binOpRCtx op e₁) hstep⟩
  | typed_unOp n Γ op e A B hop ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · cases hop
      · obtain ⟨b, rfl⟩ := canonical_values_bool (hΓ ▸ ht') hv
        exact Or.inr ⟨_, _, base_contextual_step (.unOpS _ _ (.litV (.litBool b)) _ _ rfl rfl)⟩
      · obtain ⟨z, rfl⟩ := canonical_values_int (hΓ ▸ ht') hv
        exact Or.inr ⟨_, _, base_contextual_step (.unOpS _ _ (.litV (.litInt z)) _ _ rfl rfl)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame (.unOpCtx op) hstep⟩
  | typed_pair n Γ e₁ e₂ A B ht₁ ht₂ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₂ hheap hΓ with hv₂ | hred₂
    · rcases ih₁ hheap hΓ with hv₁ | hred₁
      · exact Or.inl ⟨hv₁, hv₂⟩
      · obtain ⟨v₂, rfl⟩ := isVal_exists hv₂
        obtain ⟨e₁', h', hstep⟩ := hred₁
        exact Or.inr ⟨_, _, step_frame (.pairLCtx v₂) hstep⟩
    · obtain ⟨e₂', h', hstep⟩ := hred₂
      exact Or.inr ⟨_, _, step_frame (.pairRCtx e₁) hstep⟩
  | typed_fst n Γ e A B ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod (hΓ ▸ ht') hv
      exact Or.inr ⟨_, _, base_contextual_step (.fstS e₁ e₂ h hv₁ hv₂)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .fstCtx hstep⟩
  | typed_snd n Γ e A B ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod (hΓ ▸ ht') hv
      exact Or.inr ⟨_, _, base_contextual_step (.sndS e₁ e₂ h hv₁ hv₂)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .sndCtx hstep⟩
  | typed_injL n Γ e A B hwf ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .injLCtx hstep⟩
  | typed_injR n Γ e A B hwf ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .injRCtx hstep⟩
  | typed_case n Γ e e₁ e₂ A B C ht' ht₁ ht₂ ih ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · rcases canonical_values_sum (hΓ ▸ ht') hv with ⟨e'', rfl, hv''⟩ | ⟨e'', rfl, hv''⟩
      · exact Or.inr ⟨_, _, base_contextual_step (.caseLS e'' e₁ e₂ h hv'')⟩
      · exact Or.inr ⟨_, _, base_contextual_step (.caseRS e'' e₁ e₂ h hv'')⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame (.caseCtx e₁ e₂) hstep⟩
  | typed_roll n Γ e A ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .rollCtx hstep⟩
  | typed_unroll n Γ e A ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨e'', rfl, hv''⟩ := canonical_values_rec (hΓ ▸ ht') hv
      exact Or.inr ⟨_, _, base_contextual_step (.unrollS e'' h hv'')⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .unrollCtx hstep⟩
  | typed_load n Γ e A ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨l, rfl, hl⟩ := canonical_values_ref (hΓ ▸ ht') hv
      obtain ⟨v, hlv, _⟩ := hheap l A hl
      exact Or.inr ⟨_, _, base_contextual_step (.loadS l v h hlv)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .loadCtx hstep⟩
  | typed_store n Γ e₁ e₂ A ht₁ ht₂ ih₁ ih₂ =>
    intro hheap hΓ
    rcases ih₂ hheap hΓ with hv₂ | hred₂
    · rcases ih₁ hheap hΓ with hv₁ | hred₁
      · obtain ⟨l, rfl, hl⟩ := canonical_values_ref (hΓ ▸ ht₁) hv₁
        obtain ⟨w, hlw, _⟩ := hheap l A hl
        obtain ⟨v₂, hv₂'⟩ := isVal_spec.mp hv₂
        exact Or.inr ⟨_, _, base_contextual_step
          (.storeS l v₂ e₂ h (by rw [hlw]; simp) hv₂')⟩
      · obtain ⟨v₂, rfl⟩ := isVal_exists hv₂
        obtain ⟨e₁', h', hstep⟩ := hred₁
        exact Or.inr ⟨_, _, step_frame (.storeLCtx v₂) hstep⟩
    · obtain ⟨e₂', h', hstep⟩ := hred₂
      exact Or.inr ⟨_, _, step_frame (.storeRCtx e₁) hstep⟩
  | typed_new n Γ e A ht' ih =>
    intro hheap hΓ
    rcases ih hheap hΓ with hv | hred
    · obtain ⟨v, hv'⟩ := isVal_spec.mp hv
      obtain ⟨l, hl⟩ := heapBounded_fresh hb
      exact Or.inr ⟨_, _, base_contextual_step (.newS e v l h hv' hl)⟩
    · obtain ⟨e', h', hstep⟩ := hred
      exact Or.inr ⟨_, _, step_frame .newCtx hstep⟩

/-! ## Typed evaluation contexts -/

/-- Weakening at the empty context and no type variables, along a heap-context inclusion. -/
private theorem weaken_heap {Θ Θ' : HeapContext} {e : Expr} {A : Ty}
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) (hsub : Θ ⊑ₕ Θ') :
    SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A :=
  typed_weakening ht (CtxSubseteq.refl _) (Nat.le_refl 0) hsub

/-- Frame typing; it quantifies over larger heap contexts, since preservation may allocate while
reducing inside the frame. -/
def EctxItemTyping (Θ : HeapContext) (Ki : EctxItem) (A B : Ty) : Prop :=
  ∀ (e : Expr) (Θ' : HeapContext), Θ ⊑ₕ Θ' →
    SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A →
    SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) B

def EctxTyping (Θ : HeapContext) (K : Ectx) (A B : Ty) : Prop :=
  ∀ (e : Expr) (Θ' : HeapContext), Θ ⊑ₕ Θ' →
    SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A →
    SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) B

theorem ectx_item_typing_weaking {Θ Θ' : HeapContext} {Ki : EctxItem} {A B : Ty}
    (hsub : Θ ⊑ₕ Θ') (hK : EctxItemTyping Θ Ki A B) : EctxItemTyping Θ' Ki A B :=
  fun e Θ'' hsub'' ht => hK e Θ'' (hsub.trans hsub'') ht

theorem ectx_typing_weaking {Θ Θ' : HeapContext} {K : Ectx} {A B : Ty}
    (hsub : Θ ⊑ₕ Θ') (hK : EctxTyping Θ K A B) : EctxTyping Θ' K A B :=
  fun e Θ'' hsub'' ht => hK e Θ'' (hsub.trans hsub'') ht

theorem fill_item_typing_decompose {Θ : HeapContext} {Ki : EctxItem} {e : Expr} {A : Ty}
    (h : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) A) :
    ∃ B, SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B ∧
      EctxItemTyping Θ Ki B A := by
  cases Ki <;> simp only [fillItem] at h
  case appLCtx v =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion h
    exact ⟨.fn A₁ A, ht₁, fun e' Θ' hs h' =>
      .typed_app 0 _ e' _ A₁ A h' (weaken_heap ht₂ hs)⟩
  case appRCtx e₁ =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion h
    exact ⟨A₁, ht₂, fun e' Θ' hs h' =>
      .typed_app 0 _ e₁ e' A₁ A (weaken_heap ht₁ hs) h'⟩
  case unOpCtx op =>
    obtain ⟨A₁, hop, ht⟩ := unop_inversion h
    exact ⟨A₁, ht, fun e' Θ' hs h' => .typed_unOp 0 _ op e' A₁ A hop h'⟩
  case binOpLCtx op v =>
    obtain ⟨A₁, A₂, hop, ht₁, ht₂⟩ := binop_inversion h
    exact ⟨A₁, ht₁, fun e' Θ' hs h' =>
      .typed_binOp 0 _ op e' _ A₁ A₂ A hop h' (weaken_heap ht₂ hs)⟩
  case binOpRCtx op e₁ =>
    obtain ⟨A₁, A₂, hop, ht₁, ht₂⟩ := binop_inversion h
    exact ⟨A₂, ht₂, fun e' Θ' hs h' =>
      .typed_binOp 0 _ op e₁ e' A₁ A₂ A hop (weaken_heap ht₁ hs) h'⟩
  case ifCtx e₁ e₂ =>
    obtain ⟨ht₀, ht₁, ht₂⟩ := if_inversion h
    exact ⟨.bool, ht₀, fun e' Θ' hs h' =>
      .typed_if 0 _ e' e₁ e₂ A h' (weaken_heap ht₁ hs) (weaken_heap ht₂ hs)⟩
  case tAppCtx =>
    obtain ⟨A₂, C, rfl, hwf, hty⟩ := type_app_inversion h
    exact ⟨.all A₂, hty, fun e' Θ' hs h' => .typed_tApp 0 _ e' A₂ C hwf h'⟩
  case packCtx =>
    obtain ⟨A₂, C, rfl, hty, hwfC, hwfA⟩ := type_pack_inversion h
    exact ⟨A₂.subst1 C, hty, fun e' Θ' hs h' => .typed_pack 0 _ e' A₂ C hwfC hwfA h'⟩
  case unpackCtx x e₂ =>
    obtain ⟨A₂, x', rfl, hwfB, hty₁, hty₂⟩ := type_unpack_inversion h
    refine ⟨.exist A₂, hty₁, fun e' Θ' hs h' => .typed_unpack 0 _ x' e' e₂ A₂ A hwfB h' ?_⟩
    exact typed_weakening hty₂ (CtxSubseteq.refl _) (Nat.le_refl 1)
      (renaming_heap_ctx_inclusion hs)
  case pairLCtx v =>
    obtain ⟨A₁, A₂, rfl, ht₁, ht₂⟩ := pair_inversion h
    exact ⟨A₁, ht₁, fun e' Θ' hs h' => .typed_pair 0 _ e' _ A₁ A₂ h' (weaken_heap ht₂ hs)⟩
  case pairRCtx e₁ =>
    obtain ⟨A₁, A₂, rfl, ht₁, ht₂⟩ := pair_inversion h
    exact ⟨A₂, ht₂, fun e' Θ' hs h' => .typed_pair 0 _ e₁ e' A₁ A₂ (weaken_heap ht₁ hs) h'⟩
  case fstCtx =>
    obtain ⟨A₂, hty⟩ := fst_inversion h
    exact ⟨.prod A A₂, hty, fun e' Θ' hs h' => .typed_fst 0 _ e' A A₂ h'⟩
  case sndCtx =>
    obtain ⟨A₁, hty⟩ := snd_inversion h
    exact ⟨.prod A₁ A, hty, fun e' Θ' hs h' => .typed_snd 0 _ e' A₁ A h'⟩
  case injLCtx =>
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injl_inversion h
    exact ⟨A₁, hty, fun e' Θ' hs h' => .typed_injL 0 _ e' A₁ A₂ hwf h'⟩
  case injRCtx =>
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injr_inversion h
    exact ⟨A₂, hty, fun e' Θ' hs h' => .typed_injR 0 _ e' A₁ A₂ hwf h'⟩
  case caseCtx e₁ e₂ =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion h
    exact ⟨.sum A₁ A₂, hty, fun e' Θ' hs h' =>
      .typed_case 0 _ e' e₁ e₂ A₁ A₂ A h' (weaken_heap hty₁ hs) (weaken_heap hty₂ hs)⟩
  case rollCtx =>
    obtain ⟨A₂, rfl, hty⟩ := roll_inversion h
    exact ⟨Ty.subst1 A₂ (.mu A₂), hty, fun e' Θ' hs h' => .typed_roll 0 _ e' A₂ h'⟩
  case unrollCtx =>
    obtain ⟨A₂, rfl, hty⟩ := unroll_inversion h
    exact ⟨.mu A₂, hty, fun e' Θ' hs h' => .typed_unroll 0 _ e' A₂ h'⟩
  case loadCtx =>
    have hty := load_inversion h
    exact ⟨.ref A, hty, fun e' Θ' hs h' => .typed_load 0 _ e' A h'⟩
  case storeLCtx v =>
    obtain ⟨A₁, rfl, ht₁, ht₂⟩ := store_inversion h
    exact ⟨.ref A₁, ht₁, fun e' Θ' hs h' => .typed_store 0 _ e' _ A₁ h' (weaken_heap ht₂ hs)⟩
  case storeRCtx e₁ =>
    obtain ⟨A₁, rfl, ht₁, ht₂⟩ := store_inversion h
    exact ⟨A₁, ht₂, fun e' Θ' hs h' => .typed_store 0 _ e₁ e' A₁ (weaken_heap ht₁ hs) h'⟩
  case newCtx =>
    obtain ⟨A₁, rfl, hty⟩ := new_inversion h
    exact ⟨A₁, hty, fun e' Θ' hs h' => .typed_new 0 _ e' A₁ h'⟩

theorem fill_item_typing_compose {Θ : HeapContext} {Ki : EctxItem} {e : Expr} {A B : Ty}
    (h : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B)
    (hK : EctxItemTyping Θ Ki B A) :
    SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) A :=
  hK e Θ (HeapSubseteq.refl Θ) h

theorem fill_typing_decompose {Θ : HeapContext} {K : Ectx} {e : Expr} {A : Ty}
    (h : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) A) :
    ∃ B, SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B ∧ EctxTyping Θ K B A := by
  induction K generalizing e A with
  | nil => exact ⟨A, h, fun _ _ _ h' => h'⟩
  | cons Ki K ih =>
    rw [fill_cons] at h
    obtain ⟨B, hB, hK⟩ := ih h
    obtain ⟨B', hB', hKi⟩ := fill_item_typing_decompose hB
    refine ⟨B', hB', fun e' Θ' hs h' => ?_⟩
    rw [fill_cons]
    exact hK _ Θ' hs (hKi e' Θ' hs h')

theorem fill_typing_compose {Θ : HeapContext} {K : Ectx} {e : Expr} {A B : Ty}
    (h : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B)
    (hK : EctxTyping Θ K B A) :
    SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) A :=
  hK e Θ (HeapSubseteq.refl Θ) h

/-! ## Substitutivity for type variables -/

/-- Substitution into a single substitution: the general-`σ` form of `Ty.subst1_mu_substTy_comm`. -/
theorem Ty.subst1_substTy_comm (A B : Ty) (σ : Nat → Ty) :
    (A.subst1 B).substTy σ
      = (A.substTy (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))).subst1
          (B.substTy σ) := by
  unfold Ty.subst1
  rw [Ty.substTy_substTy, Ty.substTy_substTy]
  refine Ty.substTy_ext _ _ _ fun k => ?_
  cases k with
  | zero => rfl
  | succ j =>
    show (Ty.tVar j).substTy σ = ((σ j).rename (· + 1)).substTy _
    rw [Ty.rename_substTy]
    exact (Ty.substTy_id (σ j)).symm

/-- Shifting commutes with type substitution. -/
theorem Ty.rename_shift_substTy (B : Ty) (σ : Nat → Ty) :
    (B.rename (· + 1)).substTy (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))
      = (B.substTy σ).rename (· + 1) := by
  rw [Ty.rename_substTy, Ty.substTy_rename]

theorem typed_subst_type {Θ : HeapContext} {n m : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    {σ : Nat → Ty} (ht : SynTyped Θ n Γ e A) (hσ : ∀ k, k < n → TypeWf m (σ k)) :
    SynTyped (substHeapCtx σ Θ) m (substCtx σ Γ) e (A.substTy σ) := by
  induction ht generalizing m σ with
  | typed_lit_int n Γ z => exact .typed_lit_int m _ z
  | typed_lit_bool n Γ b => exact .typed_lit_bool m _ b
  | typed_lit_unit n Γ => exact .typed_lit_unit m _
  | typed_var n Γ x A hx =>
    refine .typed_var m _ x _ ?_
    rw [substCtx_get?, hx]
    rfl
  | typed_lam n Γ x e A B hA _ ih =>
    refine .typed_lam m _ x e (A.substTy σ) (B.substTy σ)
      (TypeWf.substTy σ n m A hσ hA) ?_
    rw [← substCtx_insert]
    exact ih hσ
  | typed_lam_anon n Γ e A B hA _ ih =>
    exact .typed_lam_anon m _ e (A.substTy σ) (B.substTy σ) (TypeWf.substTy σ n m A hσ hA)
      (ih hσ)
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_app m _ e₁ e₂ (A.substTy σ) (B.substTy σ) (ih₁ hσ) (ih₂ hσ)
  | typed_tLam n Γ e A _ ih =>
    refine .typed_tLam m _ e _ ?_
    rw [fmap_up_subst, fmap_up_subst_heap_ctx]
    refine ih (fun k hk => ?_)
    match k with
    | 0 => exact .tVar_wf (Nat.zero_lt_succ m)
    | k+1 =>
      exact TypeWf.rename (· + 1) m (m + 1) (σ k) (fun j hj => Nat.succ_lt_succ hj)
        (hσ k (Nat.lt_of_succ_lt_succ hk))
  | typed_tApp n Γ e A B hB _ ih =>
    rw [Ty.subst1_substTy_comm]
    exact .typed_tApp m _ e _ (B.substTy σ) (TypeWf.substTy σ n m B hσ hB) (ih hσ)
  | typed_pack n Γ e A B hB hA _ ih =>
    refine .typed_pack m _ e _ (B.substTy σ) (TypeWf.substTy σ n m B hσ hB) ?_ ?_
    · refine TypeWf.substTy _ (n + 1) (m + 1) A (fun k hk => ?_) hA
      match k with
      | 0 => exact .tVar_wf (Nat.zero_lt_succ m)
      | k+1 =>
        exact TypeWf.rename (· + 1) m (m + 1) (σ k) (fun j hj => Nat.succ_lt_succ hj)
          (hσ k (Nat.lt_of_succ_lt_succ hk))
    · have h := ih (m := m) (σ := σ) hσ
      rw [Ty.subst1_substTy_comm A B σ] at h
      exact h
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ ih₁ ih₂ =>
    have hup : ∀ k, k < n + 1 →
        TypeWf (m + 1)
          ((fun k => match k with | 0 => Ty.tVar 0 | k+1 => (σ k).rename (· + 1)) k) := by
      intro k hk
      match k with
      | 0 => exact .tVar_wf (Nat.zero_lt_succ m)
      | k+1 =>
        exact TypeWf.rename (· + 1) m (m + 1) (σ k) (fun j hj => Nat.succ_lt_succ hj)
          (hσ k (Nat.lt_of_succ_lt_succ hk))
    refine .typed_unpack m _ x e₁ e₂ _ (B.substTy σ) (TypeWf.substTy σ n m B hσ hB) (ih₁ hσ) ?_
    have h₂ := ih₂ hup
    rw [Ty.rename_shift_substTy, substCtx_insert, ← fmap_up_subst,
      ← fmap_up_subst_heap_ctx] at h₂
    exact h₂
  | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_pair m _ e₁ e₂ (A.substTy σ) (B.substTy σ) (ih₁ hσ) (ih₂ hσ)
  | typed_fst n Γ e A B _ ih => exact .typed_fst m _ e (A.substTy σ) (B.substTy σ) (ih hσ)
  | typed_snd n Γ e A B _ ih => exact .typed_snd m _ e (A.substTy σ) (B.substTy σ) (ih hσ)
  | typed_injL n Γ e A B hB _ ih =>
    exact .typed_injL m _ e (A.substTy σ) (B.substTy σ) (TypeWf.substTy σ n m B hσ hB) (ih hσ)
  | typed_injR n Γ e A B hA _ ih =>
    exact .typed_injR m _ e (A.substTy σ) (B.substTy σ) (TypeWf.substTy σ n m A hσ hA) (ih hσ)
  | typed_case n Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂ =>
    exact .typed_case m _ e e₁ e₂ (A.substTy σ) (B.substTy σ) (C.substTy σ) (ih hσ) (ih₁ hσ)
      (ih₂ hσ)
  | typed_unOp n Γ op e A B hop _ ih =>
    cases hop <;> exact .typed_unOp m _ _ e _ _ (by constructor) (ih hσ)
  | typed_binOp n Γ op e₁ e₂ A B C hop _ _ ih₁ ih₂ =>
    cases hop <;> exact .typed_binOp m _ _ e₁ e₂ _ _ _ (by constructor) (ih₁ hσ) (ih₂ hσ)
  | typed_if n Γ e₀ e₁ e₂ A _ _ _ ih₀ ih₁ ih₂ =>
    exact .typed_if m _ e₀ e₁ e₂ (A.substTy σ) (ih₀ hσ) (ih₁ hσ) (ih₂ hσ)
  | typed_roll n Γ e A _ ih =>
    refine .typed_roll m _ e _ ?_
    rw [Ty.subst1_mu_substTy_comm A σ]
    exact ih hσ
  | typed_unroll n Γ e A _ ih =>
    rw [← Ty.subst1_mu_substTy_comm A σ]
    exact .typed_unroll m _ e _ (ih hσ)
  | typed_loc n Γ l A hl =>
    refine .typed_loc m _ l _ ?_
    simp only [substHeapCtx, hl, Option.map_some]
  | typed_load n Γ e A _ ih => exact .typed_load m _ e (A.substTy σ) (ih hσ)
  | typed_store n Γ e₁ e₂ A _ _ ih₁ ih₂ =>
    exact .typed_store m _ e₁ e₂ (A.substTy σ) (ih₁ hσ) (ih₂ hσ)
  | typed_new n Γ e A _ ih => exact .typed_new m _ e (A.substTy σ) (ih hσ)

theorem typed_subst_type_closed {Θ : HeapContext} (C : Ty) (e : Expr) (A : Ty)
    (hwf : TypeWf 0 C) (hΘ : HeapCtxWf 0 Θ)
    (ht : SynTyped (shiftHeapCtx Θ) 1
      (shiftCtx (PartialMap.empty (M := TyMapStr) (V := Ty))) e A) :
    SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e (A.subst1 C) := by
  rw [heap_ctx_closed_shift Θ hΘ] at ht
  have h := typed_subst_type (σ := fun n => match n with | 0 => C | n+1 => .tVar n) ht
    (fun k hk => by
      match k with
      | 0 => exact hwf
      | k+1 => exact absurd hk (by omega))
  rw [shiftCtx_empty, substCtx_empty, heap_ctx_closed Θ _ hΘ] at h
  exact h

theorem typed_subst_type_closed' {Θ : HeapContext} (x : String) (C B : Ty) (e : Expr) (A : Ty)
    (hA : TypeWf 0 A) (_hC : TypeWf 1 C) (hB : TypeWf 0 B) (hΘ : HeapCtxWf 0 Θ)
    (ht : SynTyped (shiftHeapCtx Θ) 1
      (insert (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x C) e A) :
    SynTyped Θ 0 (insert (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x
      (C.subst1 B)) e A := by
  rw [heap_ctx_closed_shift Θ hΘ] at ht
  have h := typed_subst_type (σ := fun n => match n with | 0 => B | n+1 => .tVar n) ht
    (fun k hk => by
      match k with
      | 0 => exact hB
      | k+1 => exact absurd hk (by omega))
  rw [substCtx_insert, substCtx_empty, type_wf_closed A _ hA, heap_ctx_closed Θ _ hΘ] at h
  exact h

/-! ## Heap typing under allocation and update -/

theorem heap_ctx_insert {h : Heap} {Θ : HeapContext} {l : Loc} (A : Ty)
    (hheap : HeapType h Θ) (hl : h l = none) : Θ ⊑ₕ Θ.insert l A := by
  intro l' B hl'
  by_cases hll : l' = l
  · subst hll
    exfalso
    obtain ⟨v, hv, _⟩ := hheap l' B hl'
    rw [hl] at hv
    exact absurd hv (by simp)
  · rw [HeapContext.insert_ne Θ A hll]
    exact hl'

theorem heap_type_insert {h : Heap} {Θ : HeapContext} {e : Expr} {v : Val} {l : Loc} {B : Ty}
    (hheap : HeapType h Θ) (hl : h l = none)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B)
    (hv : e.toVal? = some v) : HeapType (Heap.insert h l v) (Θ.insert l B) := by
  intro l' A hl'
  by_cases hll : l' = l
  · subst hll
    rw [HeapContext.insert_eq] at hl'
    injection hl' with hl'
    subst hl'
    refine ⟨v, by simp [Heap.insert], ?_⟩
    rw [toVal?_eq hv] at ht
    exact weaken_heap ht (heap_ctx_insert B hheap hl)
  · rw [HeapContext.insert_ne Θ B hll] at hl'
    obtain ⟨w, hw, htw⟩ := hheap l' A hl'
    refine ⟨w, ?_, weaken_heap htw (heap_ctx_insert B hheap hl)⟩
    simp only [Heap.insert, if_neg hll]
    exact hw

theorem heap_type_update {h : Heap} {Θ : HeapContext} {e : Expr} {v : Val} {l : Loc} {B : Ty}
    (hheap : HeapType h Θ) (hl : Θ l = some B)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B)
    (hv : e.toVal? = some v) : HeapType (Heap.insert h l v) Θ := by
  intro l' A hl'
  by_cases hll : l' = l
  · subst hll
    rw [hl] at hl'
    injection hl' with hl'
    subst hl'
    refine ⟨v, by simp [Heap.insert], ?_⟩
    rw [toVal?_eq hv] at ht
    exact ht
  · obtain ⟨w, hw, htw⟩ := hheap l' A hl'
    refine ⟨w, ?_, htw⟩
    simp only [Heap.insert, if_neg hll]
    exact hw

/-- Reduction keeps the heap finite. -/
theorem base_step_heapBounded {e e' : Expr} {h h' : Heap} (hb : HeapBounded h)
    (hstep : BaseStep (e, h) (e', h')) : HeapBounded h' := by
  cases hstep <;> first | exact hb | exact heapBounded_insert hb

theorem contextual_step_heapBounded {e e' : Expr} {h h' : Heap} (hb : HeapBounded h)
    (hstep : ContextualStep (e, h) (e', h')) : HeapBounded h' := by
  obtain ⟨K, ea, eb, rfl, rfl, hbs⟩ := contextual_step_inv hstep
  exact base_step_heapBounded hb hbs

/-! ## Preservation and safety -/

/-- The common shape of every base step that leaves the heap context alone. -/
private theorem keep_ctx {Θ : HeapContext} {h : Heap} {e : Expr} {A : Ty}
    (hΘ : HeapCtxWf 0 Θ) (hheap : HeapType h Θ)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) :
    ∃ Θ', Θ ⊑ₕ Θ' ∧ HeapType h Θ' ∧ HeapCtxWf 0 Θ' ∧
      SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A :=
  ⟨Θ, HeapSubseteq.refl Θ, hheap, hΘ, ht⟩

theorem typed_preservation_base_step {Θ : HeapContext} {e e' : Expr} {A : Ty} {h h' : Heap}
    (hΘ : HeapCtxWf 0 Θ) (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A)
    (hheap : HeapType h Θ) (hstep : BaseStep (e, h) (e', h')) :
    ∃ Θ', Θ ⊑ₕ Θ' ∧ HeapType h' Θ' ∧ HeapCtxWf 0 Θ' ∧
      SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A := by
  cases hstep with
  | betaS y e₁ e₂ _ hv =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion ht
    refine keep_ctx hΘ hheap ?_
    cases y with
    | bAnon =>
      obtain ⟨A', C, heq, hwf, hty⟩ := lam_anon_inversion ht₁
      injection heq with heqA heqC
      subst heqA heqC
      exact hty
    | bNamed y =>
      obtain ⟨A', C, heq, hwf, hty⟩ := lam_inversion ht₁
      injection heq with heqA heqC
      subst heqA heqC
      exact typed_substitutivity hΘ ht₂ hty
  | tBetaS e₀ _ =>
    obtain ⟨A₂, C, rfl, hwf, hty⟩ := type_app_inversion ht
    obtain ⟨A₃, heq, hty'⟩ := type_lam_inversion hty
    injection heq with heq
    subst heq
    exact keep_ctx hΘ hheap (typed_subst_type_closed C _ A₂ hwf hΘ hty')
  | unpackS y e₁ e₂ _ hv =>
    obtain ⟨A₂, x', hb, hwfA, hty₁, hty₂⟩ := type_unpack_inversion ht
    subst hb
    obtain ⟨A₃, C, heq, hty₁', hwfC, hwfA₃⟩ := type_pack_inversion hty₁
    injection heq with heq
    subst heq
    rw [shiftCtx_empty, type_wf_closed_rename A _ hwfA] at hty₂
    exact keep_ctx hΘ hheap (typed_substitutivity hΘ hty₁'
      (typed_subst_type_closed' x' A₂ C e₂ A hwfA hwfA₃ hwfC hΘ hty₂))
  | unOpS op e₀ v v' _ h₁ h₂ =>
    obtain ⟨A₁, hop, hty⟩ := unop_inversion ht
    refine keep_ctx hΘ hheap ?_
    cases hop
    · obtain ⟨b, rfl⟩ := canonical_values_bool hty (toVal?_isVal h₁)
      simp only [Expr.toVal?, Option.some.injEq] at h₁
      subst h₁
      simp only [unOpEval, Option.some.injEq] at h₂
      subst h₂
      exact .typed_lit_bool 0 _ _
    · obtain ⟨z, rfl⟩ := canonical_values_int hty (toVal?_isVal h₁)
      simp only [Expr.toVal?, Option.some.injEq] at h₁
      subst h₁
      simp only [unOpEval, Option.some.injEq] at h₂
      subst h₂
      exact .typed_lit_int 0 _ _
  | binOpS op e₁ e₂ v₁ v₂ v' _ h₁ h₂ h₃ =>
    obtain ⟨A₁, A₂, hop, hty₁, hty₂⟩ := binop_inversion ht
    refine keep_ctx hΘ hheap ?_
    cases hop <;>
      (obtain ⟨z₁, rfl⟩ := canonical_values_int hty₁ (toVal?_isVal h₁)
       obtain ⟨z₂, rfl⟩ := canonical_values_int hty₂ (toVal?_isVal h₂)
       simp only [Expr.toVal?, Option.some.injEq] at h₁ h₂
       subst h₁
       subst h₂
       simp only [binOpEval, Option.some.injEq] at h₃
       subst h₃
       first
         | exact .typed_lit_int 0 _ _
         | exact .typed_lit_bool 0 _ _)
  | ifTrueS e₁ e₂ _ => exact keep_ctx hΘ hheap (if_inversion ht).2.1
  | ifFalseS e₁ e₂ _ => exact keep_ctx hΘ hheap (if_inversion ht).2.2
  | fstS e₁ e₂ _ hv₁ hv₂ =>
    obtain ⟨A₂, hty⟩ := fst_inversion ht
    obtain ⟨A₃, A₄, heq, hty₁, hty₂⟩ := pair_inversion hty
    injection heq with heqA heqB
    subst heqA
    exact keep_ctx hΘ hheap hty₁
  | sndS e₁ e₂ _ hv₁ hv₂ =>
    obtain ⟨A₁, hty⟩ := snd_inversion ht
    obtain ⟨A₃, A₄, heq, hty₁, hty₂⟩ := pair_inversion hty
    injection heq with heqA heqB
    subst heqB
    exact keep_ctx hΘ hheap hty₂
  | caseLS e₀ e₁ e₂ _ hv =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion ht
    obtain ⟨A₃, A₄, heq, hty', hwf⟩ := injl_inversion hty
    injection heq with heqA heqB
    subst heqA
    exact keep_ctx hΘ hheap (.typed_app 0 _ e₁ e₀ A₁ A hty₁ hty')
  | caseRS e₀ e₁ e₂ _ hv =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion ht
    obtain ⟨A₃, A₄, heq, hty', hwf⟩ := injr_inversion hty
    injection heq with heqA heqB
    subst heqB
    exact keep_ctx hΘ hheap (.typed_app 0 _ e₂ e₀ A₂ A hty₂ hty')
  | unrollS e₀ _ hv =>
    obtain ⟨A₂, rfl, hty⟩ := unroll_inversion ht
    obtain ⟨A₃, heq, hty'⟩ := roll_inversion hty
    injection heq with heq
    subst heq
    exact keep_ctx hΘ hheap hty'
  | newS e₀ v l _ hv hl =>
    obtain ⟨B, rfl, hty⟩ := new_inversion ht
    refine ⟨Θ.insert l B, heap_ctx_insert B hheap hl,
      heap_type_insert hheap hl hty hv,
      heap_ctx_wf_insert 0 Θ l B hΘ (syn_typed_wf hty (ctx_wf_empty 0) hΘ), ?_⟩
    exact .typed_loc 0 _ l B (by simp)
  | loadS l v _ hlv =>
    have hty := load_inversion ht
    obtain ⟨A', heq, hl⟩ := loc_inversion hty
    injection heq with heq
    subst heq
    obtain ⟨w, hw, htw⟩ := hheap l A hl
    rw [hlv] at hw
    injection hw with hw
    subst hw
    exact keep_ctx hΘ hheap htw
  | storeS l v e₂ _ hne hv =>
    obtain ⟨B, rfl, ht₁, ht₂⟩ := store_inversion ht
    obtain ⟨A', heq, hl⟩ := loc_inversion ht₁
    injection heq with heq
    subst heq
    exact ⟨Θ, HeapSubseteq.refl Θ, heap_type_update hheap hl ht₂ hv, hΘ,
      .typed_lit_unit 0 _⟩

theorem typed_preservation {Θ : HeapContext} {e e' : Expr} {A : Ty} {h h' : Heap}
    (hΘ : HeapCtxWf 0 Θ) (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A)
    (hheap : HeapType h Θ) (hstep : ContextualStep (e, h) (e', h')) :
    ∃ Θ', Θ ⊑ₕ Θ' ∧ HeapType h' Θ' ∧ HeapCtxWf 0 Θ' ∧
      SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A := by
  obtain ⟨K, ea, eb, rfl, rfl, hb⟩ := contextual_step_inv hstep
  obtain ⟨B, hB, hK⟩ := fill_typing_decompose ht
  obtain ⟨Θ', hsub, hheap', hΘ', hty'⟩ := typed_preservation_base_step hΘ hB hheap hb
  exact ⟨Θ', hsub, hheap', hΘ', hK _ Θ' hsub hty'⟩

theorem typed_preservation_steps {Θ : HeapContext} {n : Nat} {e e' : Expr} {A : Ty}
    {h h' : Heap} (hΘ : HeapCtxWf 0 Θ)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A)
    (hheap : HeapType h Θ) (hsteps : Nsteps n (e, h) (e', h')) :
    ∃ Θ', Θ ⊑ₕ Θ' ∧ HeapType h' Θ' ∧ HeapCtxWf 0 Θ' ∧
      SynTyped Θ' 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A := by
  induction n generalizing Θ e h with
  | zero =>
    obtain ⟨rfl, rfl⟩ := nsteps_zero_inv hsteps
    exact keep_ctx hΘ hheap ht
  | succ n ih =>
    obtain ⟨e₁, h₁, hstep, hrest⟩ := nsteps_succ_inv hsteps
    obtain ⟨Θ₁, hsub₁, hheap₁, hΘ₁, ht₁⟩ := typed_preservation hΘ ht hheap hstep
    obtain ⟨Θ₂, hsub₂, hheap₂, hΘ₂, ht₂⟩ := ih hΘ₁ ht₁ hheap₁ hrest
    exact ⟨Θ₂, hsub₁.trans hsub₂, hheap₂, hΘ₂, ht₂⟩

/-- A well-typed program never gets stuck. -/
theorem type_safety {Θ : HeapContext} {n : Nat} {e₁ e₂ : Expr} {A : Ty} {h₁ h₂ : Heap}
    (hΘ : HeapCtxWf 0 Θ) (hbd : HeapBounded h₁)
    (ht : SynTyped Θ 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e₁ A)
    (hheap : HeapType h₁ Θ) (hsteps : Nsteps n (e₁, h₁) (e₂, h₂)) :
    Expr.isVal e₂ ∨ reducible e₂ h₂ := by
  obtain ⟨Θ', _, hheap', hΘ', ht'⟩ := typed_preservation_steps hΘ ht hheap hsteps
  refine typed_progress ?_ hheap' ht'
  clear ht hheap ht' hheap' hΘ hΘ'
  induction n generalizing e₁ h₁ with
  | zero =>
    obtain ⟨rfl, rfl⟩ := nsteps_zero_inv hsteps
    exact hbd
  | succ n ih =>
    obtain ⟨e', h', hstep, hrest⟩ := nsteps_succ_inv hsteps
    exact ih (contextual_step_heapBounded hbd hstep) hrest

/-- For a program with no free locations, the empty heap suffices. -/
theorem closed_type_safety {n : Nat} {e e' : Expr} {A : Ty} {h : Heap}
    (ht : SynTyped HeapContext.empty 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A)
    (hsteps : Nsteps n (e, Heap.empty) (e', h)) : Expr.isVal e' ∨ reducible e' h :=
  type_safety (heap_ctx_wf_empty 0) heapBounded_empty ht
    (fun l A hl => absurd hl (by simp [HeapContext.empty])) hsteps

end SystemFMuState.Syn
