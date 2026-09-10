import LeanLR.TypeSystems.SystemF.Lang
import LeanLR.TypeSystems.SystemF.Types
import LeanLR.TypeSystems.SystemF.Pure
import LeanLR.TypeSystems.SystemF.ParallelSubst

/-!
# System F: syntactic type safety

The rest of `systemf/types.v`: context inclusion and type substitution on contexts, the
`free_vars`/`bounded` characterisation of well-formedness, weakening, the typing inversion
lemmas, substitutivity for both term and type variables, canonical values, progress,
preservation and safety.
-/

open Iris.Std

namespace SystemF

/-! ## Contexts

Rocq works with `gmap` inclusion `Γ ⊆ Δ` and the functorial action `f <$> Γ`. Here inclusion is
spelled out pointwise and the two context maps that are needed — shifting (`shiftCtx`, already in
`Types.lean`) and type substitution (`substCtx`) — are defined directly. -/

/-- Context inclusion: `Δ` types every variable `Γ` types, at the same type. -/
def CtxSubseteq (Γ Δ : TypingContext) : Prop :=
  ∀ x A, get? (M := TyMapStr) Γ x = some A → get? (M := TyMapStr) Δ x = some A

@[inherit_doc] scoped infix:50 " ⊑ " => CtxSubseteq

theorem CtxSubseteq.refl (Γ : TypingContext) : Γ ⊑ Γ := fun _ _ h => h

theorem CtxSubseteq.trans {Γ Δ Θ : TypingContext} (h₁ : Γ ⊑ Δ) (h₂ : Δ ⊑ Θ) : Γ ⊑ Θ :=
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
        (insert (M := TyMapStr) (substCtx σ Γ) x (A.substTy σ)) x = some (A.substTy σ) :=
      LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl
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
  show get? (M := TyMapStr) (substCtx σ (PartialMap.empty (M := TyMapStr) (V := Ty))) y
      = get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y
  rw [substCtx_get?, show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) y]
  rfl

theorem shiftCtx_empty :
    shiftCtx (PartialMap.empty (M := TyMapStr) (V := Ty))
      = PartialMap.empty (M := TyMapStr) (V := Ty) := by
  refine Std.ExtTreeMap.ext_getElem? fun y => ?_
  show get? (M := TyMapStr) (shiftCtx (PartialMap.empty (M := TyMapStr) (V := Ty))) y
      = get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y
  rw [shiftCtx_get?, show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) y = none from
    LawfulPartialMap.get?_empty (M := TyMapStr) y]
  rfl

/-- Shifting a substituted context is substituting into the shifted context, with the
substitution lifted under the new binder. -/
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
    | fn_wf _ _ ihA ihB | prod_wf _ _ ihA ihB | sum_wf _ _ ihA ihB =>
      intro x hx
      rcases hx with hx | hx
      · exact ihA x hx
      · exact ihB x hx
    | all_wf _ ih | exist_wf _ ih =>
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

theorem free_vars_rename (A : Ty) (x : Nat) (f : Nat → Nat) (h : A.freeVars x) :
    (A.rename f).freeVars (f x) := by
  induction A generalizing x f with
  | tVar m => simpa [Ty.freeVars, Ty.rename] using congrArg f h
  | int | bool | unit => exact h.elim
  | fn A B ihA ihB | prod A B ihA ihB | sum A B ihA ihB =>
    rcases h with h | h
    · exact Or.inl (ihA x f h)
    · exact Or.inr (ihB x f h)
  | all A ih | exist A ih =>
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
  | fn A B ihA ihB | prod A B ihA ihB | sum A B ihA ihB =>
    rcases hfree with hfree | hfree
    · exact ihA x n σ (fun y hy => hbd y (Or.inl hy)) hfree
    · exact ihB x n σ (fun y hy => hbd y (Or.inr hy)) hfree
  | all A ih | exist A ih =>
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

/-! ## Weakening -/

theorem typed_weakening {n m : Nat} {Γ Δ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped n Γ e A) (hsub : Γ ⊑ Δ) (hle : n ≤ m) : SynTyped m Δ e A := by
  induction ht generalizing Δ m with
  | typed_lit_int n Γ z => exact .typed_lit_int m Δ z
  | typed_lit_bool n Γ b => exact .typed_lit_bool m Δ b
  | typed_lit_unit n Γ => exact .typed_lit_unit m Δ
  | typed_var n Γ x A hx => exact .typed_var m Δ x A (hsub x A hx)
  | typed_lam n Γ x e A B hA _ ih =>
    exact .typed_lam m Δ x e A B (hA.mono m hle) (ih (hsub.insert_mono x A) hle)
  | typed_lam_anon n Γ e A B hA _ ih =>
    exact .typed_lam_anon m Δ e A B (hA.mono m hle) (ih hsub hle)
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_app m Δ e₁ e₂ A B (ih₁ hsub hle) (ih₂ hsub hle)
  | typed_tLam n Γ e A _ ih =>
    exact .typed_tLam m Δ e A (ih (renaming_inclusion hsub) (Nat.succ_le_succ hle))
  | typed_tApp n Γ e A B hB _ ih =>
    exact .typed_tApp m Δ e A B (hB.mono m hle) (ih hsub hle)
  | typed_pack n Γ e A B hB hA _ ih =>
    exact .typed_pack m Δ e A B (hB.mono m hle) (hA.mono (m + 1) (Nat.succ_le_succ hle))
      (ih hsub hle)
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ ih₁ ih₂ =>
    exact .typed_unpack m Δ x e₁ e₂ A B (hB.mono m hle) (ih₁ hsub hle)
      (ih₂ ((renaming_inclusion hsub).insert_mono x A) (Nat.succ_le_succ hle))
  | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    exact .typed_pair m Δ e₁ e₂ A B (ih₁ hsub hle) (ih₂ hsub hle)
  | typed_fst n Γ e A B _ ih => exact .typed_fst m Δ e A B (ih hsub hle)
  | typed_snd n Γ e A B _ ih => exact .typed_snd m Δ e A B (ih hsub hle)
  | typed_injL n Γ e A B hB _ ih => exact .typed_injL m Δ e A B (hB.mono m hle) (ih hsub hle)
  | typed_injR n Γ e A B hA _ ih => exact .typed_injR m Δ e A B (hA.mono m hle) (ih hsub hle)
  | typed_case n Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂ =>
    exact .typed_case m Δ e e₁ e₂ A B C (ih hsub hle) (ih₁ hsub hle) (ih₂ hsub hle)
  | typed_unOp n Γ op e A B hop _ ih => exact .typed_unOp m Δ op e A B hop (ih hsub hle)
  | typed_binOp n Γ op e₁ e₂ A B C hop _ _ ih₁ ih₂ =>
    exact .typed_binOp m Δ op e₁ e₂ A B C hop (ih₁ hsub hle) (ih₂ hsub hle)
  | typed_if n Γ e₀ e₁ e₂ A _ _ _ ih₀ ih₁ ih₂ =>
    exact .typed_if m Δ e₀ e₁ e₂ A (ih₀ hsub hle) (ih₁ hsub hle) (ih₂ hsub hle)

/-! ## Well-formedness of the typed type -/

theorem syn_typed_wf {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (hΓ : CtxWf n Γ) (ht : SynTyped n Γ e A) : TypeWf n A := by
  induction ht with
  | typed_lit_int _ _ _ => exact .int_wf
  | typed_lit_bool _ _ _ => exact .bool_wf
  | typed_lit_unit _ _ => exact .unit_wf
  | typed_var n Γ x A hx => exact hΓ x A hx
  | typed_lam n Γ x e A B hA _ ih => exact .fn_wf hA (ih (ctx_wf_insert n Γ x A hΓ hA))
  | typed_lam_anon n Γ e A B hA _ ih => exact .fn_wf hA (ih hΓ)
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ _ =>
    match ih₁ hΓ with
    | .fn_wf _ hB => exact hB
  | typed_tLam n Γ e A _ ih => exact .all_wf (ih (ctx_wf_up n Γ hΓ))
  | typed_tApp n Γ e A B hB _ ih =>
    match ih hΓ with
    | .all_wf hA => exact TypeWf.subst1 A B n hA hB
  | typed_pack n Γ e A B _ hA _ _ => exact .exist_wf hA
  | typed_unpack n Γ x e₁ e₂ A B hB _ _ _ _ => exact hB
  | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ => exact .prod_wf (ih₁ hΓ) (ih₂ hΓ)
  | typed_fst n Γ e A B _ ih =>
    match ih hΓ with
    | .prod_wf hA _ => exact hA
  | typed_snd n Γ e A B _ ih =>
    match ih hΓ with
    | .prod_wf _ hB => exact hB
  | typed_injL n Γ e A B hB _ ih => exact .sum_wf (ih hΓ) hB
  | typed_injR n Γ e A B hA _ ih => exact .sum_wf hA (ih hΓ)
  | typed_case n Γ e e₁ e₂ A B C _ _ _ _ ih₁ _ =>
    match ih₁ hΓ with
    | .fn_wf _ hA => exact hA
  | typed_unOp n Γ op e A B hop _ _ => cases hop <;> first | exact .bool_wf | exact .int_wf
  | typed_binOp n Γ op e₁ e₂ A B C hop _ _ _ _ =>
    cases hop <;> first | exact .int_wf | exact .bool_wf
  | typed_if n Γ e₀ e₁ e₂ A _ _ _ _ ih₁ _ => exact ih₁ hΓ

/-! ## Type substitution is insensitive outside the scope -/

theorem type_wf_subst_dom {σ τ : Nat → Ty} {n : Nat} {A : Ty} (hA : TypeWf n A)
    (h : ∀ m, m < n → σ m = τ m) : A.substTy σ = A.substTy τ := by
  induction hA generalizing σ τ with
  | tVar_wf hlt => exact h _ hlt
  | int_wf | bool_wf | unit_wf => rfl
  | fn_wf _ _ ihA ihB | prod_wf _ _ ihA ihB | sum_wf _ _ ihA ihB =>
    simp only [Ty.substTy, ihA h, ihB h]
  | all_wf _ ih | exist_wf _ ih =>
    refine congrArg _ (ih fun m hm => ?_)
    match m with
    | 0 => rfl
    | m+1 => exact congrArg (Ty.rename (· + 1)) (h m (Nat.lt_of_succ_lt_succ hm))

/-- Renaming is the substitution built from variables. -/
theorem Ty.rename_eq_substTy (A : Ty) (f : Nat → Nat) :
    A.rename f = A.substTy (fun n => .tVar (f n)) := by
  induction A generalizing f with
  | tVar _ | int | bool | unit => rfl
  | fn _ _ ihA ihB | prod _ _ ihA ihB | sum _ _ ihA ihB =>
    simp only [Ty.rename, Ty.substTy, ihA, ihB]
  | all _ ih | exist _ ih =>
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

/-! ## Typed expressions are closed -/

theorem syn_typed_closed {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty} {X : List String}
    (ht : SynTyped n Γ e A) (hX : ∀ x, get? (M := TyMapStr) Γ x ≠ none → x ∈ X) : closed X e := by
  induction ht generalizing X with
  | typed_lit_int _ _ _ | typed_lit_bool _ _ _ | typed_lit_unit _ _ => rfl
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
  | typed_app n Γ e₁ e₂ A B _ _ ih₁ ih₂ | typed_pair n Γ e₁ e₂ A B _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ hX, ih₂ hX⟩
  | typed_binOp n Γ op e₁ e₂ A B C _ _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ hX, ih₂ hX⟩
  | typed_tApp n Γ e A B _ _ ih | typed_pack n Γ e A B _ _ _ ih
  | typed_fst n Γ e A B _ ih | typed_snd n Γ e A B _ ih
  | typed_injL n Γ e A B _ _ ih | typed_injR n Γ e A B _ _ ih
  | typed_unOp n Γ op e A B _ _ ih => exact ih hX
  | typed_case n Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂
  | typed_if n Γ e A e₁ e₂ _ _ _ ih ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨⟨ih hX, ih₁ hX⟩, ih₂ hX⟩

/-! ## Derived typing rules -/

/-- The typing rule for the `match` sugar. -/
theorem typed_match {n : Nat} {Γ : TypingContext} {e e₁ e₂ : Expr} {x₁ x₂ : String}
    {A B C : Ty} (hB : TypeWf n B) (hC : TypeWf n C) (ht : SynTyped n Γ e (.sum B C))
    (h₁ : SynTyped n (insert (M := TyMapStr) Γ x₁ B) e₁ A)
    (h₂ : SynTyped n (insert (M := TyMapStr) Γ x₂ C) e₂ A) :
    SynTyped n Γ (.case e (.lam (.bNamed x₁) e₁) (.lam (.bNamed x₂) e₂)) A :=
  .typed_case n Γ e _ _ B C A ht (.typed_lam n Γ x₁ e₁ B A hB h₁)
    (.typed_lam n Γ x₂ e₂ C A hC h₂)

theorem typed_tapp' {n : Nat} {Γ : TypingContext} {e : Expr} {A B C : Ty}
    (ht : SynTyped n Γ e (.all A)) (hB : TypeWf n B) (heq : C = A.subst1 B) :
    SynTyped n Γ (.tApp e) C :=
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

theorem var_inversion {n : Nat} {Γ : TypingContext} {x : String} {A : Ty}
    (h : SynTyped n Γ (.var x) A) : get? (M := TyMapStr) Γ x = some A := by
  cases h
  assumption

theorem lam_inversion {n : Nat} {Γ : TypingContext} {x : String} {e : Expr} {C : Ty}
    (h : SynTyped n Γ (.lam (.bNamed x) e) C) :
    ∃ A B, C = .fn A B ∧ TypeWf n A ∧ SynTyped n (insert (M := TyMapStr) Γ x A) e B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem lam_anon_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped n Γ (.lam .bAnon e) C) :
    ∃ A B, C = .fn A B ∧ TypeWf n A ∧ SynTyped n Γ e B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem app_inversion {n : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped n Γ (.app e₁ e₂) B) :
    ∃ A, SynTyped n Γ e₁ (.fn A B) ∧ SynTyped n Γ e₂ A := by
  cases h
  exact ⟨_, by assumption, by assumption⟩

theorem if_inversion {n : Nat} {Γ : TypingContext} {e₀ e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped n Γ (.ite e₀ e₁ e₂) B) :
    SynTyped n Γ e₀ .bool ∧ SynTyped n Γ e₁ B ∧ SynTyped n Γ e₂ B := by
  cases h
  exact ⟨by assumption, by assumption, by assumption⟩

theorem binop_inversion {n : Nat} {Γ : TypingContext} {op : BinOp} {e₁ e₂ : Expr} {B : Ty}
    (h : SynTyped n Γ (.binOp op e₁ e₂) B) :
    ∃ A₁ A₂, BinOpTyped op A₁ A₂ B ∧ SynTyped n Γ e₁ A₁ ∧ SynTyped n Γ e₂ A₂ := by
  cases h
  exact ⟨_, _, by assumption, by assumption, by assumption⟩

theorem unop_inversion {n : Nat} {Γ : TypingContext} {op : UnOp} {e : Expr} {B : Ty}
    (h : SynTyped n Γ (.unOp op e) B) :
    ∃ A, UnOpTyped op A B ∧ SynTyped n Γ e A := by
  cases h
  exact ⟨_, by assumption, by assumption⟩

theorem type_app_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped n Γ (.tApp e) B) :
    ∃ A C, B = A.subst1 C ∧ TypeWf n C ∧ SynTyped n Γ e (.all A) := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem type_lam_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped n Γ (.tLam e) B) :
    ∃ A, B = .all A ∧ SynTyped (n + 1) (shiftCtx Γ) e A := by
  cases h
  exact ⟨_, rfl, by assumption⟩

theorem type_pack_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped n Γ (.pack e) B) :
    ∃ A C, B = .exist A ∧ SynTyped n Γ e (A.subst1 C) ∧ TypeWf n C ∧ TypeWf (n + 1) A := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption, by assumption⟩

theorem type_unpack_inversion {n : Nat} {Γ : TypingContext} {b : Binder} {e e' : Expr} {B : Ty}
    (h : SynTyped n Γ (.unpack b e e') B) :
    ∃ A x', b = .bNamed x' ∧ TypeWf n B ∧ SynTyped n Γ e (.exist A) ∧
      SynTyped (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x' A) e' (B.rename (· + 1)) := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption, by assumption⟩

theorem pair_inversion {n : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {C : Ty}
    (h : SynTyped n Γ (.pair e₁ e₂) C) :
    ∃ A B, C = .prod A B ∧ SynTyped n Γ e₁ A ∧ SynTyped n Γ e₂ B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem fst_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (h : SynTyped n Γ (.fst e) A) : ∃ B, SynTyped n Γ e (.prod A B) := by
  cases h
  exact ⟨_, by assumption⟩

theorem snd_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {B : Ty}
    (h : SynTyped n Γ (.snd e) B) : ∃ A, SynTyped n Γ e (.prod A B) := by
  cases h
  exact ⟨_, by assumption⟩

theorem injl_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped n Γ (.injL e) C) :
    ∃ A B, C = .sum A B ∧ SynTyped n Γ e A ∧ TypeWf n B := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem injr_inversion {n : Nat} {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : SynTyped n Γ (.injR e) C) :
    ∃ A B, C = .sum A B ∧ SynTyped n Γ e B ∧ TypeWf n A := by
  cases h
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem case_inversion {n : Nat} {Γ : TypingContext} {e e₁ e₂ : Expr} {A : Ty}
    (h : SynTyped n Γ (.case e e₁ e₂) A) :
    ∃ B C, SynTyped n Γ e (.sum B C) ∧ SynTyped n Γ e₁ (.fn B A) ∧
      SynTyped n Γ e₂ (.fn C A) := by
  cases h
  exact ⟨_, _, by assumption, by assumption, by assumption⟩

/-! ## Canonical values -/

theorem canonical_values_arr {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped n Γ e (.fn A B)) (hv : Expr.isVal e) :
    ∃ (x : Binder) (e' : Expr), e = .lam x e' := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .fn A B →
      ∃ (x : Binder) (e' : Expr), e = .lam x e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, _, rfl⟩

theorem canonical_values_forall {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped n Γ e (.all A)) (hv : Expr.isVal e) : ∃ e', e = .tLam e' := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .all A → ∃ e', e = .tLam e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_exists {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped n Γ e (.exist A)) (hv : Expr.isVal e) : ∃ e', e = .pack e' := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .exist A → ∃ e', e = .pack e' by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_int {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped n Γ e .int) (hv : Expr.isVal e) : ∃ z : Int, e = .lit (.litInt z) := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .int → ∃ z : Int, e = .lit (.litInt z) by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_bool {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped n Γ e .bool) (hv : Expr.isVal e) : ∃ b : Bool, e = .lit (.litBool b) := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .bool → ∃ b : Bool, e = .lit (.litBool b) by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, rfl⟩

theorem canonical_values_unit {n : Nat} {Γ : TypingContext} {e : Expr}
    (ht : SynTyped n Γ e .unit) (hv : Expr.isVal e) : e = .lit .litUnit := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .unit → e = .lit .litUnit by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | rfl

theorem canonical_values_prod {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped n Γ e (.prod A B)) (hv : Expr.isVal e) :
    ∃ e₁ e₂, e = .pair e₁ e₂ ∧ Expr.isVal e₁ ∧ Expr.isVal e₂ := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .prod A B →
      ∃ e₁ e₂, e = .pair e₁ e₂ ∧ Expr.isVal e₁ ∧ Expr.isVal e₂ by exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact ⟨_, _, rfl, hv.1, hv.2⟩

theorem canonical_values_sum {n : Nat} {Γ : TypingContext} {e : Expr} {A B : Ty}
    (ht : SynTyped n Γ e (.sum A B)) (hv : Expr.isVal e) :
    (∃ e', e = .injL e' ∧ Expr.isVal e') ∨ (∃ e', e = .injR e' ∧ Expr.isVal e') := by
  suffices h : ∀ T : Ty, SynTyped n Γ e T → T = .sum A B →
      (∃ e', e = .injL e' ∧ Expr.isVal e') ∨ (∃ e', e = .injR e' ∧ Expr.isVal e') by
    exact h _ ht rfl
  intro T ht' hT
  cases ht' <;>
    solve
      | (exfalso; simp [Expr.isVal] at hv)
      | (exfalso; simp at hT)
      | exact Or.inl ⟨_, rfl, hv⟩
      | exact Or.inr ⟨_, rfl, hv⟩

/-! ## Substitutivity for term variables -/

theorem typed_substitutivity {n : Nat} {Γ : TypingContext} {e e' : Expr} {x : String} {A B : Ty}
    (he' : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A)
    (ht : SynTyped n (insert (M := TyMapStr) Γ x A) e B) :
    SynTyped n Γ (subst x e' e) B := by
  have hAwf : TypeWf 0 A := syn_typed_wf (ctx_wf_empty 0) he'
  suffices h : ∀ (e : Expr) (n : Nat) (Γ : TypingContext) (B : Ty),
      SynTyped n (insert (M := TyMapStr) Γ x A) e B → SynTyped n Γ (subst x e' e) B by
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
      exact typed_weakening he' (CtxSubseteq.empty_le Γ) (Nat.zero_le n)
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
    rw [shiftCtx_insert, type_wf_closed_rename A (· + 1) hAwf] at hty
    simp only [subst]
    exact .typed_tLam n Γ _ A₂ (ih (n + 1) (shiftCtx Γ) A₂ hty)
  | pack e ih =>
    intro n Γ B ht
    obtain ⟨A₂, C, rfl, hty, hwfC, hwfA⟩ := type_pack_inversion ht
    simp only [subst]
    exact .typed_pack n Γ _ A₂ C hwfC hwfA (ih n Γ (A₂.subst1 C) hty)
  | unpack b e₁ e₂ ih₁ ih₂ =>
    intro n Γ B ht
    obtain ⟨A₂, x', rfl, hwfB, hty₁, hty₂⟩ := type_unpack_inversion ht
    rw [shiftCtx_insert, type_wf_closed_rename A (· + 1) hAwf] at hty₂
    simp only [subst]
    by_cases hxy : x = x'
    · subst hxy
      rw [insert_insert_eq] at hty₂
      rw [if_pos rfl]
      exact .typed_unpack n Γ x _ e₂ A₂ B hwfB (ih₁ n Γ (.exist A₂) hty₁) hty₂
    · rw [if_neg (fun h => hxy (by cases h; rfl))]
      rw [insert_comm _ hxy A A₂] at hty₂
      exact .typed_unpack n Γ x' _ _ A₂ B hwfB (ih₁ n Γ (.exist A₂) hty₁)
        (ih₂ (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x' A₂) (B.rename (· + 1)) hty₂)
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

/-! ## Progress -/

theorem typed_progress {e : Expr} {A : Ty}
    (ht : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) :
    Expr.isVal e ∨ reducible e := by
  suffices h : ∀ (n : Nat) (Γ : TypingContext) (e : Expr) (A : Ty), SynTyped n Γ e A →
      Γ = PartialMap.empty (M := TyMapStr) (V := Ty) → Expr.isVal e ∨ reducible e by
    exact h 0 _ e A ht rfl
  clear ht
  intro n Γ e A ht
  induction ht with
  | typed_lit_int _ _ _ | typed_lit_bool _ _ _ | typed_lit_unit _ _
  | typed_lam _ _ _ _ _ _ _ _ | typed_lam_anon _ _ _ _ _ _ _ | typed_tLam _ _ _ _ _ =>
    intro _
    exact Or.inl trivial
  | typed_var n Γ x A hx =>
    intro hΓ
    subst hΓ
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
      LawfulPartialMap.get?_empty (M := TyMapStr) x] at hx
    exact absurd hx (by simp)
  | typed_app n Γ e₁ e₂ A B ht₁ ht₂ ih₁ ih₂ =>
    intro hΓ
    rcases ih₂ hΓ with hv₂ | hred₂
    · rcases ih₁ hΓ with hv₁ | hred₁
      · obtain ⟨y, body, rfl⟩ := canonical_values_arr ht₁ hv₁
        exact Or.inr ⟨_, base_contextual_step (.betaS y body e₂ hv₂)⟩
      · obtain ⟨e₁', hstep⟩ := hred₁
        exact Or.inr ⟨_, contextual_step_app_l hv₂ hstep⟩
    · obtain ⟨e₂', hstep⟩ := hred₂
      exact Or.inr ⟨_, contextual_step_app_r e₁ hstep⟩
  | typed_tApp n Γ e A B hwf ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · obtain ⟨e', rfl⟩ := canonical_values_forall ht' hv
      exact Or.inr ⟨_, base_contextual_step (.tBetaS e')⟩
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_tapp hstep⟩
  | typed_pack n Γ e A B hwfB hwfA ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_pack hstep⟩
  | typed_unpack n Γ x e₁ e₂ A B hwfB ht₁ ht₂ ih₁ ih₂ =>
    intro hΓ
    rcases ih₁ hΓ with hv₁ | hred₁
    · obtain ⟨e'', rfl⟩ := canonical_values_exists ht₁ hv₁
      exact Or.inr ⟨_, base_contextual_step (.unpackS (.bNamed x) e'' e₂ hv₁)⟩
    · obtain ⟨e₁', hstep⟩ := hred₁
      exact Or.inr ⟨_, contextual_step_unpack (.bNamed x) e₂ hstep⟩
  | typed_if n Γ e₀ e₁ e₂ A ht₀ ht₁ ht₂ ih₀ ih₁ ih₂ =>
    intro hΓ
    rcases ih₀ hΓ with hv₀ | hred₀
    · obtain ⟨b, rfl⟩ := canonical_values_bool ht₀ hv₀
      cases b
      · exact Or.inr ⟨_, base_contextual_step (.ifFalseS e₁ e₂)⟩
      · exact Or.inr ⟨_, base_contextual_step (.ifTrueS e₁ e₂)⟩
    · obtain ⟨e₀', hstep⟩ := hred₀
      exact Or.inr ⟨_, contextual_step_if e₁ e₂ hstep⟩
  | typed_binOp n Γ op e₁ e₂ A B C hop ht₁ ht₂ ih₁ ih₂ =>
    intro hΓ
    rcases ih₂ hΓ with hv₂ | hred₂
    · rcases ih₁ hΓ with hv₁ | hred₁
      · cases hop <;>
          (obtain ⟨z₁, rfl⟩ := canonical_values_int ht₁ hv₁
           obtain ⟨z₂, rfl⟩ := canonical_values_int ht₂ hv₂
           exact Or.inr ⟨_, base_contextual_step
             (.binOpS _ _ _ (.litV (.litInt z₁)) (.litV (.litInt z₂)) _ rfl rfl rfl)⟩)
      · obtain ⟨e₁', hstep⟩ := hred₁
        exact Or.inr ⟨_, contextual_step_binop_l op hv₂ hstep⟩
    · obtain ⟨e₂', hstep⟩ := hred₂
      exact Or.inr ⟨_, contextual_step_binop_r op e₁ hstep⟩
  | typed_unOp n Γ op e A B hop ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · cases hop
      · obtain ⟨b, rfl⟩ := canonical_values_bool ht' hv
        exact Or.inr ⟨_, base_contextual_step (.unOpS _ _ (.litV (.litBool b)) _ rfl rfl)⟩
      · obtain ⟨z, rfl⟩ := canonical_values_int ht' hv
        exact Or.inr ⟨_, base_contextual_step (.unOpS _ _ (.litV (.litInt z)) _ rfl rfl)⟩
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_unop op hstep⟩
  | typed_pair n Γ e₁ e₂ A B ht₁ ht₂ ih₁ ih₂ =>
    intro hΓ
    rcases ih₂ hΓ with hv₂ | hred₂
    · rcases ih₁ hΓ with hv₁ | hred₁
      · exact Or.inl ⟨hv₁, hv₂⟩
      · obtain ⟨e₁', hstep⟩ := hred₁
        exact Or.inr ⟨_, contextual_step_pair_l hv₂ hstep⟩
    · obtain ⟨e₂', hstep⟩ := hred₂
      exact Or.inr ⟨_, contextual_step_pair_r e₁ hstep⟩
  | typed_fst n Γ e A B ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod ht' hv
      exact Or.inr ⟨_, base_contextual_step (.fstS e₁ e₂ hv₁ hv₂)⟩
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_fst hstep⟩
  | typed_snd n Γ e A B ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod ht' hv
      exact Or.inr ⟨_, base_contextual_step (.sndS e₁ e₂ hv₁ hv₂)⟩
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_snd hstep⟩
  | typed_injL n Γ e A B hwf ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_injl hstep⟩
  | typed_injR n Γ e A B hwf ht' ih =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · exact Or.inl hv
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_injr hstep⟩
  | typed_case n Γ e e₁ e₂ A B C ht' ht₁ ht₂ ih ih₁ ih₂ =>
    intro hΓ
    rcases ih hΓ with hv | hred
    · rcases canonical_values_sum ht' hv with ⟨e'', rfl, hv''⟩ | ⟨e'', rfl, hv''⟩
      · exact Or.inr ⟨_, base_contextual_step (.caseLS e'' e₁ e₂ hv'')⟩
      · exact Or.inr ⟨_, base_contextual_step (.caseRS e'' e₁ e₂ hv'')⟩
    · obtain ⟨e', hstep⟩ := hred
      exact Or.inr ⟨_, contextual_step_case e₁ e₂ hstep⟩

/-! ## Typed evaluation contexts -/

def EctxItemTyping (Ki : EctxItem) (A B : Ty) : Prop :=
  ∀ e, SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A →
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) B

def EctxTyping (K : Ectx) (A B : Ty) : Prop :=
  ∀ e, SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A →
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) B

theorem fill_item_typing_decompose {Ki : EctxItem} {e : Expr} {A : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) A) :
    ∃ B, SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B ∧ EctxItemTyping Ki B A := by
  cases Ki <;> simp only [fillItem] at h
  case appLCtx v =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion h
    exact ⟨.fn A₁ A, ht₁, fun e' h' => .typed_app 0 _ e' _ A₁ A h' ht₂⟩
  case appRCtx e₁ =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion h
    exact ⟨A₁, ht₂, fun e' h' => .typed_app 0 _ e₁ e' A₁ A ht₁ h'⟩
  case unOpCtx op =>
    obtain ⟨A₁, hop, ht⟩ := unop_inversion h
    exact ⟨A₁, ht, fun e' h' => .typed_unOp 0 _ op e' A₁ A hop h'⟩
  case binOpLCtx op v =>
    obtain ⟨A₁, A₂, hop, ht₁, ht₂⟩ := binop_inversion h
    exact ⟨A₁, ht₁, fun e' h' => .typed_binOp 0 _ op e' _ A₁ A₂ A hop h' ht₂⟩
  case binOpRCtx op e₁ =>
    obtain ⟨A₁, A₂, hop, ht₁, ht₂⟩ := binop_inversion h
    exact ⟨A₂, ht₂, fun e' h' => .typed_binOp 0 _ op e₁ e' A₁ A₂ A hop ht₁ h'⟩
  case ifCtx e₁ e₂ =>
    obtain ⟨ht₀, ht₁, ht₂⟩ := if_inversion h
    exact ⟨.bool, ht₀, fun e' h' => .typed_if 0 _ e' e₁ e₂ A h' ht₁ ht₂⟩
  case tAppCtx =>
    obtain ⟨A₂, C, rfl, hwf, hty⟩ := type_app_inversion h
    exact ⟨.all A₂, hty, fun e' h' => .typed_tApp 0 _ e' A₂ C hwf h'⟩
  case packCtx =>
    obtain ⟨A₂, C, rfl, hty, hwfC, hwfA⟩ := type_pack_inversion h
    exact ⟨A₂.subst1 C, hty, fun e' h' => .typed_pack 0 _ e' A₂ C hwfC hwfA h'⟩
  case unpackCtx x e₂ =>
    obtain ⟨A₂, x', rfl, hwfB, hty₁, hty₂⟩ := type_unpack_inversion h
    exact ⟨.exist A₂, hty₁, fun e' h' => .typed_unpack 0 _ x' e' e₂ A₂ A hwfB h' hty₂⟩
  case pairLCtx v =>
    obtain ⟨A₁, A₂, rfl, ht₁, ht₂⟩ := pair_inversion h
    exact ⟨A₁, ht₁, fun e' h' => .typed_pair 0 _ e' _ A₁ A₂ h' ht₂⟩
  case pairRCtx e₁ =>
    obtain ⟨A₁, A₂, rfl, ht₁, ht₂⟩ := pair_inversion h
    exact ⟨A₂, ht₂, fun e' h' => .typed_pair 0 _ e₁ e' A₁ A₂ ht₁ h'⟩
  case fstCtx =>
    obtain ⟨A₂, hty⟩ := fst_inversion h
    exact ⟨.prod A A₂, hty, fun e' h' => .typed_fst 0 _ e' A A₂ h'⟩
  case sndCtx =>
    obtain ⟨A₁, hty⟩ := snd_inversion h
    exact ⟨.prod A₁ A, hty, fun e' h' => .typed_snd 0 _ e' A₁ A h'⟩
  case injLCtx =>
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injl_inversion h
    exact ⟨A₁, hty, fun e' h' => .typed_injL 0 _ e' A₁ A₂ hwf h'⟩
  case injRCtx =>
    obtain ⟨A₁, A₂, rfl, hty, hwf⟩ := injr_inversion h
    exact ⟨A₂, hty, fun e' h' => .typed_injR 0 _ e' A₁ A₂ hwf h'⟩
  case caseCtx e₁ e₂ =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion h
    exact ⟨.sum A₁ A₂, hty, fun e' h' => .typed_case 0 _ e' e₁ e₂ A₁ A₂ A h' hty₁ hty₂⟩

theorem fill_item_typing_compose {Ki : EctxItem} {e : Expr} {A B : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B)
    (hK : EctxItemTyping Ki B A) :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fillItem Ki e) A := hK e h

theorem fill_typing_decompose {K : Ectx} {e : Expr} {A : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) A) :
    ∃ B, SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B ∧ EctxTyping K B A := by
  induction K generalizing e A with
  | nil => exact ⟨A, h, fun _ h' => h'⟩
  | cons Ki K ih =>
    rw [fill_cons] at h
    obtain ⟨B, hB, hK⟩ := ih h
    obtain ⟨B', hB', hKi⟩ := fill_item_typing_decompose hB
    refine ⟨B', hB', fun e' h' => ?_⟩
    rw [fill_cons]
    exact hK _ (hKi e' h')

theorem fill_typing_compose {K : Ectx} {e : Expr} {A B : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e B) (hK : EctxTyping K B A) :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) (fill K e) A := hK e h

/-! ## Substitutivity for type variables -/

/-- Substitution into a single substitution. -/
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

theorem typed_subst_type {n m : Nat} {Γ : TypingContext} {e : Expr} {A : Ty} {σ : Nat → Ty}
    (ht : SynTyped n Γ e A) (hσ : ∀ k, k < n → TypeWf m (σ k)) :
    SynTyped m (substCtx σ Γ) e (A.substTy σ) := by
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
    rw [fmap_up_subst]
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
    rw [Ty.rename_shift_substTy, substCtx_insert, ← fmap_up_subst] at h₂
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

theorem typed_subst_type_closed (C : Ty) (e : Expr) (A : Ty) (hwf : TypeWf 0 C)
    (ht : SynTyped 1 (shiftCtx (PartialMap.empty (M := TyMapStr) (V := Ty))) e A) :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e (A.subst1 C) := by
  have h := typed_subst_type (σ := fun n => match n with | 0 => C | n+1 => .tVar n) ht
    (fun k hk => by
      match k with
      | 0 => exact hwf
      | k+1 => exact absurd hk (by omega))
  rw [shiftCtx_empty, substCtx_empty] at h
  exact h

theorem typed_subst_type_closed' (x : String) (C B : Ty) (e : Expr) (A : Ty)
    (hA : TypeWf 0 A) (_hC : TypeWf 1 C) (hB : TypeWf 0 B)
    (ht : SynTyped 1 (insert (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x C)
      e A) :
    SynTyped 0 (insert (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x
      (C.subst1 B)) e A := by
  have h := typed_subst_type (σ := fun n => match n with | 0 => B | n+1 => .tVar n) ht
    (fun k hk => by
      match k with
      | 0 => exact hB
      | k+1 => exact absurd hk (by omega))
  rw [substCtx_insert, substCtx_empty, type_wf_closed A _ hA] at h
  exact h

/-! ## Preservation and safety -/

theorem typed_preservation_base_step {e e' : Expr} {A : Ty}
    (ht : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) (hstep : BaseStep e e') :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A := by
  cases hstep with
  | betaS y e₁ e₂ hv =>
    obtain ⟨A₁, ht₁, ht₂⟩ := app_inversion ht
    cases y with
    | bAnon =>
      obtain ⟨A', C, heq, hwf, hty⟩ := lam_anon_inversion ht₁
      injection heq with heqA heqC
      subst heqA
      subst heqC
      exact hty
    | bNamed y =>
      obtain ⟨A', C, heq, hwf, hty⟩ := lam_inversion ht₁
      injection heq with heqA heqC
      subst heqA
      subst heqC
      exact typed_substitutivity ht₂ hty
  | tBetaS e₀ =>
    obtain ⟨A₂, C, rfl, hwf, hty⟩ := type_app_inversion ht
    obtain ⟨A₃, heq, hty'⟩ := type_lam_inversion hty
    injection heq with heq
    subst heq
    exact typed_subst_type_closed C _ A₂ hwf hty'
  | unpackS y e₁ e₂ hv =>
    obtain ⟨A₂, x', hb, hwfA, hty₁, hty₂⟩ := type_unpack_inversion ht
    subst hb
    obtain ⟨A₃, C, heq, hty₁', hwfC, hwfA₃⟩ := type_pack_inversion hty₁
    injection heq with heq
    subst heq
    rw [shiftCtx_empty, type_wf_closed_rename A _ hwfA] at hty₂
    exact typed_substitutivity hty₁'
      (typed_subst_type_closed' x' A₂ C e₂ A hwfA hwfA₃ hwfC hty₂)
  | unOpS op e₀ v v' h₁ h₂ =>
    obtain ⟨A₁, hop, hty⟩ := unop_inversion ht
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
  | binOpS op e₁ e₂ v₁ v₂ v' h₁ h₂ h₃ =>
    obtain ⟨A₁, A₂, hop, hty₁, hty₂⟩ := binop_inversion ht
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
  | ifTrueS e₁ e₂ => exact (if_inversion ht).2.1
  | ifFalseS e₁ e₂ => exact (if_inversion ht).2.2
  | fstS e₁ e₂ hv₁ hv₂ =>
    obtain ⟨A₂, hty⟩ := fst_inversion ht
    obtain ⟨A₃, A₄, heq, hty₁, hty₂⟩ := pair_inversion hty
    injection heq with heqA heqB
    subst heqA
    exact hty₁
  | sndS e₁ e₂ hv₁ hv₂ =>
    obtain ⟨A₁, hty⟩ := snd_inversion ht
    obtain ⟨A₃, A₄, heq, hty₁, hty₂⟩ := pair_inversion hty
    injection heq with heqA heqB
    subst heqB
    exact hty₂
  | caseLS e₀ e₁ e₂ hv =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion ht
    obtain ⟨A₃, A₄, heq, hty', hwf⟩ := injl_inversion hty
    injection heq with heqA heqB
    subst heqA
    exact .typed_app 0 _ e₁ e₀ A₁ A hty₁ hty'
  | caseRS e₀ e₁ e₂ hv =>
    obtain ⟨A₁, A₂, hty, hty₁, hty₂⟩ := case_inversion ht
    obtain ⟨A₃, A₄, heq, hty', hwf⟩ := injr_inversion hty
    injection heq with heqA heqB
    subst heqB
    exact .typed_app 0 _ e₂ e₀ A₂ A hty₂ hty'

theorem typed_preservation {e e' : Expr} {A : Ty}
    (ht : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A)
    (hstep : ContextualStep e e') :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e' A := by
  obtain ⟨K, ea, eb, rfl, rfl, hb⟩ := contextual_step_inv hstep
  obtain ⟨B, hB, hK⟩ := fill_typing_decompose ht
  exact hK _ (typed_preservation_base_step hB hb)

/-- A well-typed program never gets stuck. -/
theorem typed_safety {e₁ e₂ : Expr} {A : Ty}
    (ht : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e₁ A)
    (hsteps : ContextualSteps e₁ e₂) : Expr.isVal e₂ ∨ reducible e₂ := by
  induction hsteps with
  | refl => exact typed_progress ht
  | step hstep _ ih => exact ih (typed_preservation ht hstep)

end SystemF
