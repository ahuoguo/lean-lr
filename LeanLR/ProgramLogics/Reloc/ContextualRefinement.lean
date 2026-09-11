import LeanLR.ProgramLogics.Reloc.Adequacy

/-!
# Contextual refinement

`program_logics/reloc/contextual_refinement.v`. A program context is a list of frames with a hole
anywhere — not just in evaluation position — and `ctxRefines` says that whenever the target
terminates in some typed context, so does the source. The logical relation is a precongruence, and
that is what makes it sound for contextual refinement.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std FromMathlib
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation
open Iris.ProgramLogic.PrimStep

namespace ProgramLogics.Reloc

open ProgramLogics.LogRel (Ty TypingContext TyMapStr shiftCtx SynTyped TypeWf BinOpTyped
  UnOpTyped tApp tLam pack unpack roll unroll)

/-! ## Program contexts -/

/-- One frame of a program context. -/
inductive CtxItem where
  | lam (x : Binder)
  | appL (e₂ : Exp)
  | appR (e₁ : Exp)
  | unOp (op : UnOp)
  | binOpL (op : BinOp) (e₂ : Exp)
  | binOpR (op : BinOp) (e₁ : Exp)
  | ifL (e₁ e₂ : Exp)
  | ifM (e₀ e₂ : Exp)
  | ifR (e₀ e₁ : Exp)
  | pairL (e₂ : Exp)
  | pairR (e₁ : Exp)
  | fst
  | snd
  | injL
  | injR
  | caseL (e₁ e₂ : Exp)
  | caseM (e₀ e₂ : Exp)
  | caseR (e₀ e₁ : Exp)
  | alloc
  | load
  | storeL (e₂ : Exp)
  | storeR (e₁ : Exp)
  | roll
  | unroll
  | tLam
  | tApp
  | pack
  | unpackL (x : Binder) (e₂ : Exp)
  | unpackR (x : Binder) (e₁ : Exp)

def fillCtxItem (C : CtxItem) (e : Exp) : Exp :=
  match C with
  | .lam x => .rec_ .anon x e
  | .appL e₂ => .app e e₂
  | .appR e₁ => .app e₁ e
  | .unOp op => .unop op e
  | .binOpL op e₂ => .binop op e e₂
  | .binOpR op e₁ => .binop op e₁ e
  | .ifL e₁ e₂ => .if e e₁ e₂
  | .ifM e₀ e₂ => .if e₀ e e₂
  | .ifR e₀ e₁ => .if e₀ e₁ e
  | .pairL e₂ => .pair e e₂
  | .pairR e₁ => .pair e₁ e
  | .fst => .fst e
  | .snd => .snd e
  | .injL => .injL e
  | .injR => .injR e
  | .caseL e₁ e₂ => .case e e₁ e₂
  | .caseM e₀ e₂ => .case e₀ e e₂
  | .caseR e₀ e₁ => .case e₀ e₁ e
  | .alloc => hl(ref(&e))
  | .load => .load e
  | .storeL e₂ => .store e e₂
  | .storeR e₁ => .store e₁ e
  | .roll => roll e
  | .unroll => unroll e
  | .tLam => tLam e
  | .tApp => tApp e
  | .pack => pack e
  | .unpackL x e₂ => unpack e x e₂
  | .unpackR x e₀ => unpack e₀ x e

/-- A program context: frames applied outermost-last. -/
abbrev Ctx := List CtxItem

def fillCtx (K : Ctx) (e : Exp) : Exp := K.foldr fillCtxItem e

@[simp] theorem fillCtx_nil (e : Exp) : fillCtx [] e = e := rfl

@[simp] theorem fillCtx_cons (C : CtxItem) (K : Ctx) (e : Exp) :
    fillCtx (C :: K) e = fillCtxItem C (fillCtx K e) := rfl

theorem fillCtx_app (K K' : Ctx) (e : Exp) : fillCtx K' (fillCtx K e) = fillCtx (K' ++ K) e :=
  List.foldr_append.symm

/-! ## Typed contexts -/

inductive TypedCtxItem :
    CtxItem → Nat → TypingContext → Ty → Nat → TypingContext → Ty → Prop where
  | tp_lam (n : Nat) (Γ : TypingContext) (A B : Ty) (x : String) :
      TypeWf n A →
      TypedCtxItem (.lam (.named x)) n (insert (M := TyMapStr) Γ x A) B n Γ (.fn A B)
  | tp_lam_anon (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n A →
      TypedCtxItem (.lam .anon) n Γ B n Γ (.fn A B)
  | tp_appL (n : Nat) (Γ : TypingContext) (e₂ : Exp) (A B : Ty) :
      SynTyped n Γ e₂ A →
      TypedCtxItem (.appL e₂) n Γ (.fn A B) n Γ B
  | tp_appR (n : Nat) (Γ : TypingContext) (e₁ : Exp) (A B : Ty) :
      SynTyped n Γ e₁ (.fn A B) →
      TypedCtxItem (.appR e₁) n Γ A n Γ B
  | tp_unOp (op : UnOp) (n : Nat) (Γ : TypingContext) (A B : Ty) :
      UnOpTyped op A B →
      TypedCtxItem (.unOp op) n Γ A n Γ B
  | tp_binOpL (op : BinOp) (n : Nat) (Γ : TypingContext) (e₂ : Exp) (A B C : Ty) :
      SynTyped n Γ e₂ B → BinOpTyped op A B C →
      TypedCtxItem (.binOpL op e₂) n Γ A n Γ C
  | tp_binOpR (op : BinOp) (e₁ : Exp) (n : Nat) (Γ : TypingContext) (A B C : Ty) :
      SynTyped n Γ e₁ A → BinOpTyped op A B C →
      TypedCtxItem (.binOpR op e₁) n Γ B n Γ C
  | tp_ifL (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (A : Ty) :
      SynTyped n Γ e₁ A → SynTyped n Γ e₂ A →
      TypedCtxItem (.ifL e₁ e₂) n Γ .bool n Γ A
  | tp_ifM (n : Nat) (Γ : TypingContext) (e₀ e₂ : Exp) (A : Ty) :
      SynTyped n Γ e₀ .bool → SynTyped n Γ e₂ A →
      TypedCtxItem (.ifM e₀ e₂) n Γ A n Γ A
  | tp_ifR (n : Nat) (Γ : TypingContext) (e₀ e₁ : Exp) (A : Ty) :
      SynTyped n Γ e₀ .bool → SynTyped n Γ e₁ A →
      TypedCtxItem (.ifR e₀ e₁) n Γ A n Γ A
  | tp_pairL (n : Nat) (Γ : TypingContext) (e₂ : Exp) (A B : Ty) :
      SynTyped n Γ e₂ B →
      TypedCtxItem (.pairL e₂) n Γ A n Γ (.prod A B)
  | tp_pairR (n : Nat) (Γ : TypingContext) (e₁ : Exp) (A B : Ty) :
      SynTyped n Γ e₁ A →
      TypedCtxItem (.pairR e₁) n Γ B n Γ (.prod A B)
  | tp_fst (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypedCtxItem .fst n Γ (.prod A B) n Γ A
  | tp_snd (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypedCtxItem .snd n Γ (.prod A B) n Γ B
  | tp_injL (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n B →
      TypedCtxItem .injL n Γ A n Γ (.sum A B)
  | tp_injR (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n A →
      TypedCtxItem .injR n Γ B n Γ (.sum A B)
  | tp_caseL (n : Nat) (Γ : TypingContext) (e₁ e₂ : Exp) (A B C : Ty) :
      SynTyped n Γ e₁ (.fn A C) → SynTyped n Γ e₂ (.fn B C) →
      TypedCtxItem (.caseL e₁ e₂) n Γ (.sum A B) n Γ C
  | tp_caseM (n : Nat) (Γ : TypingContext) (e₀ e₂ : Exp) (A B C : Ty) :
      SynTyped n Γ e₀ (.sum A B) → SynTyped n Γ e₂ (.fn B C) →
      TypedCtxItem (.caseM e₀ e₂) n Γ (.fn A C) n Γ C
  | tp_caseR (n : Nat) (Γ : TypingContext) (e₀ e₁ : Exp) (A B C : Ty) :
      SynTyped n Γ e₀ (.sum A B) → SynTyped n Γ e₁ (.fn A C) →
      TypedCtxItem (.caseR e₀ e₁) n Γ (.fn B C) n Γ C
  | tp_alloc (n : Nat) (Γ : TypingContext) (A : Ty) :
      TypedCtxItem .alloc n Γ A n Γ (.ref A)
  | tp_load (n : Nat) (Γ : TypingContext) (A : Ty) :
      TypedCtxItem .load n Γ (.ref A) n Γ A
  | tp_storeL (n : Nat) (Γ : TypingContext) (e₂ : Exp) (A : Ty) :
      SynTyped n Γ e₂ A →
      TypedCtxItem (.storeL e₂) n Γ (.ref A) n Γ .unit
  | tp_storeR (n : Nat) (Γ : TypingContext) (e₁ : Exp) (A : Ty) :
      SynTyped n Γ e₁ (.ref A) →
      TypedCtxItem (.storeR e₁) n Γ A n Γ .unit
  | tp_roll (n : Nat) (Γ : TypingContext) (A : Ty) :
      TypedCtxItem .roll n Γ (A.subst1 (.mu A)) n Γ (.mu A)
  | tp_unroll (n : Nat) (Γ : TypingContext) (A : Ty) :
      TypedCtxItem .unroll n Γ (.mu A) n Γ (A.subst1 (.mu A))
  | tp_tLam (n : Nat) (Γ : TypingContext) (A : Ty) :
      TypedCtxItem .tLam (n + 1) (shiftCtx Γ) A n Γ (.all A)
  | tp_tApp (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n B →
      TypedCtxItem .tApp n Γ (.all A) n Γ (A.subst1 B)
  | tp_pack (n : Nat) (Γ : TypingContext) (B C : Ty) :
      TypeWf n C → TypeWf (n + 1) B →
      TypedCtxItem .pack n Γ (B.subst1 C) n Γ (.exist B)
  | tp_unpackL (x : String) (e₂ : Exp) (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n B →
      SynTyped (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x A) e₂ (B.rename (· + 1)) →
      TypedCtxItem (.unpackL (.named x) e₂) n Γ (.exist A) n Γ B
  | tp_unpackR (x : String) (e₁ : Exp) (n : Nat) (Γ : TypingContext) (A B : Ty) :
      TypeWf n B →
      SynTyped n Γ e₁ (.exist A) →
      TypedCtxItem (.unpackR (.named x) e₁) (n + 1)
        (insert (M := TyMapStr) (shiftCtx Γ) x A) (B.rename (· + 1)) n Γ B

inductive TypedCtx : Ctx → Nat → TypingContext → Ty → Nat → TypingContext → Ty → Prop where
  | nil (n : Nat) (Γ : TypingContext) (A : Ty) : TypedCtx [] n Γ A n Γ A
  | cons (n₁ : Nat) (Γ₁ : TypingContext) (A : Ty) (n₂ : Nat) (Γ₂ : TypingContext) (B : Ty)
      (n₃ : Nat) (Γ₃ : TypingContext) (C : Ty) (k : CtxItem) (K : Ctx) :
      TypedCtxItem k n₂ Γ₂ B n₃ Γ₃ C →
      TypedCtx K n₁ Γ₁ A n₂ Γ₂ B →
      TypedCtx (k :: K) n₁ Γ₁ A n₃ Γ₃ C

theorem typed_ctx_item_typed {k : CtxItem} {n : Nat} {Γ : TypingContext} {A : Ty}
    {n' : Nat} {Γ' : TypingContext} {B : Ty} {e : Exp}
    (he : SynTyped n Γ e A) (hk : TypedCtxItem k n Γ A n' Γ' B) :
    SynTyped n' Γ' (fillCtxItem k e) B := by
  cases hk with
  | tp_lam _ _ _ _ x hA => exact .typed_lam _ _ x _ _ _ he hA
  | tp_lam_anon _ _ _ _ hA => exact .typed_lam_anon _ _ _ _ _ he hA
  | tp_appL _ _ _ _ _ h₂ => exact .typed_app _ _ _ _ _ _ he h₂
  | tp_appR _ _ _ _ _ h₁ => exact .typed_app _ _ _ _ _ _ h₁ he
  | tp_unOp _ _ _ _ _ hop => exact .typed_unop _ _ _ _ _ _ hop he
  | tp_binOpL _ _ _ _ _ _ _ h₂ hop => exact .typed_binop _ _ _ _ _ _ _ _ hop he h₂
  | tp_binOpR _ _ _ _ _ _ _ h₁ hop => exact .typed_binop _ _ _ _ _ _ _ _ hop h₁ he
  | tp_ifL _ _ _ _ _ h₁ h₂ => exact .typed_if _ _ _ _ _ _ he h₁ h₂
  | tp_ifM _ _ _ _ _ h₀ h₂ => exact .typed_if _ _ _ _ _ _ h₀ he h₂
  | tp_ifR _ _ _ _ _ h₀ h₁ => exact .typed_if _ _ _ _ _ _ h₀ h₁ he
  | tp_pairL _ _ _ _ _ h₂ => exact .typed_pair _ _ _ _ _ _ he h₂
  | tp_pairR _ _ _ _ _ h₁ => exact .typed_pair _ _ _ _ _ _ h₁ he
  | tp_fst => exact .typed_fst _ _ _ _ _ he
  | tp_snd => exact .typed_snd _ _ _ _ _ he
  | tp_injL _ _ _ _ hB => exact .typed_injl _ _ _ _ _ hB he
  | tp_injR _ _ _ _ hA => exact .typed_injr _ _ _ _ _ hA he
  | tp_caseL _ _ _ _ _ _ _ h₁ h₂ => exact .typed_case _ _ _ _ _ _ _ _ he h₁ h₂
  | tp_caseM _ _ _ _ _ _ _ h₀ h₂ => exact .typed_case _ _ _ _ _ _ _ _ h₀ he h₂
  | tp_caseR _ _ _ _ _ _ _ h₀ h₁ => exact .typed_case _ _ _ _ _ _ _ _ h₀ h₁ he
  | tp_alloc => exact .typed_new _ _ _ _ he
  | tp_load => exact .typed_load _ _ _ _ he
  | tp_storeL _ _ _ _ h₂ => exact .typed_store _ _ _ _ _ he h₂
  | tp_storeR _ _ _ _ h₁ => exact .typed_store _ _ _ _ _ h₁ he
  | tp_roll => exact .typed_roll _ _ _ _ he
  | tp_unroll => exact .typed_unroll _ _ _ _ he
  | tp_tLam => exact .typed_tlam _ _ _ _ he
  | tp_tApp _ _ _ B hB => exact .typed_tapp _ _ _ B _ he hB
  | tp_pack _ _ _ C hC hB => exact .typed_pack _ _ _ C _ hC hB he
  | tp_unpackL x _ _ _ _ _ hB h₂ => exact .typed_unpack _ _ _ _ _ _ x hB he h₂
  | tp_unpackR x _ _ _ _ _ hB h₁ => exact .typed_unpack _ _ _ _ _ _ x hB h₁ he

theorem typed_ctx_typed {K : Ctx} {n : Nat} {Γ : TypingContext} {A : Ty}
    {n' : Nat} {Γ' : TypingContext} {B : Ty} {e : Exp}
    (he : SynTyped n Γ e A) (hK : TypedCtx K n Γ A n' Γ' B) :
    SynTyped n' Γ' (fillCtx K e) B := by
  induction hK with
  | nil => exact he
  | cons _ _ _ _ _ _ _ _ _ _ _ hk _ ih => exact typed_ctx_item_typed (ih he) hk

theorem typed_ctx_compose {K K' : Ctx} {n₁ n₂ n₃ : Nat} {Γ₁ Γ₂ Γ₃ : TypingContext} {A B C : Ty}
    (hK : TypedCtx K n₁ Γ₁ A n₂ Γ₂ B) (hK' : TypedCtx K' n₂ Γ₂ B n₃ Γ₃ C) :
    TypedCtx (K' ++ K) n₁ Γ₁ A n₃ Γ₃ C := by
  induction hK' with
  | nil => exact hK
  | cons _ _ _ _ _ _ _ _ _ k _ hk _ ih => exact .cons _ _ _ _ _ _ _ _ _ k _ hk (ih hK)

/-! ## Contextual refinement -/

/-- If the target terminates with a value in a typed context, so does the source. -/
def ctxRefines (n : Nat) (Γ : TypingContext) (e e' : Exp) (A : Ty) : Prop :=
  ∀ (K : Ctx) (σ₀ σ₁ : State) (v₁ : Val) (B : Ty),
    σ₀ = mkstate σ₀.heap →
    TypedCtx K n Γ A 0 ∅ B →
    Relation.ReflTransGen ThreadStep (fillCtx K e, σ₀) (hl(v(&v₁)), σ₁) →
    ∃ (v₂ : Val) (σ₁' : State),
      Relation.ReflTransGen ThreadStep (fillCtx K e', σ₀) (hl(v(&v₂)), σ₁')

theorem ctxRefines_refl {n : Nat} {Γ : TypingContext} {A : Ty} (e : Exp) :
    ctxRefines n Γ e e A := fun _ _ _ _ _ _ _ hst => ⟨_, _, hst⟩

theorem ctxRefines_trans {n : Nat} {Γ : TypingContext} {A : Ty} {e₁ e₂ e₃ : Exp}
    (h₁ : ctxRefines n Γ e₁ e₂ A) (h₂ : ctxRefines n Γ e₂ e₃ A) : ctxRefines n Γ e₁ e₃ A := by
  intro K σ₀ σ₁ v₁ B hσ hK hst
  obtain ⟨v₂, σ₁', hst'⟩ := h₁ K σ₀ σ₁ v₁ B hσ hK hst
  exact h₂ K σ₀ σ₁' v₂ B hσ hK hst'

theorem ctxRefines_congruence {n : Nat} {Γ : TypingContext} {e₁ e₂ : Exp} {A : Ty}
    {n' : Nat} {Γ' : TypingContext} {B : Ty} {K : Ctx}
    (hK : TypedCtx K n Γ A n' Γ' B) (h : ctxRefines n Γ e₁ e₂ A) :
    ctxRefines n' Γ' (fillCtx K e₁) (fillCtx K e₂) B := by
  intro K' σ₀ σ₁ v C hσ hK' hst
  rw [fillCtx_app] at hst ⊢
  exact h (K' ++ K) σ₀ σ₁ v C hσ (typed_ctx_compose hK hK') hst

/-! ## The logical relation is a precongruence -/

section LogRelCtx

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

theorem log_related_under_typed_ctx {K : Ctx} {n : Nat} {Γ : TypingContext} {A : Ty}
    {n' : Nat} {Γ' : TypingContext} {B : Ty} {e e' : Exp}
    (hK : TypedCtx K n Γ A n' Γ' B) (h : semTyped GF n Γ e e' A) :
    semTyped GF n' Γ' (fillCtx K e) (fillCtx K e') B := by
  induction hK with
  | nil => exact h
  | cons _ _ _ _ _ _ _ _ _ k _ hk _ ih =>
    have ihh := ih h
    cases hk with
    | tp_lam _ _ _ _ x hA => exact compat_lambda x ihh
    | tp_lam_anon => exact compat_lambda_anon ihh
    | tp_appL _ _ _ _ _ h₂ => exact compat_beta ihh (fundamental h₂)
    | tp_appR _ _ _ _ _ h₁ => exact compat_beta (fundamental h₁) ihh
    | tp_unOp _ _ _ _ _ hop => exact compat_unop hop ihh
    | tp_binOpL _ _ _ _ _ _ _ h₂ hop => exact compat_binop hop ihh (fundamental h₂)
    | tp_binOpR _ _ _ _ _ _ _ h₁ hop => exact compat_binop hop (fundamental h₁) ihh
    | tp_ifL _ _ _ _ _ h₁ h₂ => exact compat_if ihh (fundamental h₁) (fundamental h₂)
    | tp_ifM _ _ _ _ _ h₀ h₂ => exact compat_if (fundamental h₀) ihh (fundamental h₂)
    | tp_ifR _ _ _ _ _ h₀ h₁ => exact compat_if (fundamental h₀) (fundamental h₁) ihh
    | tp_pairL _ _ _ _ _ h₂ => exact compat_pair ihh (fundamental h₂)
    | tp_pairR _ _ _ _ _ h₁ => exact compat_pair (fundamental h₁) ihh
    | tp_fst => exact compat_fst ihh
    | tp_snd => exact compat_snd ihh
    | tp_injL => exact compat_injl ihh
    | tp_injR => exact compat_injr ihh
    | tp_caseL _ _ _ _ _ _ _ h₁ h₂ => exact compat_case ihh (fundamental h₁) (fundamental h₂)
    | tp_caseM _ _ _ _ _ _ _ h₀ h₂ => exact compat_case (fundamental h₀) ihh (fundamental h₂)
    | tp_caseR _ _ _ _ _ _ _ h₀ h₁ => exact compat_case (fundamental h₀) (fundamental h₁) ihh
    | tp_alloc => exact compat_new ihh
    | tp_load => exact compat_load ihh
    | tp_storeL _ _ _ _ h₂ => exact compat_store ihh (fundamental h₂)
    | tp_storeR _ _ _ _ h₁ => exact compat_store (fundamental h₁) ihh
    | tp_roll => exact compat_roll ihh
    | tp_unroll => exact compat_unroll ihh
    | tp_tLam => exact compat_tlam ihh
    | tp_tApp _ _ _ C _ => exact compat_tapp C ihh
    | tp_pack _ _ _ C _ _ => exact compat_pack C ihh
    | tp_unpackL x _ _ _ _ _ _ h₂ => exact compat_unpack x ihh (fundamental h₂)
    | tp_unpackR x _ _ _ _ _ _ h₁ => exact compat_unpack x (fundamental h₁) ihh

end LogRelCtx

/-! ## Observable types

Exactly the types at which the relation forces the two values to be equal. -/

inductive ObsType : Ty → Prop where
  | obs_int : ObsType .int
  | obs_bool : ObsType .bool
  | obs_unit : ObsType .unit
  | obs_prod (A₁ A₂ : Ty) : ObsType A₁ → ObsType A₂ → ObsType (.prod A₁ A₂)
  | obs_sum (A₁ A₂ : Ty) : ObsType A₁ → ObsType A₂ → ObsType (.sum A₁ A₂)

section Obs

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

theorem ObsType_soundness {A : Ty} (h : ObsType A) (δ : Env GF) (v v' : Val) :
    typeInterp A δ v v' ⊢ iprop(⌜v = v'⌝) := by
  induction h generalizing v v' with
  | obs_int =>
    simp only [typeInterp_int, intInterp_car]
    iintro ⟨%z, %ha, %hb⟩
    ipureintro
    rw [ha, hb]
  | obs_bool =>
    simp only [typeInterp_bool, boolInterp_car]
    iintro ⟨%b, %ha, %hb⟩
    ipureintro
    rw [ha, hb]
  | obs_unit =>
    simp only [typeInterp_unit, unitInterp_car]
    iintro ⟨%ha, %hb⟩
    ipureintro
    rw [ha, hb]
  | obs_prod A₁ A₂ _ _ ih₁ ih₂ =>
    simp only [typeInterp_prod, prodInterp_car]
    iintro ⟨%w₁, %w₁', %w₂, %w₂', %ha, %hb, H₁, H₂⟩
    icases ih₁ w₁ w₁' $$ H₁ with %h₁
    icases ih₂ w₂ w₂' $$ H₂ with %h₂
    ipureintro
    rw [ha, hb, h₁, h₂]
  | obs_sum A₁ A₂ _ _ ih₁ ih₂ =>
    simp only [typeInterp_sum, sumInterp_car]
    iintro ⟨⟨%w, %w', %ha, %hb, H⟩ | ⟨%w, %w', %ha, %hb, H⟩⟩
    · icases ih₁ w w' $$ H with %hw
      ipureintro
      rw [ha, hb, hw]
    · icases ih₂ w w' $$ H with %hw
      ipureintro
      rw [ha, hb, hw]

/-- The environment mapping every type variable to the empty relation. -/
def trivialEnv : Env GF := fun _ => mkSemType (fun _ _ => iprop(False)) (fun _ _ => inferInstance)

end Obs

/-! ## Soundness -/

section Soundness

variable {GF : BundledGFunctors}

theorem logrel_adequate [RelocGpreS .hasLC GF] (e e' : Exp) (n : Nat) (A : Ty) (σ : State)
    (hσ : σ = mkstate σ.heap)
    (Hlog : ∀ [_inst : RelocGS .hasLC GF], semTyped GF n ∅ e e' A)
    (Hnf : ∀ (t₂ : List Exp) (σ₂ : State), ([e], σ) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1) :
    AdequateNoFork .NotStuck e σ (fun v _ => ∃ (v' : Val) (h : State),
      Relation.ReflTransGen ThreadStep (e', σ) (hl(v(&v')), h) ∧ (ObsType A → v = v')) := by
  refine refines_adequate (GF := GF) (fun _ => typeInterp A trivialEnv) _ e e' σ hσ ?_ ?_ Hnf
  · intro _inst v v'
    by_cases hobs : ObsType A
    · exact (ObsType_soundness hobs trivialEnv v v').trans (BI.pure_mono fun heq _ => heq)
    · exact BI.pure_intro fun hc => absurd hc hobs
  · intro _inst
    have H := (contextInterp_empty (GF := GF) trivialEnv).trans
      (semTyped_apply Hlog trivialEnv (∅ : TyMapStr (Val × Val)))
    rw [LawfulPartialMap.map_empty (M := TyMapStr) (f := (Prod.fst : Val × Val → Val)),
      LawfulPartialMap.map_empty (M := TyMapStr) (f := (Prod.snd : Val × Val → Val)),
      Exp.substMap_empty (M := TyMapStr), Exp.substMap_empty (M := TyMapStr)] at H
    exact H

theorem logrel_typesafety [RelocGpreS .hasLC GF] (e e' e₁ : Exp) (n : Nat) (A : Ty)
    (σ σ' : State) (hσ : σ = mkstate σ.heap)
    (Hlog : ∀ [_inst : RelocGS .hasLC GF], semTyped GF n ∅ e e' A)
    (Hnf : ∀ (t₂ : List Exp) (σ₂ : State), ([e], σ) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1)
    (Hsteps : Relation.ReflTransGen ThreadStep (e, σ) (e₁, σ')) : NotStuck (e₁, σ') :=
  (logrel_adequate (GF := GF) e e' n A σ hσ Hlog Hnf).not_stuck rfl
    (rtc_thread_erased_step Hsteps) (List.mem_singleton_self _)

theorem logrel_simul [RelocGpreS .hasLC GF] (e e' : Exp) (n : Nat) (A : Ty) (v : Val)
    (h : State) (σ : State) (hσ : σ = mkstate σ.heap)
    (Hlog : ∀ [_inst : RelocGS .hasLC GF], semTyped GF n ∅ e e' A)
    (Hnf : ∀ (t₂ : List Exp) (σ₂ : State), ([e], σ) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1)
    (Hsteps : Relation.ReflTransGen ThreadStep (e, σ) (hl(v(&v)), h)) :
    ∃ (v' : Val) (h' : State),
      Relation.ReflTransGen ThreadStep (e', σ) (hl(v(&v')), h') ∧ (ObsType A → v = v') :=
  (logrel_adequate (GF := GF) e e' n A σ hσ Hlog Hnf).result (rtc_thread_erased_step Hsteps)

theorem refines_sound_open [RelocGpreS .hasLC GF] {n : Nat} {Γ : TypingContext} {e e' : Exp}
    {A : Ty} (Hlog : ∀ [_inst : RelocGS .hasLC GF], semTyped GF n Γ e e' A)
    (Hnf : ∀ (K : Ctx) (σ₀ : State) (t₂ : List Exp) (σ₂ : State),
      ([fillCtx K e], σ₀) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1) :
    ctxRefines n Γ e e' A := by
  intro K σ₀ σ₁ v₁ B hσ hK hst
  obtain ⟨v₂, σ₁', hst', _⟩ :=
    logrel_simul (GF := GF) (fillCtx K e) (fillCtx K e') 0 B v₁ σ₁ σ₀ hσ
      (fun {_inst} => log_related_under_typed_ctx hK Hlog) (Hnf K σ₀) hst
  exact ⟨v₂, σ₁', hst'⟩

theorem refines_sound [RelocGpreS .hasLC GF] {n : Nat} {e e' : Exp} {A : Ty}
    (Hlog : ∀ [_inst : RelocGS .hasLC GF] (δ : Env GF), ⊢ refines e e' (typeInterp A δ).car)
    (Hnf : ∀ (K : Ctx) (σ₀ : State) (t₂ : List Exp) (σ₂ : State),
      ([fillCtx K e], σ₀) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1) :
    ctxRefines n ∅ e e' A := by
  refine refines_sound_open (GF := GF) ?_ Hnf
  intro _inst
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [LawfulPartialMap.map_empty (M := TyMapStr) (f := (Prod.fst : Val × Val → Val)),
    LawfulPartialMap.map_empty (M := TyMapStr) (f := (Prod.snd : Val × Val → Val)),
    Exp.substMap_empty (M := TyMapStr), Exp.substMap_empty (M := TyMapStr)]
  ihave H := (Hlog δ)
  iexact H

/-- A concrete bundle of functors for the binary relation: `HeapLangS` plus a ghost variable for
the source expression. The source heap reuses `HeapLangS`'s heap-view slot, with its own name. -/
def RelocS : BundledGFunctors
  | 8 => ⟨GhostVarF Exp, by infer_instance⟩
  | n => HeapLangS n

instance instRelocGpreS_RelocS : RelocGpreS HasLC.hasLC RelocS where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6
  proph_pre := by
    constructor
    · constructor
      exists 7
  sheap_pre := by
    constructor
    exists 4
  sexpr_pre := @Iris.GhostVarG.mk _ _ ⟨8, rfl⟩

/-- Safety of the syntactically typed fragment, read off reflexivity of the relation. -/
theorem F_mu_ref_typesafety {e e' : Exp} {σ σ' : State} {n : Nat} {A : Ty}
    (hσ : σ = mkstate σ.heap) (h : SynTyped n ∅ e A)
    (Hnf : ∀ (t₂ : List Exp) (σ₂ : State), ([e], σ) -·->ₜₚ* (t₂, σ₂) → t₂.length = 1)
    (Hsteps : Relation.ReflTransGen ThreadStep (e, σ) (e', σ')) : NotStuck (e', σ') :=
  logrel_typesafety (GF := RelocS) e e e' n A σ σ' hσ (fun {_inst} => fundamental h) Hnf Hsteps

end Soundness

end ProgramLogics.Reloc
