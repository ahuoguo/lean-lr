import LeanLR.ProgramLogics.Reloc.LogRel
import LeanLR.ProgramLogics.LogRel.Syntactic
import Iris.HeapLang.Metatheory

/-!
# The fundamental theorem of the binary logical relation

`program_logics/reloc/fundamental.v`: the interpretation of a type as a relation, the context
relation, the substitution lemmas, one compatibility lemma per typing rule, and reflexivity of
the relation for syntactically typed terms.
-/

open Iris Iris.BI Iris.OFE Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage

namespace ProgramLogics.Reloc

open ProgramLogics.LogRel (Ty TypingContext TyMapStr shiftCtx SynTyped BinOpTyped UnOpTyped
  tApp tLamV tLam pack packV unpack roll rollV unroll)

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

/-! ## The interpretation of a type

As in the unary relation, the `μ` case needs its own non-expansiveness in order to build the
fixpoint, so the two are defined together. -/

def typeInterpAux : Ty → { σ : Env GF → SemType GF // NonExpansive σ }
  | .tVar x => ⟨varInterp x, ⟨fun {_ _ _} h => h x⟩⟩
  | .int => ⟨intInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .bool => ⟨boolInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .unit => ⟨unitInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .fn A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨funInterp p.1 q.1, ⟨fun {_ _ _} h v v' => by
      refine BI.forall_ne fun w => BI.forall_ne fun w' => BI.intuitionistically_ne.ne ?_
      exact BI.wand_ne.ne (p.2.ne h w w') (refines_ne fun u u' => q.2.ne h u u')⟩⟩
  | .all A =>
    let p := typeInterpAux A
    ⟨allInterp p.1, ⟨fun {_ _ _} h v v' => by
      refine BI.intuitionistically_ne.ne (BI.forall_ne fun τ => ?_)
      exact refines_ne fun u u' => p.2.ne (consEnv_ne .rfl h) u u'⟩⟩
  | .exist A =>
    let p := typeInterpAux A
    ⟨existInterp p.1, ⟨fun {_ _ _} h v v' => by
      refine BI.exists_ne fun w => BI.exists_ne fun w' => BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne .rfl (BI.exists_ne fun τ => ?_)
      exact p.2.ne (consEnv_ne .rfl h) w w'⟩⟩
  | .mu A =>
    let p := typeInterpAux A
    ⟨fun δ => @Iris.fixpoint _ _ _ (muRec p.1 δ) (muRec_contractive p.1 p.2 δ),
      ⟨fun {_ δ δ'} h => by
        refine @Iris.fixpoint_dist _ _ _ _ _ (muRec_contractive p.1 p.2 δ)
          (muRec_contractive p.1 p.2 δ') _ fun ρ v v' => ?_
        refine BI.exists_ne fun w => BI.exists_ne fun w' => BI.sep_ne.ne .rfl ?_
        refine BI.sep_ne.ne .rfl (BI.later_ne.ne ?_)
        exact p.2.ne (consEnv_ne .rfl h) w w'⟩⟩
  | .ref A =>
    let p := typeInterpAux A
    ⟨refInterp p.1, ⟨fun {_ _ _} h v v' => by
      refine BI.exists_ne fun l => BI.exists_ne fun l' => BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne .rfl ((Iris.inv_ne logN).ne ?_)
      refine BI.exists_ne fun w => BI.exists_ne fun w' => BI.sep_ne.ne .rfl ?_
      exact BI.sep_ne.ne .rfl (p.2.ne h w w')⟩⟩
  | .prod A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨prodInterp p.1 q.1, ⟨fun {_ _ _} h v v' => by
      refine BI.exists_ne fun w₁ => BI.exists_ne fun w₁' => BI.exists_ne fun w₂ =>
        BI.exists_ne fun w₂' => BI.sep_ne.ne .rfl (BI.sep_ne.ne .rfl ?_)
      exact BI.sep_ne.ne (p.2.ne h w₁ w₁') (q.2.ne h w₂ w₂')⟩⟩
  | .sum A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨sumInterp p.1 q.1, ⟨fun {_ _ _} h v v' => by
      refine BI.or_ne.ne ?_ ?_
      · exact BI.exists_ne fun w => BI.exists_ne fun w' =>
          BI.sep_ne.ne .rfl (BI.sep_ne.ne .rfl (p.2.ne h w w'))
      · exact BI.exists_ne fun w => BI.exists_ne fun w' =>
          BI.sep_ne.ne .rfl (BI.sep_ne.ne .rfl (q.2.ne h w w'))⟩⟩

/-- Rocq's `𝒱`. -/
def typeInterp (A : Ty) : Env GF → SemType GF := (typeInterpAux A).1

instance typeInterp_ne (A : Ty) : NonExpansive (typeInterp (GF := GF) A) := (typeInterpAux A).2

@[simp] theorem typeInterp_tVar (x : Nat) :
    typeInterp (GF := GF) (.tVar x) = varInterp x := rfl
@[simp] theorem typeInterp_int : typeInterp (GF := GF) .int = intInterp := rfl
@[simp] theorem typeInterp_bool : typeInterp (GF := GF) .bool = boolInterp := rfl
@[simp] theorem typeInterp_unit : typeInterp (GF := GF) .unit = unitInterp := rfl
@[simp] theorem typeInterp_fn (A B : Ty) :
    typeInterp (GF := GF) (.fn A B) = funInterp (typeInterp A) (typeInterp B) := rfl
@[simp] theorem typeInterp_all (A : Ty) :
    typeInterp (GF := GF) (.all A) = allInterp (typeInterp A) := rfl
@[simp] theorem typeInterp_exist (A : Ty) :
    typeInterp (GF := GF) (.exist A) = existInterp (typeInterp A) := rfl
@[simp] theorem typeInterp_ref (A : Ty) :
    typeInterp (GF := GF) (.ref A) = refInterp (typeInterp A) := rfl
@[simp] theorem typeInterp_prod (A B : Ty) :
    typeInterp (GF := GF) (.prod A B) = prodInterp (typeInterp A) (typeInterp B) := rfl
@[simp] theorem typeInterp_sum (A B : Ty) :
    typeInterp (GF := GF) (.sum A B) = sumInterp (typeInterp A) (typeInterp B) := rfl
theorem typeInterp_mu (A : Ty) (δ : Env GF) :
    typeInterp (.mu A) δ =
      @Iris.fixpoint _ _ _ (muRec (typeInterp A) δ)
        (muRec_contractive _ (typeInterp_ne A) δ) := rfl

/-- The unfolding equation for a recursive type. -/
theorem typeInterp_mu_unfold (A : Ty) (δ : Env GF) :
    typeInterp (.mu A) δ = muRec (typeInterp A) δ (typeInterp (.mu A) δ) := by
  letI := muRec_contractive (typeInterp (GF := GF) A) (typeInterp_ne A) δ
  exact Iris.fixpoint_unfold (Function.toContractiveHom (muRec (typeInterp A) δ))

/-! ## Moving substitutions through the interpretation -/

theorem typeInterp_ext (B : Ty) (δ δ' : Env GF) (h : ∀ n, δ n = δ' n) :
    typeInterp B δ = typeInterp B δ' := by rw [funext h]

private theorem consEnv_comp_up (τ : SemType GF) (δ : Env GF) (f : Nat → Nat) :
    (fun n => (τ .:: δ) (match n with | 0 => 0 | n + 1 => f n + 1)) = (τ .:: fun n => δ (f n)) := by
  funext n; cases n <;> rfl

theorem typeInterp_move_ren (B : Ty) : ∀ (δ : Env GF) (f : Nat → Nat),
    typeInterp B (fun n => δ (f n)) = typeInterp (B.rename f) δ := by
  induction B with
  | tVar x => intro _ _; rfl
  | int | bool | unit => intro _ _; rfl
  | fn A B ihA ihB =>
    intro δ f
    simp only [Ty.rename, typeInterp_fn, funInterp, ihA, ihB]
  | ref A ih =>
    intro δ f
    simp only [Ty.rename, typeInterp_ref, refInterp, ih]
  | prod A B ihA ihB =>
    intro δ f
    simp only [Ty.rename, typeInterp_prod, prodInterp, ihA, ihB]
  | sum A B ihA ihB =>
    intro δ f
    simp only [Ty.rename, typeInterp_sum, sumInterp, ihA, ihB]
  | all A ih =>
    intro δ f
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => δ (f n))
        = typeInterp (A.rename (fun n => match n with | 0 => 0 | n + 1 => f n + 1)) (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_up]
    simp only [Ty.rename, typeInterp_all, allInterp, h]
    try rfl
  | exist A ih =>
    intro δ f
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => δ (f n))
        = typeInterp (A.rename (fun n => match n with | 0 => 0 | n + 1 => f n + 1)) (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_up]
    simp only [Ty.rename, typeInterp_exist, existInterp, h]
    try rfl
  | mu A ih =>
    intro δ f
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => δ (f n))
        = typeInterp (A.rename (fun n => match n with | 0 => 0 | n + 1 => f n + 1)) (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_up]
    simp only [Ty.rename]
    rw [typeInterp_mu, typeInterp_mu]
    refine @Iris.fixpoint_proper _ _ _ _ _
      (muRec_contractive _ (typeInterp_ne A) _) (muRec_contractive _ (typeInterp_ne _) _)
      fun ρ => ?_
    simp only [muRec, h ρ]
    rfl

private theorem consEnv_comp_upSubst (τ : SemType GF) (δ : Env GF) (σ : Nat → Ty) :
    (fun n => typeInterp (GF := GF)
        (match n with | 0 => Ty.tVar 0 | n + 1 => (σ n).rename (· + 1)) (τ .:: δ))
      = (τ .:: fun n => typeInterp (σ n) δ) := by
  funext n
  cases n with
  | zero => rfl
  | succ m =>
    show typeInterp ((σ m).rename (· + 1)) (τ .:: δ) = typeInterp (σ m) δ
    rw [← typeInterp_move_ren]
    rfl

theorem typeInterp_move_subst (B : Ty) : ∀ (δ : Env GF) (σ : Nat → Ty),
    typeInterp B (fun n => typeInterp (σ n) δ) = typeInterp (B.substTy σ) δ := by
  induction B with
  | tVar x => intro _ _; rfl
  | int | bool | unit => intro _ _; rfl
  | fn A B ihA ihB =>
    intro δ σ
    simp only [Ty.substTy, typeInterp_fn, funInterp, ihA, ihB]
  | ref A ih =>
    intro δ σ
    simp only [Ty.substTy, typeInterp_ref, refInterp, ih]
  | prod A B ihA ihB =>
    intro δ σ
    simp only [Ty.substTy, typeInterp_prod, prodInterp, ihA, ihB]
  | sum A B ihA ihB =>
    intro δ σ
    simp only [Ty.substTy, typeInterp_sum, sumInterp, ihA, ihB]
  | all A ih =>
    intro δ σ
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => typeInterp (σ n) δ)
        = typeInterp (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n + 1 => (σ n).rename (· + 1)))
            (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_upSubst]
    simp only [Ty.substTy, typeInterp_all, allInterp, h]
    try rfl
  | exist A ih =>
    intro δ σ
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => typeInterp (σ n) δ)
        = typeInterp (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n + 1 => (σ n).rename (· + 1)))
            (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_upSubst]
    simp only [Ty.substTy, typeInterp_exist, existInterp, h]
    try rfl
  | mu A ih =>
    intro δ σ
    have h : ∀ τ : SemType GF, typeInterp A (τ .:: fun n => typeInterp (σ n) δ)
        = typeInterp (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n + 1 => (σ n).rename (· + 1)))
            (τ .:: δ) := by
      intro τ; rw [← ih (τ .:: δ) _, consEnv_comp_upSubst]
    simp only [Ty.substTy]
    rw [typeInterp_mu, typeInterp_mu]
    refine @Iris.fixpoint_proper _ _ _ _ _
      (muRec_contractive _ (typeInterp_ne A) _) (muRec_contractive _ (typeInterp_ne _) _)
      fun ρ => ?_
    simp only [muRec, h ρ]
    rfl

theorem typeInterp_move_single_subst (A B : Ty) (δ : Env GF) :
    typeInterp B ((typeInterp A δ) .:: δ) = typeInterp (B.subst1 A) δ := by
  rw [Ty.subst1, ← typeInterp_move_subst]
  refine typeInterp_ext B _ _ fun n => ?_
  cases n <;> rfl

theorem typeInterp_cons (A : Ty) (δ : Env GF) (τ : SemType GF) :
    typeInterp A δ = typeInterp (A.rename (· + 1)) (τ .:: δ) := by
  rw [← typeInterp_move_ren]
  rfl

/-! ## The context relation -/

/-- Rocq's `𝒢`: the substitution relates the two programs' free variables. -/
def contextInterp (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF) : IProp GF :=
  iprop([∗map] _x ↦ A;p ∈ Γ;γ, typeInterp A δ p.1 p.2)

instance contextInterp_pers (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF) :
    Persistent (contextInterp (GF := GF) Γ γ δ) := by
  unfold contextInterp; infer_instance

theorem contextInterp_dom_eq (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF) :
    contextInterp (GF := GF) Γ γ δ ⊢ iprop(⌜PartialMap.dom Γ = PartialMap.dom γ⌝) :=
  BigSepM2.bigSepM2_dom _ _ _

theorem contextInterp_empty (δ : Env GF) : ⊢ contextInterp (GF := GF) ∅ ∅ δ :=
  (BigSepM2.bigSepM2_empty _).mpr

/-- The context relation at the empty context pins the substitution down. -/
theorem contextInterp_empty_inv (γ : TyMapStr (Val × Val)) (δ : Env GF) :
    contextInterp (GF := GF) ∅ γ δ ⊢ iprop(⌜γ = ∅⌝) := by
  refine (contextInterp_dom_eq ∅ γ δ).trans (BI.pure_mono fun h => ?_)
  refine LawfulPartialMap.eq_empty_iff.mpr fun k => ?_
  have hk := congrFun h k
  simp only [PartialMap.dom, LawfulPartialMap.get?_empty, Option.isSome_none,
    Bool.false_eq_true, eq_iff_iff, false_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hk
  exact hk

theorem contextInterp_insert (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF)
    (A : Ty) (v v' : Val) (x : String) :
    ⊢@{IProp GF} typeInterp A δ v v' -∗ contextInterp Γ γ δ -∗
      contextInterp (insert (M := TyMapStr) Γ x A) (insert (M := TyMapStr) γ x (v, v')) δ := by
  iintro Hv Hγ
  unfold contextInterp
  iapply BigSepM2.bigSepM2_insert_elim
    (Φ := fun (_ : String) (B : Ty) (p : Val × Val) => typeInterp B δ p.1 p.2)
    (m1 := Γ) (m2 := γ) (i := x) (x1 := A) (x2 := (v, v')) $$ Hv Hγ

theorem contextInterp_lookup' (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF)
    (A : Ty) {x : String} (h : get? (M := TyMapStr) Γ x = some A) :
    contextInterp (GF := GF) Γ γ δ ⊢
      iprop(∃ p : Val × Val, ⌜get? (M := TyMapStr) γ x = some p⌝ ∧ typeInterp A δ p.1 p.2) :=
  BigSepM2.bigSepM2_lookup_left h

theorem contextInterp_lookup (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF)
    (A : Ty) {x : String} (h : get? (M := TyMapStr) Γ x = some A) :
    contextInterp (GF := GF) Γ γ δ ⊢
      iprop(∃ v : Val, ∃ v' : Val,
        ⌜get? (M := TyMapStr) (Iris.Std.PartialMap.map (M := TyMapStr) Prod.fst γ) x = some v⌝ ∗
        ⌜get? (M := TyMapStr) (Iris.Std.PartialMap.map (M := TyMapStr) Prod.snd γ) x = some v'⌝ ∗
        typeInterp A δ v v') := by
  iintro Hγ
  icases contextInterp_lookup' Γ γ δ A h $$ Hγ with ⟨%p, %hp, Hv⟩
  iexists p.1, p.2
  isplitr
  · ipureintro; rw [LawfulPartialMap.get?_map, hp]; rfl
  isplitr
  · ipureintro; rw [LawfulPartialMap.get?_map, hp]; rfl
  · iexact Hv

theorem contextInterp_cons (Γ : TypingContext) (γ : TyMapStr (Val × Val)) (δ : Env GF)
    (τ : SemType GF) : contextInterp Γ γ δ ⊢ contextInterp (shiftCtx Γ) γ (τ .:: δ) := by
  unfold contextInterp shiftCtx
  refine Entails.trans ?_ (BigSepM2.bigSepM2_map_left _ _ _ _).mpr
  refine BigSepM2.bigSepM2_mono fun _ _ => ?_
  rw [typeInterp_cons _ δ τ]

/-! ## Semantic typing -/

/-- Rocq's `TY n; Γ ⊨ e :≤: e' : A`. -/
def semTyped (GF : BundledGFunctors) [RelocGS hlc GF] (_n : Nat) (Γ : TypingContext)
    (e e' : Exp) (A : Ty) : Prop :=
  ⊢ (iprop(∀ δ : Env GF, ∀ γ : TyMapStr (Val × Val), contextInterp Γ γ δ -∗
    refines (e.substMap (Iris.Std.PartialMap.map (M := TyMapStr) Prod.fst γ))
      (e'.substMap (Iris.Std.PartialMap.map (M := TyMapStr) Prod.snd γ))
      (typeInterp A δ).car) : IProp GF)

theorem semTyped_apply {n : Nat} {Γ : TypingContext} {e e' : Exp} {A : Ty}
    (h : semTyped GF n Γ e e' A) (δ : Env GF) (γ : TyMapStr (Val × Val)) :
    contextInterp Γ γ δ ⊢
      refines (e.substMap (Iris.Std.PartialMap.map (M := TyMapStr) Prod.fst γ))
        (e'.substMap (Iris.Std.PartialMap.map (M := TyMapStr) Prod.snd γ))
        (typeInterp A δ).car := by
  unfold semTyped at h
  iintro #Hctx
  ihave H := h
  ispecialize H $$ %δ %γ Hctx
  iexact H

private theorem get?_delete_self {V : Type} {m : TyMapStr V} {x : String} :
    get? (M := TyMapStr) (delete (M := TyMapStr) m x) x = none :=
  LawfulPartialMap.get?_delete_eq rfl

/-! ## Compatibility lemmas -/

section Compat

variable {n : Nat} {Γ : TypingContext} {A B : Ty}

theorem compat_var (x : String) (h : get? (M := TyMapStr) Γ x = some A) :
    semTyped GF n Γ (.var x) (.var x) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_lookup Γ γ δ A h $$ Hctx with ⟨%v, %v', %hv, %hv', Hv⟩
  simp only [Exp.substMap, hv, hv']
  iapply refines_value
  iexact Hv

theorem compat_int (z : Int) : semTyped GF n Γ hl(#z) hl(#z) .int := by
  unfold semTyped
  iintro %δ %γ _
  simp only [Exp.ofVal, Exp.substMap, typeInterp_int]
  iapply refines_value
  simp only [intInterp_car]
  iexists z
  isplitr
  · ipureintro; rfl
  · ipureintro; rfl

theorem compat_bool (b : Bool) : semTyped GF n Γ hl(#b) hl(#b) .bool := by
  unfold semTyped
  iintro %δ %γ _
  simp only [Exp.ofVal, Exp.substMap, typeInterp_bool]
  iapply refines_value
  simp only [boolInterp_car]
  iexists b
  isplitr
  · ipureintro; rfl
  · ipureintro; rfl

theorem compat_unit : semTyped GF n Γ hl(#()) hl(#()) .unit := by
  unfold semTyped
  iintro %δ %γ _
  simp only [Exp.ofVal, Exp.substMap, typeInterp_unit]
  iapply refines_value
  simp only [unitInterp_car]
  isplitr
  · ipureintro; trivial
  · ipureintro; trivial

theorem compat_beta {e₁ e₁' e₂ e₂' : Exp} (h₁ : semTyped GF n Γ e₁ e₁' (.fn A B))
    (h₂ : semTyped GF n Γ e₂ e₂' A) : semTyped GF n Γ (.app e₁ e₂) (.app e₁' e₂') B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_appR
  iapply refines_wand $$ H2
  iintro %v₂ %v₂' Hv₂
  iapply refines_bind_appL v₂ v₂'
  iapply refines_wand $$ H1
  iintro %v₁ %v₁' Hv₁
  simp only [typeInterp_fn, funInterp_car]
  iapply Hv₁ $$ %v₂ %v₂' Hv₂

theorem compat_lambda (x : String) {e e' : Exp}
    (h : semTyped GF n (insert (M := TyMapStr) Γ x A) e e' B) :
    semTyped GF n Γ (.rec_ .anon (.named x) e) (.rec_ .anon (.named x) e') (.fn A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [Exp.substMap, Binder.deleteMap]
  iapply refines_target_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_value
  simp only [typeInterp_fn, funInterp_car]
  iintro %w %w' !> Hw
  iapply refines_target_step (ProgramLogics.pure_step_beta _ _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  rw [← Exp.substMap_insert, ← Exp.substMap_insert,
    ← LawfulPartialMap.map_insert (f := (Prod.fst : Val × Val → Val)) (k := x) (v := (w, w')),
    ← LawfulPartialMap.map_insert (f := (Prod.snd : Val × Val → Val)) (k := x) (v := (w, w'))]
  icases contextInterp_insert Γ γ δ A w w' x $$ Hw Hctx with Hctx'
  icases semTyped_apply h δ (insert (M := TyMapStr) γ x (w, w')) $$ Hctx' with H
  iexact H

theorem compat_lambda_anon {e e' : Exp} (h : semTyped GF n Γ e e' B) :
    semTyped GF n Γ (.rec_ .anon .anon e) (.rec_ .anon .anon e') (.fn A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [Exp.substMap, Binder.deleteMap]
  iapply refines_target_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_value
  simp only [typeInterp_fn, funInterp_car]
  iintro %w %w' !> _
  iapply refines_target_step (ProgramLogics.pure_step_beta _ _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  icases semTyped_apply h δ γ $$ Hctx with H
  iexact H

theorem compat_binop {e₁ e₁' e₂ e₂' : Exp} {C : Ty} {op : BinOp} (hop : BinOpTyped op A B C)
    (h₁ : semTyped GF n Γ e₁ e₁' A) (h₂ : semTyped GF n Γ e₂ e₂' B) :
    semTyped GF n Γ (.binop op e₁ e₂) (.binop op e₁' e₂') C := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_binOpR
  iapply refines_wand $$ H2
  iintro %v₂ %v₂' Hv₂
  iapply refines_bind_binOpL _ v₂ v₂'
  iapply refines_wand $$ H1
  iintro %v₁ %v₁' Hv₁
  cases hop <;>
    simp only [typeInterp_int, typeInterp_bool, intInterp_car] <;>
    icases Hv₁ with ⟨%z₁, %ha₁, %hb₁⟩ <;> icases Hv₂ with ⟨%z₂, %ha₂, %hb₂⟩ <;>
    subst ha₁ <;> subst hb₁ <;> subst ha₂ <;> subst hb₂ <;>
    iapply refines_target_step (ProgramLogics.pure_step_binOpVal (v' := _) rfl) <;>
    iapply refines_src_step (ProgramLogics.pure_step_binOpVal (v' := _) rfl) <;>
    iapply refines_value <;>
    simp only [intInterp_car, boolInterp_car] <;>
    (iexists _; isplitr) <;> (ipureintro; rfl)

theorem compat_unop {e e' : Exp} {op : UnOp} (hop : UnOpTyped op A B)
    (h : semTyped GF n Γ e e' A) : semTyped GF n Γ (.unop op e) (.unop op e') B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_unOp
  iapply refines_wand $$ H
  iintro %v %v' Hv
  cases hop <;>
    simp only [typeInterp_int, typeInterp_bool, intInterp_car, boolInterp_car] <;>
    icases Hv with ⟨%z, %ha, %hb⟩ <;> subst ha <;> subst hb <;>
    iapply refines_target_step (ProgramLogics.pure_step_unOpVal (v' := _) rfl) <;>
    iapply refines_src_step (ProgramLogics.pure_step_unOpVal (v' := _) rfl) <;>
    iapply refines_value <;>
    simp only [intInterp_car, boolInterp_car] <;>
    (iexists _; isplitr) <;> (ipureintro; rfl)

theorem compat_if {e₀ e₀' e₁ e₁' e₂ e₂' : Exp} (h₀ : semTyped GF n Γ e₀ e₀' .bool)
    (h₁ : semTyped GF n Γ e₁ e₁' A) (h₂ : semTyped GF n Γ e₂ e₂' A) :
    semTyped GF n Γ (.if e₀ e₁ e₂) (.if e₀' e₁' e₂') A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₀ δ γ $$ Hctx with H0
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_if
  iapply refines_wand $$ H0
  iintro %v %v' Hv
  simp only [typeInterp_bool, boolInterp_car]
  icases Hv with ⟨%b, %ha, %hb⟩
  subst ha
  subst hb
  cases b
  · iapply refines_target_step (ProgramLogics.pure_step_if_false _ _)
    iapply refines_src_step (ProgramLogics.pure_step_if_false _ _)
    iexact H2
  · iapply refines_target_step (ProgramLogics.pure_step_if_true _ _)
    iapply refines_src_step (ProgramLogics.pure_step_if_true _ _)
    iexact H1

theorem compat_pair {e₁ e₁' e₂ e₂' : Exp} (h₁ : semTyped GF n Γ e₁ e₁' A)
    (h₂ : semTyped GF n Γ e₂ e₂' B) :
    semTyped GF n Γ (.pair e₁ e₂) (.pair e₁' e₂') (.prod A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_pairR
  iapply refines_wand $$ H2
  iintro %v₂ %v₂' Hv₂
  iapply refines_bind_pairL v₂ v₂'
  iapply refines_wand $$ H1
  iintro %v₁ %v₁' Hv₁
  iapply refines_target_step (ProgramLogics.pure_step_pair _ _)
  iapply refines_src_step (ProgramLogics.pure_step_pair _ _)
  iapply refines_value
  simp only [typeInterp_prod, prodInterp_car]
  iexists v₁, v₁', v₂, v₂'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  isplitl [Hv₁]
  · iexact Hv₁
  · iexact Hv₂

theorem compat_fst {e e' : Exp} (h : semTyped GF n Γ e e' (.prod A B)) :
    semTyped GF n Γ (.fst e) (.fst e') A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_fst
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_prod, prodInterp_car]
  icases Hv with ⟨%w₁, %w₁', %w₂, %w₂', %ha, %hb, Hw₁, Hw₂⟩
  subst ha
  subst hb
  iapply refines_target_step (ProgramLogics.pure_step_fst _ _)
  iapply refines_src_step (ProgramLogics.pure_step_fst _ _)
  iapply refines_value
  iexact Hw₁

theorem compat_snd {e e' : Exp} (h : semTyped GF n Γ e e' (.prod A B)) :
    semTyped GF n Γ (.snd e) (.snd e') B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_snd
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_prod, prodInterp_car]
  icases Hv with ⟨%w₁, %w₁', %w₂, %w₂', %ha, %hb, Hw₁, Hw₂⟩
  subst ha
  subst hb
  iapply refines_target_step (ProgramLogics.pure_step_snd _ _)
  iapply refines_src_step (ProgramLogics.pure_step_snd _ _)
  iapply refines_value
  iexact Hw₂

theorem compat_injl {e e' : Exp} (h : semTyped GF n Γ e e' A) :
    semTyped GF n Γ (.injL e) (.injL e') (.sum A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_injL
  iapply refines_wand $$ H
  iintro %v %v' Hv
  iapply refines_target_step (ProgramLogics.pure_step_injl _)
  iapply refines_src_step (ProgramLogics.pure_step_injl _)
  iapply refines_value
  simp only [typeInterp_sum, sumInterp_car]
  ileft
  iexists v, v'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  · iexact Hv

theorem compat_injr {e e' : Exp} (h : semTyped GF n Γ e e' B) :
    semTyped GF n Γ (.injR e) (.injR e') (.sum A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_injR
  iapply refines_wand $$ H
  iintro %v %v' Hv
  iapply refines_target_step (ProgramLogics.pure_step_injr _)
  iapply refines_src_step (ProgramLogics.pure_step_injr _)
  iapply refines_value
  simp only [typeInterp_sum, sumInterp_car]
  iright
  iexists v, v'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  · iexact Hv

theorem compat_case {e e' e₁ e₁' e₂ e₂' : Exp} {C : Ty} (h : semTyped GF n Γ e e' (.sum B C))
    (h₁ : semTyped GF n Γ e₁ e₁' (.fn B A)) (h₂ : semTyped GF n Γ e₂ e₂' (.fn C A)) :
    semTyped GF n Γ (.case e e₁ e₂) (.case e' e₁' e₂') A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_case
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_sum, sumInterp_car, typeInterp_fn]
  icases Hv with ⟨⟨%w, %w', %ha, %hb, Hw⟩ | ⟨%w, %w', %ha, %hb, Hw⟩⟩
  · subst ha
    subst hb
    iapply refines_target_step (ProgramLogics.pure_step_match_injl _ _ _)
    iapply refines_src_step (ProgramLogics.pure_step_match_injl _ _ _)
    iapply refines_bind_appL w w'
    iapply refines_wand $$ H1
    iintro %g %g' Hg
    simp only [funInterp_car]
    iapply Hg $$ %w %w' Hw
  · subst ha
    subst hb
    iapply refines_target_step (ProgramLogics.pure_step_match_injr _ _ _)
    iapply refines_src_step (ProgramLogics.pure_step_match_injr _ _ _)
    iapply refines_bind_appL w w'
    iapply refines_wand $$ H2
    iintro %g %g' Hg
    simp only [funInterp_car]
    iapply Hg $$ %w %w' Hw

theorem compat_tlam {e e' : Exp} (h : semTyped GF (n + 1) (shiftCtx Γ) e e' A) :
    semTyped GF n Γ (tLam e) (tLam e') (.all A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [tLam, Exp.substMap, Binder.deleteMap]
  iapply refines_target_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_rec _ _ _)
  iapply refines_value
  simp only [typeInterp_all, allInterp_car]
  iintro !> %τ
  simp only [tApp]
  iapply refines_target_step (ProgramLogics.pure_step_beta _ _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  icases contextInterp_cons Γ γ δ τ $$ Hctx with Hctx'
  icases semTyped_apply h (τ .:: δ) γ $$ Hctx' with H
  iexact H

theorem compat_tapp {e e' : Exp} (B : Ty) (h : semTyped GF n Γ e e' (.all A)) :
    semTyped GF n Γ (tApp e) (tApp e') (A.subst1 B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [tApp, Exp.ofVal, Exp.substMap]
  iapply refines_bind_appL _ _
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_all, allInterp_car]
  icases Hv with #Hv
  ispecialize Hv $$ %(typeInterp B δ)
  rw [typeInterp_move_single_subst B A δ]
  simp only [tApp]
  iexact Hv

theorem compat_pack {e e' : Exp} (B : Ty) (h : semTyped GF n Γ e e' (A.subst1 B)) :
    semTyped GF n Γ (pack e) (pack e') (.exist A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [pack]
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_exist, existInterp_car]
  iexists v, v'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iexists (typeInterp B δ)
  rw [typeInterp_move_single_subst B A δ]
  iexact Hv

theorem compat_unpack {e e' e₂ e₂' : Exp} {C : Ty} (x : String)
    (h : semTyped GF n Γ e e' (.exist A))
    (h' : semTyped GF (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x A) e₂ e₂'
      (C.rename (· + 1))) :
    semTyped GF n Γ (unpack e (.named x) e₂) (unpack e' (.named x) e₂') C := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [unpack, Exp.substMap, Binder.deleteMap]
  iapply refines_bind_appR
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_exist, existInterp_car]
  icases Hv with ⟨%w, %w', %ha, %hb, %τ, Hw⟩
  subst ha
  subst hb
  iapply refines_target_step (ProgramLogics.pure_step_appL
    (ProgramLogics.pure_step_rec _ _ _) _)
  iapply refines_src_step (ProgramLogics.pure_step_appL (ProgramLogics.pure_step_rec _ _ _) _)
  iapply refines_target_step (ProgramLogics.pure_step_beta _ _ _ _)
  iapply refines_src_step (ProgramLogics.pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  rw [← Exp.substMap_insert, ← Exp.substMap_insert,
    ← LawfulPartialMap.map_insert (f := (Prod.fst : Val × Val → Val)) (k := x) (v := (v, v')),
    ← LawfulPartialMap.map_insert (f := (Prod.snd : Val × Val → Val)) (k := x) (v := (v, v'))]
  icases contextInterp_cons Γ γ δ τ $$ Hctx with Hctx'
  icases contextInterp_insert (shiftCtx Γ) γ (τ .:: δ) A v v' x $$ Hw Hctx' with Hctx''
  icases semTyped_apply h' (τ .:: δ) (insert (M := TyMapStr) γ x (v, v')) $$ Hctx'' with H'
  iapply refines_wand $$ H'
  iintro %u %u' Hu
  rw [typeInterp_cons C δ τ]
  iexact Hu

theorem compat_roll {e e' : Exp} (h : semTyped GF n Γ e e' (A.subst1 (.mu A))) :
    semTyped GF n Γ (roll e) (roll e') (.mu A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [roll]
  iapply refines_wand $$ H
  iintro %v %v' Hv
  rw [typeInterp_mu_unfold A δ]
  simp only [muRec_car]
  iexists v, v'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  inext
  rw [typeInterp_move_single_subst (.mu A) A δ]
  iexact Hv

theorem compat_unroll {e e' : Exp} (h : semTyped GF n Γ e e' (.mu A)) :
    semTyped GF n Γ (unroll e) (unroll e') (A.subst1 (.mu A)) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [unroll, Exp.substMap, Binder.deleteMap, get?_delete_self]
  iapply refines_bind_appR
  iapply refines_wand $$ H
  iintro %v %v' Hv
  rw [typeInterp_mu_unfold A δ]
  simp only [muRec_car]
  icases Hv with ⟨%w, %w', %ha, %hb, Hw⟩
  subst ha
  subst hb
  iapply refines_target_step (ProgramLogics.pure_step_appL
    (ProgramLogics.pure_step_rec _ _ _) _)
  iapply refines_src_step (ProgramLogics.pure_step_appL (ProgramLogics.pure_step_rec _ _ _) _)
  iapply refines_target_step_later (ProgramLogics.pure_step_beta _ _ _ _)
  inext
  iapply refines_src_step (ProgramLogics.pure_step_beta _ _ _ _)
  simp [Exp.subst]
  iapply refines_value
  rw [← typeInterp_move_single_subst (.mu A) A δ]
  iexact Hw

theorem compat_new {e e' : Exp} (h : semTyped GF n Γ e e' A) :
    semTyped GF n Γ hl(ref(&e)) hl(ref(&e')) (.ref A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.ofVal, Exp.substMap]
  iapply refines_bind_allocNR
  iapply refines_wand $$ H
  iintro %v %v' Hv
  iapply refines_src_alloc v'
  iintro %l' Hl'
  unfold refines
  iintro %K Hs
  iapply swp_fupd
  iapply swp_alloc v
  iintro %l Hl
  imod Iris.inv_alloc logN ⊤ (refInv l l' (typeInterp A δ)) $$ [Hl Hl' Hv] with #Hinv
  · inext
    unfold refInv
    iexists v, v'
    iframe Hl Hl' Hv
  imodintro
  iexists hl_val(#l')
  isplitl [Hs]
  · iexact Hs
  · simp only [typeInterp_ref, refInterp_car]
    iexists l, l'
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    · iexact Hinv

theorem compat_load {e e' : Exp} (h : semTyped GF n Γ e e' (.ref A)) :
    semTyped GF n Γ (.load e) (.load e') A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [Exp.substMap]
  iapply refines_bind_load
  iapply refines_wand $$ H
  iintro %v %v' Hv
  simp only [typeInterp_ref, refInterp_car]
  icases Hv with ⟨%l, %l', %ha, %hb, #Hinv⟩
  subst ha
  subst hb
  unfold refines
  iintro %K Hs
  iapply ImpredInvariants.inv_open (N := logN) logN_subseteq_top $$ Hinv
  iintro HI
  unfold refInv
  iapply fupd_swp (E₂ := (⊤ : CoPset) \ ↑logN)
  icases HI with ⟨%w, %w', >Hl, >Hl', #Hw⟩
  imod srcExpr_step_load srcN_subseteq_diff_logN $$ [Hs Hl'] with ⟨Hs, Hl'⟩
  · iframe Hs Hl'
  imodintro
  swp_enter Hcl
  wp_load
  imod Hcl
  imodintro
  isplitl [Hl Hl']
  · inext
    iexists w, w'
    iframe Hl Hl' Hw
  · iexists w'
    iframe Hs Hw

theorem compat_store {e₁ e₁' e₂ e₂' : Exp} (h₁ : semTyped GF n Γ e₁ e₁' (.ref A))
    (h₂ : semTyped GF n Γ e₂ e₂' A) :
    semTyped GF n Γ (.store e₁ e₂) (.store e₁' e₂') .unit := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [Exp.substMap]
  iapply refines_bind_storeR
  iapply refines_wand $$ H2
  iintro %v₂ %v₂' Hv₂
  iapply refines_bind_storeL v₂ v₂'
  iapply refines_wand $$ H1
  iintro %v₁ %v₁' Hv₁
  simp only [typeInterp_ref, refInterp_car]
  icases Hv₁ with ⟨%l, %l', %ha, %hb, #Hinv⟩
  subst ha
  subst hb
  unfold refines
  iintro %K Hs
  iapply ImpredInvariants.inv_open (N := logN) logN_subseteq_top $$ Hinv
  iintro HI
  unfold refInv
  iapply fupd_swp (E₂ := (⊤ : CoPset) \ ↑logN)
  icases HI with ⟨%w, %w', >Hl, >Hl', _⟩
  imod srcExpr_step_store srcN_subseteq_diff_logN $$ [Hs Hl'] with ⟨Hs, Hl'⟩
  · iframe Hs Hl'
  imodintro
  swp_enter Hcl
  wp_store
  imod Hcl
  imodintro
  isplitl [Hl Hl' Hv₂]
  · inext
    iexists v₂, v₂'
    iframe Hl Hl' Hv₂
  · iexists hl_val(#())
    isplitl [Hs]
    · iexact Hs
    · simp only [typeInterp_unit, unitInterp_car]
      isplitr
      · ipureintro; trivial
      · ipureintro; trivial

end Compat

/-- The fundamental theorem: the logical relation is reflexive on syntactically typed terms. -/
theorem fundamental {n : Nat} {Γ : TypingContext} {e : Exp} {A : Ty} (h : SynTyped n Γ e A) :
    semTyped GF n Γ e e A := by
  induction h with
  | typed_var _ _ x _ hx => exact compat_var x hx
  | typed_lam _ _ x _ _ _ _ _ ih => exact compat_lambda x ih
  | typed_lam_anon _ _ _ _ _ _ _ ih => exact compat_lambda_anon ih
  | typed_tlam _ _ _ _ _ ih => exact compat_tlam ih
  | typed_tapp _ _ _ B _ _ _ ih => exact compat_tapp B ih
  | typed_pack _ _ _ B _ _ _ _ ih => exact compat_pack B ih
  | typed_unpack _ _ _ _ _ _ x _ _ _ ih ih' => exact compat_unpack x ih ih'
  | typed_int _ _ z => exact compat_int z
  | typed_bool _ _ b => exact compat_bool b
  | typed_unit => exact compat_unit
  | typed_if _ _ _ _ _ _ _ _ _ ih₀ ih₁ ih₂ => exact compat_if ih₀ ih₁ ih₂
  | typed_app _ _ _ _ _ _ _ _ ih₁ ih₂ => exact compat_beta ih₁ ih₂
  | typed_binop _ _ _ _ _ _ _ _ hop _ _ ih₁ ih₂ => exact compat_binop hop ih₁ ih₂
  | typed_unop _ _ _ _ _ _ hop _ ih => exact compat_unop hop ih
  | typed_pair _ _ _ _ _ _ _ _ ih₁ ih₂ => exact compat_pair ih₁ ih₂
  | typed_fst _ _ _ _ _ _ ih => exact compat_fst ih
  | typed_snd _ _ _ _ _ _ ih => exact compat_snd ih
  | typed_injl _ _ _ _ _ _ _ ih => exact compat_injl ih
  | typed_injr _ _ _ _ _ _ _ ih => exact compat_injr ih
  | typed_case _ _ _ _ _ _ _ _ _ _ _ ih ih₁ ih₂ => exact compat_case ih ih₁ ih₂
  | typed_roll _ _ _ _ _ ih => exact compat_roll ih
  | typed_unroll _ _ _ _ _ ih => exact compat_unroll ih
  | typed_load _ _ _ _ _ ih => exact compat_load ih
  | typed_store _ _ _ _ _ _ _ ih₁ ih₂ => exact compat_store ih₁ ih₂
  | typed_new _ _ _ _ _ ih => exact compat_new ih

end ProgramLogics.Reloc
