import LeanLR.ProgramLogics.LogRel.Syntactic
import LeanLR.ProgramLogics.LogRel.PersistentPred
import LeanLR.ProgramLogics.InvariantLib
import LeanLR.ProgramLogics.HeapLang.SwpTactics
import Iris.Instances.Lib.Invariants
import Iris.HeapLang.Metatheory

/-!
# A logical relation for System F + μ + state, in Iris

`program_logics/logrel/logrel_sol.v`.
-/

open Iris Iris.BI Iris.OFE Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std

namespace ProgramLogics.LogRel

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

/-! ## Semantic types

A semantic type is a persistent predicate on values; a type-variable environment maps De Bruijn
indices to semantic types. `Nat` is discrete, so an environment is an ordinary function and its
OFE is the pointwise one. -/

abbrev SemType (GF : BundledGFunctors) := PersistentPred Val (IProp GF)

abbrev Env (GF : BundledGFunctors) := Nat → SemType GF

/-- Rocq's `mk_semtype`. -/
def mkSemType (pred : Val → IProp GF) (h : ∀ v, Persistent (pred v)) : SemType GF := ⟨pred, h⟩

/-- Rocq's `τ .:: δ`. -/
def consEnv (τ : SemType GF) (δ : Env GF) : Env GF
  | 0 => τ
  | n + 1 => δ n

@[inherit_doc] notation:30 τ " .:: " δ => consEnv τ δ

theorem consEnv_ne {n : Nat} {τ τ' : SemType GF} {δ δ' : Env GF}
    (hτ : τ ≡{n}≡ τ') (hδ : δ ≡{n}≡ δ') : (τ .:: δ) ≡{n}≡ (τ' .:: δ') := by
  intro k
  cases k with
  | zero => exact hτ
  | succ k => exact hδ k

/-! ## The interpretations -/

/-- The expression relation. The course's `WP` is the *sequential* one. -/
def exprInterp (τ : SemType GF) (e : Exp) : IProp GF := swp .NotStuck ⊤ ⊤ e (fun v => τ v)

def intInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v => iprop(∃ n : Int, ⌜v = hl_val(#n)⌝)) (fun _ => inferInstance)

def boolInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v => iprop(∃ b : Bool, ⌜v = hl_val(#b)⌝)) (fun _ => inferInstance)

def unitInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v => iprop(⌜v = hl_val(#())⌝)) (fun _ => inferInstance)

def funInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop(∀ w : Val, □ (σ₁ δ w -∗ exprInterp (σ₂ δ) hl(v(&v) &w))))
    (fun _ => inferInstance)

def varInterp (x : Nat) : Env GF → SemType GF := fun δ => δ x

def allInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop(□ ∀ τ : SemType GF, exprInterp (σ (τ .:: δ)) (tApp hl(v(&v)))))
    (fun _ => inferInstance)

def existInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop(∃ w : Val, ⌜v = packV w⌝ ∗ ∃ τ : SemType GF, (σ (τ .:: δ)) w))
    (fun _ => inferInstance)

/-- One unrolling of a recursive type. The `▷` is what makes it contractive. -/
def muRec (σ : Env GF → SemType GF) (δ : Env GF) (ρ : SemType GF) : SemType GF :=
  mkSemType (fun v => iprop(∃ w : Val, ⌜v = rollV w⌝ ∗ ▷ (σ (ρ .:: δ)) w))
    (fun _ => inferInstance)

def logN : Namespace := nroot .@ "logrel"

def refInv (l : Loc) (τ : SemType GF) : IProp GF := iprop(∃ w : Val, (l ↦ some w) ∗ τ w)

def refInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop(∃ l : Loc, ⌜v = hl_val(#l)⌝ ∗ inv logN (refInv l (σ δ))))
    (fun _ => inferInstance)

def prodInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop(∃ w₁ w₂ : Val, ⌜v = hl_val((&w₁, &w₂))⌝ ∗ σ₁ δ w₁ ∗ σ₂ δ w₂))
    (fun _ => inferInstance)

def sumInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v => iprop((∃ w : Val, ⌜v = hl_val(injl(&w))⌝ ∗ σ₁ δ w) ∨
      (∃ w : Val, ⌜v = hl_val(injr(&w))⌝ ∗ σ₂ δ w)))
    (fun _ => inferInstance)

/-! ### Applying an interpretation to a value

Each holds by `rfl`; they let `simp` see through `mkSemType`. -/

@[simp] theorem intInterp_car (δ : Env GF) (v : Val) :
    (intInterp δ).car v = iprop(∃ n : Int, ⌜v = hl_val(#n)⌝) := rfl
@[simp] theorem boolInterp_car (δ : Env GF) (v : Val) :
    (boolInterp δ).car v = iprop(∃ b : Bool, ⌜v = hl_val(#b)⌝) := rfl
@[simp] theorem unitInterp_car (δ : Env GF) (v : Val) :
    (unitInterp δ).car v = iprop(⌜v = hl_val(#())⌝) := rfl
@[simp] theorem funInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (funInterp σ₁ σ₂ δ).car v
      = iprop(∀ w : Val, □ ((σ₁ δ).car w -∗ exprInterp (σ₂ δ) hl(v(&v) &w))) := rfl
@[simp] theorem allInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (allInterp σ δ).car v
      = iprop(□ ∀ τ : SemType GF, exprInterp (σ (τ .:: δ)) (tApp hl(v(&v)))) := rfl
@[simp] theorem existInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (existInterp σ δ).car v
      = iprop(∃ w : Val, ⌜v = packV w⌝ ∗ ∃ τ : SemType GF, (σ (τ .:: δ)).car w) := rfl
@[simp] theorem refInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (refInterp σ δ).car v
      = iprop(∃ l : Loc, ⌜v = hl_val(#l)⌝ ∗ inv logN (refInv l (σ δ))) := rfl
@[simp] theorem prodInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (prodInterp σ₁ σ₂ δ).car v
      = iprop(∃ w₁ w₂ : Val, ⌜v = hl_val((&w₁, &w₂))⌝ ∗ (σ₁ δ).car w₁ ∗ (σ₂ δ).car w₂) := rfl
@[simp] theorem sumInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v : Val) :
    (sumInterp σ₁ σ₂ δ).car v
      = iprop((∃ w : Val, ⌜v = hl_val(injl(&w))⌝ ∗ (σ₁ δ).car w) ∨
        (∃ w : Val, ⌜v = hl_val(injr(&w))⌝ ∗ (σ₂ δ).car w)) := rfl
@[simp] theorem muRec_car (σ : Env GF → SemType GF) (δ : Env GF) (ρ : SemType GF) (v : Val) :
    (muRec σ δ ρ).car v = iprop(∃ w : Val, ⌜v = rollV w⌝ ∗ ▷ (σ (ρ .:: δ)).car w) := rfl

/-- `muRec` is contractive in its recursive argument: the `▷` is what pays for it. -/
theorem muRec_contractive (σ : Env GF → SemType GF) (hσ : NonExpansive σ) (δ : Env GF) :
    Contractive (muRec σ δ) where
  distLater_dist {n ρ ρ'} h v := by
    refine BI.exists_ne fun w => BI.sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist (f := (BIBase.later : IProp GF → IProp GF)) ?_
    intro m hm
    exact hσ.ne (consEnv_ne (h m hm) .rfl) w

/-- The interpretation of a type, packaged with its non-expansiveness in the environment: the
`μ` case needs the latter in order to build its fixpoint, so the two are defined together. -/
def typeInterpAux : Ty → { σ : Env GF → SemType GF // NonExpansive σ }
  | .tVar x => ⟨varInterp x, ⟨fun {_ _ _} h => h x⟩⟩
  | .int => ⟨intInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .bool => ⟨boolInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .unit => ⟨unitInterp, ⟨fun {_ _ _} _ => .rfl⟩⟩
  | .fn A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨funInterp p.1 q.1, ⟨fun {_ _ _} h v => by
      refine BI.forall_ne fun w => BI.intuitionistically_ne.ne ?_
      exact BI.wand_ne.ne (p.2.ne h w) (swp_ne.ne fun u => q.2.ne h u)⟩⟩
  | .all A =>
    let p := typeInterpAux A
    ⟨allInterp p.1, ⟨fun {_ _ _} h v => by
      refine BI.intuitionistically_ne.ne (BI.forall_ne fun τ => ?_)
      exact swp_ne.ne fun u => p.2.ne (consEnv_ne .rfl h) u⟩⟩
  | .exist A =>
    let p := typeInterpAux A
    ⟨existInterp p.1, ⟨fun {_ _ _} h v => by
      refine BI.exists_ne fun w => BI.sep_ne.ne .rfl (BI.exists_ne fun τ => ?_)
      exact p.2.ne (consEnv_ne .rfl h) w⟩⟩
  | .mu A =>
    let p := typeInterpAux A
    ⟨fun δ => @Iris.fixpoint _ _ _ (muRec p.1 δ) (muRec_contractive p.1 p.2 δ),
      ⟨fun {_ δ δ'} h => by
        refine @Iris.fixpoint_dist _ _ _ _ _ (muRec_contractive p.1 p.2 δ)
          (muRec_contractive p.1 p.2 δ') _ fun ρ v => ?_
        refine BI.exists_ne fun w => BI.sep_ne.ne .rfl (BI.later_ne.ne ?_)
        exact p.2.ne (consEnv_ne .rfl h) w⟩⟩
  | .ref A =>
    let p := typeInterpAux A
    ⟨refInterp p.1, ⟨fun {_ _ _} h v => by
      refine BI.exists_ne fun l => BI.sep_ne.ne .rfl ?_
      refine (Iris.inv_ne logN).ne ?_
      exact BI.exists_ne fun w => BI.sep_ne.ne .rfl (p.2.ne h w)⟩⟩
  | .prod A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨prodInterp p.1 q.1, ⟨fun {_ _ _} h v => by
      refine BI.exists_ne fun w₁ => BI.exists_ne fun w₂ => BI.sep_ne.ne .rfl ?_
      exact BI.sep_ne.ne (p.2.ne h w₁) (q.2.ne h w₂)⟩⟩
  | .sum A B =>
    let p := typeInterpAux A
    let q := typeInterpAux B
    ⟨sumInterp p.1 q.1, ⟨fun {_ _ _} h v => by
      refine BI.or_ne.ne ?_ ?_
      · exact BI.exists_ne fun w => BI.sep_ne.ne .rfl (p.2.ne h w)
      · exact BI.exists_ne fun w => BI.sep_ne.ne .rfl (q.2.ne h w)⟩⟩

/-- Rocq's `𝒱`. -/
def typeInterp (A : Ty) : Env GF → SemType GF := (typeInterpAux A).1

instance typeInterp_ne (A : Ty) : NonExpansive (typeInterp (GF := GF) A) := (typeInterpAux A).2

/-! ### Unfolding `typeInterp`

Each of these holds by `rfl`; they exist so that `simp` can use them. -/

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

/-! ## Moving substitutions through the interpretation

`iris-lean`'s OFE equivalence *is* Lean equality, so Rocq's `≡` statements become plain
equations and `type_interp_ext` is `funext`. -/

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

/-- Rocq's `𝒢`. -/
def contextInterp (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF) : IProp GF :=
  iprop([∗map] _x ↦ A;v ∈ Γ;γ, typeInterp A δ v)

instance contextInterp_pers (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF) :
    Persistent (contextInterp (GF := GF) Γ γ δ) := by
  unfold contextInterp; infer_instance

theorem contextInterp_dom_eq (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF) :
    contextInterp (GF := GF) Γ γ δ ⊢ iprop(⌜PartialMap.dom Γ = PartialMap.dom γ⌝) :=
  BigSepM2.bigSepM2_dom _ _ _

theorem contextInterp_empty (δ : Env GF) : ⊢ contextInterp (GF := GF) ∅ ∅ δ :=
  (BigSepM2.bigSepM2_empty _).mpr

/-- The context relation at the empty context pins the substitution down. -/
theorem contextInterp_empty_inv (γ : TyMapStr Val) (δ : Env GF) :
    contextInterp (GF := GF) ∅ γ δ ⊢ iprop(⌜γ = ∅⌝) := by
  refine (contextInterp_dom_eq ∅ γ δ).trans (BI.pure_mono fun h => ?_)
  refine LawfulPartialMap.eq_empty_iff.mpr fun k => ?_
  have hk := congrFun h k
  simp only [PartialMap.dom, LawfulPartialMap.get?_empty, Option.isSome_none,
    Bool.false_eq_true, eq_iff_iff, false_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hk
  exact hk

theorem contextInterp_insert (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF)
    (A : Ty) (v : Val) (x : String) :
    ⊢@{IProp GF} typeInterp A δ v -∗ contextInterp Γ γ δ -∗
      contextInterp (insert (M := TyMapStr) Γ x A) (insert (M := TyMapStr) γ x v) δ := by
  iintro Hv Hγ
  unfold contextInterp
  iapply BigSepM2.bigSepM2_insert_elim
    (Φ := fun (_ : String) (B : Ty) (w : Val) => typeInterp B δ w) $$ Hv Hγ

theorem contextInterp_lookup (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF)
    (A : Ty) {x : String} (h : get? (M := TyMapStr) Γ x = some A) :
    contextInterp (GF := GF) Γ γ δ ⊢
      iprop(∃ v : Val, ⌜get? (M := TyMapStr) γ x = some v⌝ ∧ typeInterp A δ v) :=
  BigSepM2.bigSepM2_lookup_left h

theorem contextInterp_cons (Γ : TypingContext) (γ : TyMapStr Val) (δ : Env GF) (τ : SemType GF) :
    contextInterp Γ γ δ ⊢ contextInterp (shiftCtx Γ) γ (τ .:: δ) := by
  unfold contextInterp shiftCtx
  refine Entails.trans ?_ (BigSepM2.bigSepM2_map_left _ _ _ _).mpr
  refine BigSepM2.bigSepM2_mono fun _ _ => ?_
  rw [typeInterp_cons _ δ τ]

/-! ## Semantic typing -/

/-- Rocq's `TY n; Γ ⊨ e : A`. The type-variable count `n` is inert here, as in Rocq: the
environment is total. -/
def semTyped (GF : BundledGFunctors) [HeapLangGS hlc GF] (_n : Nat) (Γ : TypingContext) (e : Exp)
    (A : Ty) : Prop :=
  ⊢ (iprop(∀ δ : Env GF, ∀ γ : TyMapStr Val,
    contextInterp Γ γ δ -∗ exprInterp (typeInterp A δ) (e.substMap γ)) : IProp GF)

/-- A semantic typing fact, in the form the compatibility proofs use it. -/
theorem semTyped_apply {n : Nat} {Γ : TypingContext} {e : Exp} {A : Ty}
    (h : semTyped GF n Γ e A) (δ : Env GF) (γ : TyMapStr Val) :
    contextInterp Γ γ δ ⊢ exprInterp (typeInterp A δ) (e.substMap γ) := by
  unfold semTyped at h
  iintro #Hctx
  ihave H := h
  ispecialize H $$ %δ %γ Hctx
  iexact H

private theorem deleteMap_named_comm {V : Type} {M : Type → Type} [LawfulPartialMap M String]
    (vs : M V) (x f : String) :
    (Binder.named x).deleteMap ((Binder.named f).deleteMap vs)
      = (Binder.named f).deleteMap ((Binder.named x).deleteMap vs) :=
  LawfulPartialMap.delete_delete_comm

/-! ## Compatibility lemmas -/

section Compat

variable {n : Nat} {Γ : TypingContext} {A B : Ty}

theorem compat_var (x : String) (h : get? (M := TyMapStr) Γ x = some A) :
    semTyped GF n Γ (.var x) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_lookup Γ γ δ A h $$ Hctx with ⟨%v, %hv, Hv⟩
  simp only [exprInterp, Exp.substMap, hv]
  iapply swp_value'
  iexact Hv

theorem compat_int (z : Int) : semTyped GF n Γ hl(#z) .int := by
  unfold semTyped
  iintro %δ %γ _
  simp only [exprInterp, Exp.ofVal, Exp.substMap, typeInterp_int, intInterp_car]
  iapply swp_value'
  iexists z
  ipureintro
  rfl

theorem compat_bool (b : Bool) : semTyped GF n Γ hl(#b) .bool := by
  unfold semTyped
  iintro %δ %γ _
  simp only [exprInterp, Exp.ofVal, Exp.substMap, typeInterp_bool, boolInterp_car]
  iapply swp_value'
  iexists b
  ipureintro
  rfl

theorem compat_unit : semTyped GF n Γ hl(#()) .unit := by
  unfold semTyped
  iintro %δ %γ _
  simp only [exprInterp, Exp.ofVal, Exp.substMap, typeInterp_unit, unitInterp_car]
  iapply swp_value'
  ipureintro
  rfl

theorem compat_beta {e₁ e₂ : Exp} (h₁ : semTyped GF n Γ e₁ (.fn A B))
    (h₂ : semTyped GF n Γ e₂ A) : semTyped GF n Γ (.app e₁ e₂) B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap, typeInterp_fn, funInterp_car]
  iapply swp_bind_appR
  iapply swp_wand $$ H2
  iintro %v₂ Hv₂
  iapply swp_bind_appL
  iapply swp_wand $$ H1
  iintro %v₁ Hv₁
  iapply Hv₁ $$ %v₂ Hv₂

theorem compat_lambda (x : String) {e : Exp}
    (h : semTyped GF n (insert (M := TyMapStr) Γ x A) e B) :
    semTyped GF n Γ (.rec_ .anon (.named x) e) (.fn A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [exprInterp, Exp.substMap, typeInterp_fn, funInterp_car, Binder.deleteMap]
  iapply swp_pure_step (pure_step_rec _ _ _)
  iapply swp_value'
  iintro %w !> Hw
  iapply swp_pure_step (pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  rw [← Exp.substMap_insert]
  icases contextInterp_insert Γ γ δ A w x $$ Hw Hctx with Hctx'
  icases semTyped_apply h δ (insert (M := TyMapStr) γ x w) $$ Hctx' with H
  simp only [exprInterp]
  iexact H

theorem compat_lambda_anon {e : Exp} (h : semTyped GF n Γ e B) :
    semTyped GF n Γ (.rec_ .anon .anon e) (.fn A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [exprInterp, Exp.substMap, typeInterp_fn, funInterp_car, Binder.deleteMap]
  iapply swp_pure_step (pure_step_rec _ _ _)
  iapply swp_value'
  iintro %w !> _
  iapply swp_pure_step (pure_step_beta _ _ _ _)
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.subst]
  iexact H

theorem compat_binop {e₁ e₂ : Exp} {C : Ty} {op : BinOp} (hop : BinOpTyped op A B C)
    (h₁ : semTyped GF n Γ e₁ A) (h₂ : semTyped GF n Γ e₂ B) :
    semTyped GF n Γ (.binop op e₁ e₂) C := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap]
  iapply swp_bind_binOpR
  iapply swp_wand $$ H2
  iintro %v₂ Hv₂
  iapply swp_bind_binOpL
  iapply swp_wand $$ H1
  iintro %v₁ Hv₁
  cases hop <;>
    simp only [typeInterp_int, typeInterp_bool, intInterp_car, boolInterp_car] <;>
    icases Hv₁ with ⟨%z₁, %hz₁⟩ <;> icases Hv₂ with ⟨%z₂, %hz₂⟩ <;> subst hz₁ <;> subst hz₂ <;>
    iapply swp_pure_step (pure_step_binOpVal (v' := _) rfl) <;>
    iapply swp_value' <;>
    (iexists _; ipureintro; rfl)

theorem compat_unop {e : Exp} {op : UnOp} (hop : UnOpTyped op A B)
    (h : semTyped GF n Γ e A) : semTyped GF n Γ (.unop op e) B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap]
  iapply swp_bind_unOp
  iapply swp_wand $$ H
  iintro %v Hv
  cases hop <;>
    simp only [typeInterp_int, typeInterp_bool, intInterp_car, boolInterp_car] <;>
    icases Hv with ⟨%z, %hz⟩ <;> subst hz <;>
    iapply swp_pure_step (pure_step_unOpVal (v' := _) rfl) <;>
    iapply swp_value' <;>
    (iexists _; ipureintro; rfl)

theorem compat_if {e₀ e₁ e₂ : Exp} (h₀ : semTyped GF n Γ e₀ .bool)
    (h₁ : semTyped GF n Γ e₁ A) (h₂ : semTyped GF n Γ e₂ A) :
    semTyped GF n Γ (.if e₀ e₁ e₂) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₀ δ γ $$ Hctx with H0
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap, typeInterp_bool, boolInterp_car]
  iapply swp_bind_if
  iapply swp_wand $$ H0
  iintro %v ⟨%b, %hb⟩
  subst hb
  cases b
  · iapply swp_pure_step (pure_step_if_false _ _)
    iexact H2
  · iapply swp_pure_step (pure_step_if_true _ _)
    iexact H1

theorem compat_pair {e₁ e₂ : Exp} (h₁ : semTyped GF n Γ e₁ A) (h₂ : semTyped GF n Γ e₂ B) :
    semTyped GF n Γ (.pair e₁ e₂) (.prod A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap, typeInterp_prod, prodInterp_car]
  iapply swp_bind_pairR
  iapply swp_wand $$ H2
  iintro %v₂ Hv₂
  iapply swp_bind_pairL
  iapply swp_wand $$ H1
  iintro %v₁ Hv₁
  iapply swp_pure_step (pure_step_pair _ _)
  iapply swp_value'
  iexists v₁
  iexists v₂
  isplitr
  · ipureintro; rfl
  isplitl [Hv₁]
  · iexact Hv₁
  · iexact Hv₂

theorem compat_fst {e : Exp} (h : semTyped GF n Γ e (.prod A B)) :
    semTyped GF n Γ (.fst e) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap, typeInterp_prod, prodInterp_car]
  iapply swp_bind_fst
  iapply swp_wand $$ H
  iintro %v ⟨%w₁, %w₂, %hv, Hw₁, Hw₂⟩
  subst hv
  iapply swp_pure_step (pure_step_fst _ _)
  iapply swp_value'
  iexact Hw₁

theorem compat_snd {e : Exp} (h : semTyped GF n Γ e (.prod A B)) :
    semTyped GF n Γ (.snd e) B := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap, typeInterp_prod, prodInterp_car]
  iapply swp_bind_snd
  iapply swp_wand $$ H
  iintro %v ⟨%w₁, %w₂, %hv, Hw₁, Hw₂⟩
  subst hv
  iapply swp_pure_step (pure_step_snd _ _)
  iapply swp_value'
  iexact Hw₂

theorem compat_injl {e : Exp} (h : semTyped GF n Γ e A) :
    semTyped GF n Γ (.injL e) (.sum A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap, typeInterp_sum, sumInterp_car]
  iapply swp_bind_injL
  iapply swp_wand $$ H
  iintro %v Hv
  iapply swp_pure_step (pure_step_injl _)
  iapply swp_value'
  ileft
  iexists v
  isplitr
  · ipureintro; rfl
  · iexact Hv

theorem compat_injr {e : Exp} (h : semTyped GF n Γ e B) :
    semTyped GF n Γ (.injR e) (.sum A B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap, typeInterp_sum, sumInterp_car]
  iapply swp_bind_injR
  iapply swp_wand $$ H
  iintro %v Hv
  iapply swp_pure_step (pure_step_injr _)
  iapply swp_value'
  iright
  iexists v
  isplitr
  · ipureintro; rfl
  · iexact Hv

theorem compat_rec (f x : String) {e : Exp} (hxf : x ≠ f)
    (h : semTyped GF n (insert (M := TyMapStr) (insert (M := TyMapStr) Γ f (.fn A B)) x A) e B) :
    semTyped GF n Γ (.rec_ (.named f) (.named x) e) (.fn A B) := by
  rw [LawfulPartialMap.insert_insert_comm (M := TyMapStr) (Ne.symm hxf)] at h
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [exprInterp, Exp.substMap, typeInterp_fn, funInterp_car]
  iapply swp_pure_step (pure_step_rec _ _ _)
  iapply swp_value'
  iintro %w !> Hw
  iloeb as IH generalizing %w Hw
  iapply swp_pure_step_later (pure_step_beta _ _ _ _)
  inext
  rw [← Exp.substMap_insertMap_2 (b₁ := Binder.named f) (b₂ := Binder.named x)]
  icases contextInterp_insert Γ γ δ A w x $$ Hw Hctx with Hx
  icases contextInterp_insert (insert (M := TyMapStr) Γ x A) (insert (M := TyMapStr) γ x w) δ
    (.fn A B)
    (Val.rec_ (.named f) (.named x)
      (Exp.substMap ((Binder.named x).deleteMap ((Binder.named f).deleteMap γ)) e)) f
    $$ [#] Hx with Hfull
  · simp only [typeInterp_fn, funInterp_car, exprInterp]
    iintro %w' !> Hw'
    iapply IH $$ %w' Hw'
  icases semTyped_apply h δ _ $$ Hfull with H
  simp only [exprInterp, Binder.insertMap]
  iexact H

theorem compat_tlam {e : Exp} (h : semTyped GF (n + 1) (shiftCtx Γ) e A) :
    semTyped GF n Γ (tLam e) (.all A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  simp only [exprInterp, tLam, Exp.substMap, typeInterp_all, allInterp_car, Binder.deleteMap]
  iapply swp_pure_step (pure_step_rec _ _ _)
  iapply swp_value'
  iintro !> %τ
  simp only [tApp]
  iapply swp_pure_step (pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  icases contextInterp_cons Γ γ δ τ $$ Hctx with Hctx'
  icases semTyped_apply h (τ .:: δ) γ $$ Hctx' with H
  simp only [exprInterp]
  iexact H

theorem compat_tapp {e : Exp} (B : Ty) (h : semTyped GF n Γ e (.all A)) :
    semTyped GF n Γ (tApp e) (A.subst1 B) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, tApp, Exp.ofVal, Exp.substMap, typeInterp_all, allInterp_car]
  iapply swp_bind_appL
  iapply swp_wand $$ H
  iintro %v #Hv
  ispecialize Hv $$ %(typeInterp B δ)
  rw [typeInterp_move_single_subst B A δ]
  iexact Hv

theorem compat_pack {e : Exp} (B : Ty) (h : semTyped GF n Γ e (A.subst1 B)) :
    semTyped GF n Γ (pack e) (.exist A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, pack, typeInterp_exist, existInterp_car]
  iapply swp_wand $$ H
  iintro %v Hv
  iexists v
  isplitr
  · ipureintro; rfl
  iexists (typeInterp B δ)
  rw [typeInterp_move_single_subst B A δ]
  iexact Hv

theorem compat_unpack {e e' : Exp} {C : Ty} (x : String)
    (h : semTyped GF n Γ e (.exist A))
    (h' : semTyped GF (n + 1) (insert (M := TyMapStr) (shiftCtx Γ) x A) e'
      (C.rename (· + 1))) :
    semTyped GF n Γ (unpack e (.named x) e') C := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, unpack, Exp.substMap, typeInterp_exist, existInterp_car,
    Binder.deleteMap]
  iapply swp_bind_appR
  iapply swp_wand $$ H
  iintro %v ⟨%w, %hv, %τ, Hw⟩
  subst hv
  iapply swp_pure_step (pure_step_appL (pure_step_rec _ _ _) _)
  iapply swp_pure_step (pure_step_beta _ _ _ _)
  simp only [Exp.subst]
  rw [← Exp.substMap_insert]
  icases contextInterp_cons Γ γ δ τ $$ Hctx with Hctx'
  icases contextInterp_insert (shiftCtx Γ) γ (τ .:: δ) A v x $$ Hw Hctx' with Hctx''
  icases semTyped_apply h' (τ .:: δ) (insert (M := TyMapStr) γ x v) $$ Hctx'' with H'
  simp only [exprInterp]
  iapply swp_wand $$ H'
  iintro %u Hu
  rw [typeInterp_cons C δ τ]
  iexact Hu

theorem compat_case {e e₁ e₂ : Exp} {C : Ty} (h : semTyped GF n Γ e (.sum B C))
    (h₁ : semTyped GF n Γ e₁ (.fn B A)) (h₂ : semTyped GF n Γ e₂ (.fn C A)) :
    semTyped GF n Γ (.case e e₁ e₂) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap, typeInterp_sum, sumInterp_car, typeInterp_fn,
    funInterp_car]
  iapply swp_bind_case
  iapply swp_wand $$ H
  iintro %v Hv
  icases Hv with ⟨⟨%w, %hv, Hw⟩ | ⟨%w, %hv, Hw⟩⟩
  · subst hv
    iapply swp_pure_step (pure_step_match_injl _ _ _)
    iapply swp_bind_appL
    iapply swp_wand $$ H1
    iintro %g Hg
    iapply Hg $$ %w Hw
  · subst hv
    iapply swp_pure_step (pure_step_match_injr _ _ _)
    iapply swp_bind_appL
    iapply swp_wand $$ H2
    iintro %g Hg
    iapply Hg $$ %w Hw

theorem compat_roll {e : Exp} (h : semTyped GF n Γ e (A.subst1 (.mu A))) :
    semTyped GF n Γ (roll e) (.mu A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, roll]
  iapply swp_wand $$ H
  iintro %v Hv
  rw [typeInterp_mu_unfold A δ]
  simp only [muRec_car]
  iexists v
  isplitr
  · ipureintro; rfl
  inext
  rw [typeInterp_move_single_subst (.mu A) A δ]
  iexact Hv

theorem compat_unroll {e : Exp} (h : semTyped GF n Γ e (.mu A)) :
    semTyped GF n Γ (unroll e) (A.subst1 (.mu A)) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, unroll, Exp.substMap, Binder.deleteMap,
    LawfulPartialMap.get?_delete_eq (M := TyMapStr) rfl]
  iapply swp_bind_appR
  iapply swp_wand $$ H
  iintro %v Hv
  rw [typeInterp_mu_unfold A δ]
  simp only [muRec_car]
  icases Hv with ⟨%w, %hv, Hw⟩
  subst hv
  iapply swp_pure_step (pure_step_appL (pure_step_rec _ _ _) _)
  iapply swp_pure_step_later (pure_step_beta _ _ _ _)
  inext
  simp [Exp.subst]
  iapply swp_value'
  rw [← typeInterp_move_single_subst (.mu A) A δ]
  iexact Hw

theorem compat_new {e : Exp} (h : semTyped GF n Γ e A) :
    semTyped GF n Γ hl(ref(&e)) (.ref A) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.ofVal, Exp.substMap, typeInterp_ref, refInterp_car]
  iapply swp_bind_allocNR
  iapply swp_wand $$ H
  iintro %v Hv
  iapply swp_fupd
  iapply swp_alloc v
  iintro %l Hl
  imod Iris.inv_alloc logN ⊤ (refInv l (typeInterp A δ)) $$ [Hl Hv] with #Hinv
  · inext
    unfold refInv
    iexists v
    isplitl [Hl]
    · iexact Hl
    · iexact Hv
  imodintro
  iexists l
  isplitr
  · ipureintro; rfl
  · iexact Hinv

theorem compat_load {e : Exp} (h : semTyped GF n Γ e (.ref A)) :
    semTyped GF n Γ (.load e) A := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h δ γ $$ Hctx with H
  simp only [exprInterp, Exp.substMap, typeInterp_ref, refInterp_car]
  iapply swp_bind_load
  iapply swp_wand $$ H
  iintro %v ⟨%l, %hv, #Hinv⟩
  subst hv
  iapply ImpredInvariants.inv_open (N := logN) (by simp) $$ Hinv
  iintro HI
  unfold refInv
  swp_enter Hcl
  icases HI with ⟨%w, >Hl, #Hw⟩
  wp_load
  imod Hcl
  imodintro
  isplitl [Hl]
  · inext
    iexists w
    isplitl [Hl]
    · iexact Hl
    · iexact Hw
  · iexact Hw

theorem compat_store {e₁ e₂ : Exp} (h₁ : semTyped GF n Γ e₁ (.ref A))
    (h₂ : semTyped GF n Γ e₂ A) : semTyped GF n Γ (.store e₁ e₂) .unit := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases semTyped_apply h₁ δ γ $$ Hctx with H1
  icases semTyped_apply h₂ δ γ $$ Hctx with H2
  simp only [exprInterp, Exp.substMap, typeInterp_ref, refInterp_car, typeInterp_unit,
    unitInterp_car]
  iapply swp_bind_storeR
  iapply swp_wand $$ H2
  iintro %v₂ Hv₂
  iapply swp_bind_storeL
  iapply swp_wand $$ H1
  iintro %v₁ ⟨%l, %hv, #Hinv⟩
  subst hv
  iapply ImpredInvariants.inv_open (N := logN) (by simp) $$ Hinv
  iintro HI
  unfold refInv
  swp_enter Hcl
  icases HI with ⟨%w, >Hl, _⟩
  wp_store
  imod Hcl
  imodintro
  isplitl [Hl Hv₂]
  · inext
    iexists v₂
    isplitl [Hl]
    · iexact Hl
    · iexact Hv₂
  · ipureintro; rfl

end Compat

/-- The fundamental theorem: every syntactically typed term is semantically typed. -/
theorem fundamental {n : Nat} {Γ : TypingContext} {e : Exp} {A : Ty} (h : SynTyped n Γ e A) :
    semTyped GF n Γ e A := by
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

/-! ## A mutable bit

The file's own `mutbit` section: the program is safe because the location only ever holds `0` or
`1`, which a plain invariant records — no ghost state needed. `assertE` is the course's `assert`;
`ghost_state_sol.v` declares the same thing, and `GhostState.lean` reuses this one. -/

/-- The course's `assert`: a failed assertion applies an integer to an integer and is stuck. -/
def assertE (e : Exp) : Exp := hl(if &e then #() else #(0 : Int) #(0 : Int))

section MutBit

/-- `(Unit → Unit) × (Unit → Bool)`. -/
def mutbitT : Ty := .prod (.fn .unit .unit) (.fn .unit .bool)

def myMutBit : Exp :=
  hl(let x := ref(#(0 : Int));
     ((λ y, (&(assertE hl(((!x = #(0 : Int)) || (!x = #(1 : Int)))));
             x ← (#(1 : Int) - !x))),
      (λ y, (&(assertE hl(((!x = #(0 : Int)) || (!x = #(1 : Int)))));
             #(0 : Int) < !x))))

def mutbitN : Namespace := nroot .@ "mutbit"

/-- Rocq writes this invariant inline. -/
def mutbitInv (l : Loc) : IProp GF :=
  iprop((l ↦ some hl_val(#(0 : Int))) ∨ (l ↦ some hl_val(#(1 : Int))))

private theorem eq00 : ((hl_val(#(0 : Int)) : Val) == hl_val(#(0 : Int))) = true := rfl
private theorem eq10 : ((hl_val(#(1 : Int)) : Val) == hl_val(#(0 : Int))) = false := rfl
private theorem eq11 : ((hl_val(#(1 : Int)) : Val) == hl_val(#(1 : Int))) = true := rfl
private theorem sub10 : ((1 : Int) - 0) = 1 := by decide
private theorem sub11 : ((1 : Int) - 1) = 0 := by decide
private theorem lt00 : decide ((0 : Int) < 0) = false := by decide
private theorem lt01 : decide ((0 : Int) < 1) = true := by decide

theorem mymutbit_typed : semTyped GF 0 ∅ myMutBit mutbitT := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [Exp.substMap_empty (M := TyMapStr)]
  simp only [exprInterp, myMutBit]
  swp_enter Hcl
  wp_alloc l with Hl
  wp_pures
  imod Iris.inv_alloc mutbitN (∅ : CoPset) (mutbitInv (GF := GF) l) $$ [Hl] with #Hinv
  · inext
    unfold mutbitInv
    ileft
    iexact Hl
  imod Hcl
  imodintro
  simp only [mutbitT, typeInterp_prod, typeInterp_fn, typeInterp_unit, typeInterp_bool,
    prodInterp_car]
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · simp only [funInterp_car, unitInterp_car]
    iintro %w !> %hw
    subst hw
    simp only [exprInterp, assertE]
    swp_pures
    iapply ImpredInvariants.inv_open (N := mutbitN) (by simp) $$ Hinv
    iintro HI
    unfold mutbitInv
    swp_enter Hcl2
    simp only [unitInterp_car]
    icases HI with ⟨>Hl | >Hl⟩
    · wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq00]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      wp_store
      simp only [sub10]
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        iright
        iexact Hl
      · ipureintro; trivial
    · wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq10]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq11]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      wp_store
      simp only [sub11]
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        ileft
        iexact Hl
      · ipureintro; trivial
  · simp only [funInterp_car, unitInterp_car]
    iintro %w !> %hw
    subst hw
    simp only [exprInterp, assertE]
    swp_pures
    iapply ImpredInvariants.inv_open (N := mutbitN) (by simp) $$ Hinv
    iintro HI
    unfold mutbitInv
    swp_enter Hcl2
    simp only [boolInterp_car]
    icases HI with ⟨>Hl | >Hl⟩
    · wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq00]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      simp only [lt00]
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        ileft
        iexact Hl
      · iexists false
        ipureintro; rfl
    · wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq10]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      simp only [eq11]
      wp_pures
      wp_bind (!#l)
      wp_load
      wp_pures
      simp only [lt01]
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        iright
        iexact Hl
      · iexists true
        ipureintro; rfl

end MutBit

end ProgramLogics.LogRel
