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

/-- The expression relation. -/
def exprInterp (τ : SemType GF) (e : Exp) : IProp GF := WP e {{ v, τ v }}

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
      exact BI.wand_ne.ne (p.2.ne h w) (wp_ne.ne fun u => q.2.ne h u)⟩⟩
  | .all A =>
    let p := typeInterpAux A
    ⟨allInterp p.1, ⟨fun {_ _ _} h v => by
      refine BI.intuitionistically_ne.ne (BI.forall_ne fun τ => ?_)
      exact wp_ne.ne fun u => p.2.ne (consEnv_ne .rfl h) u⟩⟩
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

/-- The unfolding equation for a recursive type. -/
theorem typeInterp_mu_unfold (A : Ty) (δ : Env GF) :
    typeInterp (.mu A) δ = muRec (typeInterp A) δ (typeInterp (.mu A) δ) := by
  letI := muRec_contractive (typeInterp (GF := GF) A) (typeInterp_ne A) δ
  exact Iris.fixpoint_unfold (Function.toContractiveHom (muRec (typeInterp A) δ))

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

/-! ## Semantic typing -/

/-- Rocq's `TY n; Γ ⊨ e : A`. The type-variable count `n` is inert here, as in Rocq: the
environment is total. -/
def semTyped (GF : BundledGFunctors) [HeapLangGS hlc GF] (_n : Nat) (Γ : TypingContext) (e : Exp)
    (A : Ty) : Prop :=
  ⊢ (iprop(∀ δ : Env GF, ∀ γ : TyMapStr Val,
    contextInterp Γ γ δ -∗ exprInterp (typeInterp A δ) (e.substMap γ)) : IProp GF)

end ProgramLogics.LogRel
