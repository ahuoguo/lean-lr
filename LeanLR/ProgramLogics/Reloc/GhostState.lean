import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.GhostVar
import LeanLR.ProgramLogics.Fupd
import LeanLR.ProgramLogics.SeqAdequacy

/-!
# Ghost state for the source program

`program_logics/reloc/ghost_state.v`. A binary logical relation has to talk about a *second*
program, the source, which no weakest precondition executes. Its heap and its current expression
are therefore held as ghost state: a ghost map for the heap and a ghost variable, split in half,
for the expression — one half in the invariant of `SrcRules.lean`, one half in the hand of
whoever is proving a refinement.
-/

open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProofMode

namespace ProgramLogics.Reloc

/-- The ghost state a refinement proof allocates. -/
class RelocGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends HeapLangGpreS hlc GF where
  sheap_pre : GhostMapG GF Loc (Option Val) HeapF
  sexpr_pre : GhostVarG GF Exp

attribute [reducible, instance] RelocGpreS.sheap_pre
attribute [reducible, instance] RelocGpreS.sexpr_pre

/-- The ghost state a refinement proof runs in: `HeapLangGS` for the target, a ghost map for the
source heap and a ghost variable for the source expression, each with its name. -/
class RelocGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [heapGS : HeapLangGS hlc GF]
  sheap : GhostMapG GF Loc (Option Val) HeapF
  sexpr : GhostVarG GF Exp
  sexprName : GName
  sheapName : GName

attribute [reducible, instance] RelocGS.heapGS
attribute [reducible, instance] RelocGS.sheap
attribute [reducible, instance] RelocGS.sexpr

section Definitions

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

/-- The source points-to assertion. -/
def heapSPointsTo (l : Loc) (v : Val) : IProp GF :=
  ghost_map_elem (H := HeapF) (RelocGS.sheapName (hlc := hlc) GF) (.own 1) l (some v)

/-- One half of the ghost variable holding the source expression. -/
def exprS (e : Exp) : IProp GF :=
  ghost_var (RelocGS.sexprName (hlc := hlc) GF) (.own (1 : Qp).half) e

/-- The authoritative source heap. -/
def heapSAuth (σ : HeapF (Option Val)) : IProp GF :=
  ghost_map_auth (H := HeapF) (RelocGS.sheapName (hlc := hlc) GF) (.own 1) σ

@[inherit_doc heapSPointsTo] notation:20 l " ↦ₛ " v => heapSPointsTo l v

instance heapS_pointsto_timeless (l : Loc) (v : Val) :
    Timeless (heapSPointsTo (hlc := hlc) (GF := GF) l v) := by
  unfold heapSPointsTo; infer_instance

instance heapS_auth_timeless (σ : HeapF (Option Val)) :
    Timeless (heapSAuth (hlc := hlc) (GF := GF) σ) := by
  unfold heapSAuth; infer_instance

instance exprS_timeless (e : Exp) : Timeless (exprS (hlc := hlc) (GF := GF) e) := by
  unfold exprS; infer_instance

end Definitions

section PointsTo

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]
variable {l : Loc} {v v₁ v₂ w : Val} {σ : HeapF (Option Val)}

theorem pointstoS_agree :
    ⊢@{IProp GF} (heapSPointsTo (hlc := hlc) l v₁) -∗ (l ↦ₛ v₂) -∗ ⌜v₁ = v₂⌝ := by
  unfold heapSPointsTo
  iintro H1 H2
  icases ghost_map_elem_agree (H := HeapF) _ l _ _ (some v₁) (some v₂) $$ [H1 H2] with %Ha
  · iframe H1 H2
  ipureintro
  exact Option.some.inj Ha

theorem heapS_lookup :
    ⊢@{IProp GF} (heapSAuth (hlc := hlc) σ) -∗ (l ↦ₛ v) -∗ ⌜get? σ l = some (some v)⌝ := by
  unfold heapSAuth heapSPointsTo
  exact ghost_map_lookup

/-- Agreement keeps the points-to assertions; the conclusion is pure. -/
theorem heapS_lookup' :
    iprop(heapSAuth (hlc := hlc) (GF := GF) σ ∗ (l ↦ₛ v)) ⊢
      iprop((heapSAuth σ ∗ (l ↦ₛ v)) ∗ ⌜get? σ l = some (some v)⌝) := by
  refine (BI.and_intro .rfl ?_).trans BI.persistent_and_sep_mp
  iintro ⟨Hauth, Hl⟩
  iapply heapS_lookup $$ Hauth Hl

theorem heapS_insert (h : get? σ l = none) :
    ⊢@{IProp GF} (heapSAuth (hlc := hlc) σ) -∗
      |==> (heapSAuth (insert (M := HeapF) σ l (some v)) ∗ (l ↦ₛ v)) := by
  unfold heapSAuth heapSPointsTo
  exact ghost_map_insert l (some v) h

theorem heapS_update :
    ⊢@{IProp GF} (heapSAuth (hlc := hlc) σ) -∗ (l ↦ₛ v) -∗
      |==> (heapSAuth (insert (M := HeapF) σ l (some w)) ∗ (l ↦ₛ w)) := by
  unfold heapSAuth heapSPointsTo
  exact ghost_map_update (some w)

theorem heapS_delete :
    ⊢@{IProp GF} (heapSAuth (hlc := hlc) σ) -∗ (l ↦ₛ v) -∗
      |==> heapSAuth (delete (M := HeapF) σ l) := by
  unfold heapSAuth heapSPointsTo
  exact ghost_map_delete l (some v)

end PointsTo

section ExprS

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF] {e e₁ e₂ e₁' : Exp}

theorem exprS_agree : ⊢@{IProp GF} exprS (hlc := hlc) e₁ -∗ exprS e₂ -∗ ⌜e₁ = e₂⌝ := by
  unfold exprS
  exact ghost_var_agree _ e₁ _ e₂ _

/-- Agreement keeps both halves; the conclusion is pure. -/
theorem exprS_agree' :
    iprop(exprS (hlc := hlc) (GF := GF) e₁ ∗ exprS e₂) ⊢
      iprop((exprS e₁ ∗ exprS e₂) ∗ ⌜e₁ = e₂⌝) := by
  refine (BI.and_intro .rfl ?_).trans BI.persistent_and_sep_mp
  iintro ⟨H1, H2⟩
  iapply exprS_agree $$ H1 H2

theorem exprS_update (e₂ : Exp) :
    ⊢@{IProp GF} exprS (hlc := hlc) e₁ -∗ exprS e₁' -∗ |==> (exprS e₂ ∗ exprS e₂) := by
  unfold exprS
  exact ghost_var_update_halves e₂ _ e₁ e₁'

end ExprS

end ProgramLogics.Reloc
