import LeanLR.ProgramLogics.LogRel.LogRel
import LeanLR.ProgramLogics.SeqAdequacy

/-!
# Logical relations: adequacy

The port of `program_logics/logrel/adequacy.v`. A semantically typed closed term is safe, and
therefore — by `fundamental` — so is a syntactically typed one.

Both statements carry the fork-freedom side condition of `ProgramLogics.heap_swp_adequacy`; see
`CORRESPONDENCE.md` §5.12.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode Iris.HeapLang
open Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation
open Iris.ProgramLogic.PrimStep

namespace ProgramLogics.LogRel

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The environment that maps every type variable to the empty semantic type. -/
def trivialEnv [HeapLangGS hlc GF] : Env GF :=
  fun _ => mkSemType (fun _ => iprop(False)) inferInstance

/-- A closed, semantically typed term is safe. -/
theorem soundness [HeapLangGpreS .hasLC GF] {e : Exp} {A : Ty} (σ : State)
    (Hlog : ∀ [HeapLangGS .hasLC GF], semTyped GF 0 ∅ e A)
    (Hnf : ∀ (t2 : List Exp) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1) :
    AdequateNoFork .NotStuck e σ (fun _ _ => True) := by
  refine heap_swp_adequacy (GF := GF) e σ (fun _ => True) ?_ Hnf
  intro inst
  have H := (contextInterp_empty (GF := GF) trivialEnv).trans
    (semTyped_apply Hlog trivialEnv (∅ : TyMapStr Val))
  rw [Exp.substMap_empty (M := TyMapStr)] at H
  unfold exprInterp at H
  exact H.trans (swp_mono (fun _ => true_intro))

/-- A closed, syntactically typed term is safe. -/
theorem syn_soundness {e : Exp} {A : Ty} (σ : State) (h : SynTyped 0 ∅ e A)
    (Hnf : ∀ (t2 : List Exp) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1) :
    AdequateNoFork .NotStuck e σ (fun _ _ => True) := by
  refine soundness (GF := HeapLangS) (A := A) σ ?_ Hnf
  intro inst
  exact fundamental h

/-- The form the course states safety in: no reachable thread is stuck. -/
theorem syn_soundness_not_stuck {e e' : Exp} {A : Ty} {σ σ' : State} {tp : List Exp}
    (h : SynTyped 0 ∅ e A)
    (Hnf : ∀ (t2 : List Exp) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1)
    (Hsteps : ([e], σ) -·->ₜₚ* (tp, σ')) (Hin : e' ∈ tp) : NotStuck (e', σ') :=
  (syn_soundness σ h Hnf).not_stuck rfl Hsteps Hin

end ProgramLogics.LogRel
