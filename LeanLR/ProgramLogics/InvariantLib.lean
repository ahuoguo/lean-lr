import LeanLR.ProgramLogics.SequentialWp
import Iris.HeapLang.PrimitiveLaws
import Iris.Instances.Lib.Invariants

/-!
# Impredicative invariants over the sequential WP

`program_logics/invariant_lib.v`, which is also the content of `hoare_lib.v`'s
`impred_invariants` module.

`SequentialWp.lean`'s `inv_open_swp` requires the invariant to be `Timeless`, so that opening it
hands over `F` rather than `▷ F`. Dropping that requirement is what makes invariants
*impredicative*: `F` may itself mention `inv`, and the price is that the rules below traffic in
`▷ F`.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics.ImpredInvariants

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {N : Namespace} {e : Expr}
variable {F P : IProp GF} {Φ : Val → IProp GF}

/-- An invariant may be allocated at any point before the expression runs. -/
theorem inv_alloc : F ⊢ iprop((inv N F -∗ swp s E E e Φ) -∗ swp s E E e Φ) := by
  iintro HF Hs
  imod Iris.inv_alloc N E F $$ HF with #Hinv
  iapply Hs $$ Hinv

/-- An invariant may be held open for the whole of `e`, provided `e` gives it back. Unlike
`inv_open_swp`, `F` need not be `Timeless`; opening therefore yields `▷ F`. -/
theorem inv_open (Hsub : ↑N ⊆ E) :
    inv N F ⊢ iprop((▷ F -∗ swp s (E \ ↑N) (E \ ↑N) e (fun v => iprop(▷ F ∗ Φ v))) -∗
      swp s E E e Φ) := by
  iintro #Hinv Hs
  imod Iris.inv_acc Hsub $$ Hinv with ⟨HF, Hcl⟩
  iapply swp_fupd'
  ispecialize Hs $$ HF
  iapply swp_wand $$ Hs
  iintro %v ⟨HF', HΦ⟩
  ispecialize Hcl $$ HF'
  imod Hcl
  imodintro
  iexact HΦ

/-- The entailment form. -/
theorem ent_inv_open (Hsub : ↑N ⊆ E)
    (h : iprop(P ∗ ▷ F) ⊢ swp s (E \ ↑N) (E \ ↑N) e (fun v => iprop(▷ F ∗ Φ v))) :
    iprop(P ∗ inv N F) ⊢ swp s E E e Φ := by
  iintro ⟨HP, #Hinv⟩
  iapply inv_open Hsub $$ Hinv
  iintro HF
  iapply h
  isplitl [HP]
  · iexact HP
  · iexact HF

end ProgramLogics.ImpredInvariants
