import LeanLR.ProgramLogics.InvariantLib

/-!
# Fancy updates

`program_logics/fupd.v`. The axiomatic rules the lecture notes give for `|={E₁,E₂}=>`, and the
four derived ones the file leaves as an exercise.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics.Fupd

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E E₁ E₂ E₃ : CoPset} {N : Namespace} {e : Expr}
variable {P Q : IProp GF} {Φ : Val → IProp GF}

/-! ## The axiomatic rules -/

theorem fupd_return : P ⊢ iprop(|={E, E}=> P) := fupd_intro

theorem fupd_bind : iprop((|={E₁, E₂}=> P) ∗ (P -∗ |={E₂, E₃}=> Q)) ⊢ iprop(|={E₁, E₃}=> Q) := by
  iintro ⟨>HP, HPQ⟩
  iapply HPQ $$ HP

theorem fupd_swp' : iprop(|={E₁, E₂}=> swp s E₂ E₃ e Φ) ⊢ swp s E₁ E₃ e Φ := fupd_swp

theorem fupd_swp_mask : iprop(|={E}=> swp s E E e Φ) ⊢ swp s E E e Φ := fupd_swp

theorem fupd_timeless [Timeless P] : iprop(▷ P) ⊢ iprop(|={E}=> P) := by
  iintro >HP
  iexact HP

theorem fupd_inv_open (Hsub : ↑N ⊆ E) :
    inv N P ⊢ iprop(|={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True)) := by
  iintro #Hinv
  imod Iris.inv_acc Hsub $$ Hinv with ⟨HP, Hcl⟩
  imodintro
  isplitl [HP]
  · iexact HP
  · iintro HP
    imod Hcl $$ HP
    imodintro
    itrivial

theorem fupd_intro_mask (h : E₂ ⊆ E₁) :
    iprop(|={E₁}=> P) ⊢ iprop(|={E₁, E₂}=> |={E₂, E₁}=> P) := by
  iintro HP
  iapply fupd_mask_intro h
  iintro Hcl
  imod Hcl
  iexact HP

/-! ## The derived rules -/

theorem fupd_wand : ⊢@{IProp GF} iprop(|={E₁, E₂}=> P) -∗ (P -∗ Q) -∗ |={E₁, E₂}=> Q := by
  iintro HP HPQ
  iapply fupd_bind
  isplitl [HP]
  · iexact HP
  · iintro HP
    iapply fupd_return
    iapply HPQ $$ HP

theorem fupd_mono (h : P ⊢ Q) : iprop(|={E₁, E₂}=> P) ⊢ iprop(|={E₁, E₂}=> Q) := by
  iintro HP
  iapply fupd_wand $$ HP
  iintro HP
  iapply h $$ HP

theorem fupd_trans' : iprop(|={E₁, E₂}=> |={E₂, E₃}=> P) ⊢ iprop(|={E₁, E₃}=> P) := by
  iintro HP
  iapply fupd_bind
  isplitl [HP]
  · iexact HP
  · iintro $

theorem fupd_frame : ⊢@{IProp GF} P -∗ iprop(|={E₁, E₂}=> Q) -∗ |={E₁, E₂}=> (P ∗ Q) := by
  iintro HP HQ
  iapply fupd_wand $$ HQ
  iintro HQ
  iframe HP HQ

end ProgramLogics.Fupd
