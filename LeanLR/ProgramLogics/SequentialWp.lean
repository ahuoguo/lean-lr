import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.WeakestPre
import Iris.Instances.Lib.Invariants
import Iris.ProofMode

/-!
# Program logics: the sequential, two-mask weakest precondition

The port of `program_logics/program_logic/sequential_wp.v`.

The course defines two things in that file:

* `wp'`, a fork- and observation-free copy of Iris's weakest precondition, and
* `swp s E₁ E₂ e Φ := |={E₁,∅}=> wp' s ∅ e (λ v, |={∅,E₂}=> Φ v)`, the *sequential* weakest
  precondition, written `WP e @ s; E₁; E₂ {{ Φ }}`.

Only the second is content. `wp'` is a fork of upstream Iris's WP, and `iris-lean` already provides
the upstream version — so this file keeps the `swp` layer and builds it on `Iris.ProgramLogic.wp`.
Every proof below is the Rocq proof of the corresponding lemma in `Section swp`, with `wp'_*`
replaced by `iris-lean`'s `wp_*`.

Why it matters: sandwiching the execution between `|={E₁,∅}=>` and `|={∅,E₂}=>` means an invariant
opened before the expression runs stays open for the whole of it. That is what makes the course's
`inv_open` derivable, which it is not for the single-mask WP (`CORRESPONDENCE.md` §5.4b); the rule
is at the bottom of this file.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.ProgramLogic.Language

namespace ProgramLogics

section Swp

variable {hlc : outParam HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s s₁ s₂ : Stuckness} {E₁ E₂ E₃ : CoPset} {e : Expr}
variable {P : IProp GF} {Φ Ψ : Val → IProp GF}

/-- The sequential weakest precondition: run `e` with every invariant in `E₁` available to be
opened *before* the first step and closed again *after* the last one, ending in mask `E₂`. -/
def swp (s : Stuckness) (E₁ E₂ : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  iprop(|={E₁, ∅}=> WP e @ s ; (∅ : CoPset) {{ v, |={∅, E₂}=> Φ v }})

-- The braces are spelled `" {" noWs "{ "`, exactly as `Iris.BI.WeakestPre` spells them: a
-- `" {{ "` literal would register `{{` as a single token and break Iris's own `WP e {{ Φ }}`
-- parser in every file that imports this one.
syntax:max "SWP " term:max " @ " term:max "; " term:max ", " term:max
  " {" noWs "{ " term " }" noWs "} " : term
syntax:max "SWP " term:max " @ " term:max "; " term:max ", " term:max
  " {" noWs "{ " ident ", " term " }" noWs "} " : term

macro_rules
  | `(SWP $e @ $s; $E₁, $E₂ {{ $v:ident, $Φ }}) => `(swp $s $E₁ $E₂ $e (fun $v => iprop($Φ)))
  | `(SWP $e @ $s; $E₁, $E₂ {{ $Φ:term }}) => `(swp $s $E₁ $E₂ $e $Φ)

/-! ## The primitive rules -/

theorem swp_value_fupd' (v : Val) :
    swp s E₁ E₂ (v : Expr) Φ ⊣⊢ iprop(|={E₁, E₂}=> Φ v) := by
  unfold swp
  rw [wp_value_fupd'.to_eq]
  constructor
  · exact (fupd_mono fupd_trans).trans fupd_trans
  · exact (fupd_mask_intro_subseteq (by simp)).trans
      (fupd_mono (fupd_trans.trans fupd_intro))

theorem swp_strong_mono (hs : s₁ ≤ s₂) :
    swp s₁ E₁ E₂ e Φ ⊢ iprop((∀ v, Φ v ={E₂, E₃}=∗ Ψ v) -∗ swp s₂ E₁ E₃ e Ψ) := by
  unfold swp
  iintro H HΦ
  imod H with H
  imodintro
  iapply wp_strong_mono hs Iris.Std.LawfulSet.subset_refl $$ H
  iintro %v H
  imodintro
  imod H with H
  iapply HΦ $$ H

/-- A fancy update in front of a sequential WP is absorbed into its opening mask. -/
theorem fupd_swp : iprop(|={E₁, E₂}=> swp s E₂ E₃ e Φ) ⊢ swp s E₁ E₃ e Φ := fupd_trans

/-- A fancy update in the postcondition is absorbed into the closing mask. -/
theorem swp_fupd : swp s E₁ E₂ e (fun v => iprop(|={E₂}=> Φ v)) ⊢ swp s E₁ E₂ e Φ :=
  fupd_mono (wp_mono fun _ => fupd_trans)

/-- The mask-changing form: the postcondition may itself change the mask from `E₁` to `E₂`. -/
theorem swp_fupd' : swp s E₁ E₁ e (fun v => iprop(|={E₁, E₂}=> Φ v)) ⊢ swp s E₁ E₂ e Φ :=
  fupd_mono (wp_mono fun _ => fupd_trans)

theorem swp_bind (K : Expr → Expr) [Language.Context K] :
    swp s E₁ E₂ e (fun v => swp s E₂ E₃ (K (Λ.ofVal v)) Φ) ⊢ swp s E₁ E₃ (K e) Φ := by
  unfold swp
  refine fupd_mono (Entails.trans ?_ (wp_bind K))
  exact wp_mono fun _ => fupd_trans.trans fupd_wp

/-! ## Proof-mode instances

These make `imod` and `iframe` work directly on a `swp` goal, exactly as `iris-lean` provides them
for its own `wp`. -/

instance elimModal_fupd_swp (p : Bool) (io : InOut) (s : Stuckness) (E₁ E₂ E₃ : CoPset)
    (e : Expr) (P : IProp GF) (Φ : Val → IProp GF) :
    ElimModal True p io false iprop(|={E₁, E₂}=> P) P (swp s E₁ E₃ e Φ) (swp s E₂ E₃ e Φ) where
  elim_modal _ := by
    iintro ⟨H1, H2⟩
    iapply fupd_swp (E₂ := E₂)
    icases intuitionisticallyIf_elim $$ H1 with H1
    imod H1
    iapply H2 $$ H1

instance elimModal_bupd_swp (p : Bool) (io : InOut) (s : Stuckness) (E₁ E₂ : CoPset)
    (e : Expr) (P : IProp GF) (Φ : Val → IProp GF) :
    ElimModal True p io false iprop(|==> P) P (swp s E₁ E₂ e Φ) (swp s E₁ E₂ e Φ) where
  elim_modal _ := by
    iintro ⟨H1, H2⟩
    iapply fupd_swp (E₂ := E₁)
    icases intuitionisticallyIf_elim $$ H1 with H1
    icases BIUpdateFUpdate.fupd_of_bupd (E := E₁) $$ H1 with H1
    imod H1
    iapply H2 $$ H1

instance addModal_fupd_swp (s : Stuckness) (E₁ E₂ : CoPset) (e : Expr)
    (P : IProp GF) (Φ : Val → IProp GF) :
    AddModal iprop(|={E₁}=> P) P (swp s E₁ E₂ e Φ) where
  add_modal := by
    iintro ⟨HP, H⟩
    iapply fupd_swp (E₂ := E₁)
    imod HP with HP
    imodintro
    iapply H $$ HP

theorem swp_step_fupd (hv : ToVal.toVal e = none) :
    iprop(|={E₁}[E₂]▷=> P) ⊢
      iprop(swp s E₂ E₂ e (fun v => iprop(P ={E₁, E₃}=∗ Φ v)) -∗ swp s E₁ E₃ e Φ) := by
  have hpost : ∀ v : Val, iprop(|={∅, E₂}=> (P ={E₁, E₃}=∗ Φ v)) ⊢
      iprop((|={E₂, E₁}=> P) ={(∅ : CoPset)}=∗ |={∅, E₃}=> Φ v) := by
    intro v
    iintro H1 H2
    imodintro
    imod H1 with H1
    imod H2 with H2
    iapply H1 $$ H2
  unfold swp
  iintro HR H
  imod HR with HR
  imod H with H
  imodintro
  ihave HR' : |={(∅ : CoPset)}[(∅ : CoPset)]▷=> (|={E₂, E₁}=> P) $$ [HR]
  · iapply step_fupd_intro Iris.Std.LawfulSet.subset_refl
    iexact HR
  iapply wp_step_fupd (P := iprop(|={E₂, E₁}=> P)) hv Iris.Std.LawfulSet.subset_refl $$ HR'
  iapply wp_mono hpost $$ H

/-! ## Derived rules -/

theorem swp_mono (h : ∀ v, Φ v ⊢ Ψ v) : swp s E₁ E₂ e Φ ⊢ swp s E₁ E₂ e Ψ := by
  iintro H
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ H
  iintro %v HΦ
  imodintro
  iapply h v $$ HΦ

theorem swp_stuck_mono (hs : s₁ ≤ s₂) : swp s₁ E₁ E₂ e Φ ⊢ swp s₂ E₁ E₂ e Φ := by
  iintro H
  iapply swp_strong_mono hs $$ H
  iintro %v HΦ
  imodintro
  iexact HΦ

theorem swp_stuck_weaken : swp s E₁ E₂ e Φ ⊢ swp .MaybeStuck E₁ E₂ e Φ :=
  swp_stuck_mono (by cases s <;> simp)

theorem swp_value' (v : Val) : Φ v ⊢ swp s E₁ E₁ (v : Expr) Φ :=
  fupd_intro.trans (swp_value_fupd' v).mpr

theorem swp_value_fupd {v : Val} (h : Language.IntoVal e v) :
    swp s E₁ E₂ e Φ ⊣⊢ iprop(|={E₁, E₂}=> Φ v) := by
  rw [← h.into_val]
  exact swp_value_fupd' v

theorem swp_value {v : Val} (h : Language.IntoVal e v) : Φ v ⊢ swp s E₁ E₁ e Φ := by
  rw [← h.into_val]
  exact swp_value' v

theorem swp_frame_l : iprop(P ∗ swp s E₁ E₂ e Φ) ⊢ swp s E₁ E₂ e (fun v => iprop(P ∗ Φ v)) := by
  iintro ⟨HP, H⟩
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ H
  iintro %v HΦ
  imodintro
  isplitl [HP]
  · iexact HP
  · iexact HΦ

theorem swp_frame_r : iprop(swp s E₁ E₂ e Φ ∗ P) ⊢ swp s E₁ E₂ e (fun v => iprop(Φ v ∗ P)) := by
  iintro ⟨H, HP⟩
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ H
  iintro %v HΦ
  imodintro
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

theorem swp_wand : swp s E₁ E₂ e Φ ⊢ iprop((∀ v, Φ v -∗ Ψ v) -∗ swp s E₁ E₂ e Ψ) := by
  iintro H HΦ
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ H
  iintro %v Hv
  imodintro
  iapply HΦ $$ Hv

theorem swp_wand_l : iprop((∀ v, Φ v -∗ Ψ v) ∗ swp s E₁ E₂ e Φ) ⊢ swp s E₁ E₂ e Ψ := by
  iintro ⟨HΦ, H⟩
  iapply swp_wand $$ H HΦ

theorem swp_wand_r : iprop(swp s E₁ E₂ e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢ swp s E₁ E₂ e Ψ := by
  iintro ⟨H, HΦ⟩
  iapply swp_wand $$ H HΦ

theorem swp_frame_wand :
    P ⊢ iprop(swp s E₁ E₂ e (fun v => iprop(P -∗ Φ v)) -∗ swp s E₁ E₂ e Φ) := by
  iintro HP H
  iapply swp_wand $$ H
  iintro %v HΦ
  iapply HΦ $$ HP

theorem swp_frame_step_l (hv : ToVal.toVal e = none) :
    iprop((|={E₁}[E₂]▷=> P) ∗ swp s E₂ E₂ e (fun v => iprop(|={E₁, E₃}=> Φ v)))
      ⊢ swp s E₁ E₃ e (fun v => iprop(P ∗ Φ v)) := by
  have h : ∀ v : Val, iprop(|={E₁, E₃}=> Φ v) ⊢ iprop(P ={E₁, E₃}=∗ (P ∗ Φ v)) := by
    intro v
    iintro H HP
    imod H with H
    imodintro
    isplitl [HP]
    · iexact HP
    · iexact H
  iintro ⟨Hu, Hwp⟩
  iapply swp_step_fupd hv $$ Hu
  iapply swp_mono h $$ Hwp

theorem swp_frame_step_r (hv : ToVal.toVal e = none) :
    iprop(swp s E₂ E₂ e (fun v => iprop(|={E₁, E₃}=> Φ v)) ∗ (|={E₁}[E₂]▷=> P))
      ⊢ swp s E₁ E₃ e (fun v => iprop(Φ v ∗ P)) := by
  have h : ∀ v : Val, iprop(|={E₁, E₃}=> Φ v) ⊢ iprop(P ={E₁, E₃}=∗ (Φ v ∗ P)) := by
    intro v
    iintro H HP
    imod H with H
    imodintro
    isplitl [H]
    · iexact H
    · iexact HP
  iintro ⟨Hwp, Hu⟩
  iapply swp_step_fupd hv $$ Hu
  iapply swp_mono h $$ Hwp

theorem swp_frame_step_l' (hv : ToVal.toVal e = none) (hE : E₁ ⊆ E₂) :
    iprop(▷ P ∗ swp s E₁ E₂ e Φ) ⊢ swp s E₁ E₂ e (fun v => iprop(P ∗ Φ v)) := by
  iintro ⟨HP, Hwp⟩
  iapply swp_frame_step_l (E₂ := E₁) (E₃ := E₂) hv
  isplitl [HP]
  · iapply step_fupd_intro Iris.Std.LawfulSet.subset_refl
    iexact HP
  · iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ Hwp
    iintro %v HΦ
    iapply fupd_mask_intro_subseteq hE $$ HΦ

theorem swp_frame_step_r' (hv : ToVal.toVal e = none) (hE : E₁ ⊆ E₂) :
    iprop(swp s E₁ E₂ e Φ ∗ ▷ P) ⊢ swp s E₁ E₂ e (fun v => iprop(Φ v ∗ P)) := by
  iintro ⟨Hwp, HP⟩
  iapply swp_frame_step_r (E₂ := E₁) (E₃ := E₂) hv
  isplitl [Hwp]
  · iapply swp_strong_mono (Std.IsPreorder.le_refl s) $$ Hwp
    iintro %v HΦ
    iapply fupd_mask_intro_subseteq hE $$ HΦ
  · iapply step_fupd_intro Iris.Std.LawfulSet.subset_refl
    iexact HP

/-- `swp_bind` in the shape the course uses it: the continuation may move the closing mask. -/
theorem swp_bind' (K : Expr → Expr) [Language.Context K] :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (K (Λ.ofVal v)) Φ) ⊢ swp s E₁ E₂ (K e) Φ :=
  swp_bind K

instance frame_swp {p : Bool} {R : IProp GF} {Φ Ψ : Val → IProp GF}
    [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (swp s E₁ E₂ e Φ) (swp s E₁ E₂ e Ψ) where
  frame := by
    refine swp_frame_l.trans ?_
    exact swp_mono fun v => (H v).frame_instantiatiate_exist_disabled.frame

instance isExcept0Swp {Φ : Val → IProp GF} : IsExcept0 (swp s E₁ E₂ e Φ) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E₁}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E₁}=> _ := BIFUpdate.except0
      _ ⊢ swp s E₁ E₂ e Φ := fupd_swp

/-- The sequential WP is non-expansive in its postcondition. Rocq's `wp_proper`
follows from this by `OFE.NonExpansive.eqv`, and its `wp_mono'`/`wp_flip_mono'` `Proper` instances
are `swp_mono` read through `Entails.trans`. -/
instance swp_ne : OFE.NonExpansive (swp (GF := GF) s E₁ E₂ e) where
  ne {n Φ₁ Φ₂} HΦ := by
    simp only [swp]
    exact fupd_ne.ne (wp_ne.ne fun v => fupd_ne.ne (HΦ v))

/-- An accessor may be opened around a whole sequential WP —
which is the point of the sequential WP, since the mask stays closed for the entire execution. -/
instance elimAcc_swp_nonatomic {X : Type} {E₀ : CoPset} {α β : X → IProp GF}
    {mγ : X → Option (IProp GF)} :
    ElimAcc (X := X) True (fupd E₁ E₀) (fupd E₂ E₂) α β mγ
      (swp s E₁ E₂ e Φ)
      (fun x => swp s E₀ E₂ e (fun v => iprop(|={E₂}=> β x ∗ (mγ x -∗? Φ v)))) where
  elim_acc := by
    simp only [accessor, BIBase.wandM]
    iintro %_ Hinner Hacc
    imod Hacc with ⟨%x, Hα, Hclose⟩
    ispecialize Hinner $$ %x Hα
    iapply swp_fupd
    iapply swp_wand $$ Hinner
    iintro %v HΦ
    imod HΦ with ⟨Hβ, HΦ⟩
    ispecialize Hclose $$ Hβ
    cases (mγ x) with simp_all
    | none =>
      imod Hclose
      iexact HΦ
    | some p =>
      imod Hclose
      iapply HΦ $$ Hclose

end Swp

/-! ## Pure steps

The sequential WP absorbs the `▷` that `wp_pure_step_later` demands: the later can be introduced
underneath the opening `|={E,∅}=>`, so the rules below are later-free, as the course's are. -/

section PureSteps

variable {hlc : outParam HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val] [Inhabited State]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e e' : Expr} {Φ : Val → IProp GF}

/-- A pure step may be taken under a sequential WP, with no later left over. -/
theorem swp_pure_step (h : Language.PureExec True 1 e e') :
    swp s E E e' Φ ⊢ swp s E E e Φ := by
  unfold swp
  refine fupd_mono (Entails.trans ?_ (wp_pure_step_later (n := 1) (Hexec := h) trivial))
  exact later_intro.trans (later_mono (wand_intro sep_elim_left))

/-- Finitely many pure steps. -/
theorem swp_pure_steps {n : Nat} (h : Language.PureExec True n e e') :
    swp s E E e' Φ ⊢ swp s E E e Φ := by
  unfold swp
  refine fupd_mono (Entails.trans ?_ (wp_pure_step_later (n := n) (Hexec := h) trivial))
  exact (laterN_intro n).trans (laterN_mono n (wand_intro sep_elim_left))

/-- The later-carrying form. `swp_pure_step` is stronger as a rule, but this one is what strips
the `▷` from a Löb hypothesis, so it is the form a recursive-function proof needs. The mask can be
handed back and taken again around the step, which is what makes it hold at all. -/
theorem swp_pure_step_later (h : Language.PureExec True 1 e e') :
    iprop(▷ swp s E E e' Φ) ⊢ swp s E E e Φ := by
  unfold swp
  iintro H
  imod (fupd_mask_subseteq (E2 := (∅ : CoPset)) (by simp)) with Hcl
  imodintro
  iapply wp_pure_step_fupd (E₂ := E) (Hexec := h) trivial
  simp only [Nat.repeat]
  imod Hcl
  imodintro
  inext
  imod H
  imodintro
  iintro _
  iexact H

end PureSteps

/-! ## Opening an invariant across a whole expression

This is the rule the sequential WP exists for. It is *not* derivable for the single-mask WP, where
an invariant may only be open across one atomic step. -/

section Invariants

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {N : Namespace} {e : Expr}
variable {F P : IProp GF} {Φ : Val → IProp GF}

/-- An invariant may be held open for the whole of `e`, provided `e` gives it
back in its postcondition.

This is the rule that is *not* available for the single-mask WP. -/
theorem inv_open_swp [Timeless F] (Hsub : ↑N ⊆ E) :
    inv N F ⊢ iprop((F -∗ swp s (E \ ↑N) (E \ ↑N) e (fun v => iprop(F ∗ Φ v))) -∗
      swp s E E e Φ) := by
  iintro #Hinv Hs
  imod inv_acc_timeless Hsub $$ Hinv with ⟨HF, Hcl⟩
  iapply swp_fupd'
  ispecialize Hs $$ HF
  iapply swp_wand $$ Hs
  iintro %v ⟨HF', HΦ⟩
  ispecialize Hcl $$ HF'
  imod Hcl
  imodintro
  iexact HΦ

/-- The entailment form. -/
theorem ent_inv_open [Timeless F] (Hsub : ↑N ⊆ E)
    (h : iprop(P ∗ F) ⊢ swp s (E \ ↑N) (E \ ↑N) e (fun v => iprop(F ∗ Φ v))) :
    iprop(P ∗ inv N F) ⊢ swp s E E e Φ := by
  iintro ⟨HP, #Hinv⟩
  iapply inv_open_swp Hsub $$ Hinv
  iintro HF
  iapply h
  isplitl [HP]
  · iexact HP
  · iexact HF

end Invariants

end ProgramLogics
