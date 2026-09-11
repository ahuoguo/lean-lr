import Iris.ProgramLogic.Adequacy
import Iris.HeapLang.PrimitiveLaws
import LeanLR.ProgramLogics.SequentialWp

/-!
# Program logics: adequacy for the sequential weakest precondition

The port of `program_logics/program_logic/adequacy.v` and of the `heap_adequacy` of
`program_logics/heap_lang/adequacy.v`.

The course forks Iris's adequacy proof because its `swp` opens every invariant *before* the
expression runs and closes them only at the end: the thread pool is therefore run at mask `∅`,
not at `⊤`. `iris-lean`'s `Iris.ProgramLogic.Adequacy` is the same development at mask `⊤`, so
this file is that development again with the thread-pool mask taken to be `∅`. The mask `⊤` is
still the one we start from — `swp .NotStuck ⊤ ⊤` spends it on its leading `|={⊤,∅}=>` — and
`fupd_finally_soundness` is applied at `⊤` accordingly.

The course's `wp'` builds `⌜efs = []⌝` into the weakest precondition, so a `swp` thread can never
fork. `iris-lean`'s `wp` hard-codes forked threads at mask `⊤`, where they cannot be stepped while
a sequential thread holds every invariant open, and it does not prove `efs = []`. The lemmas below
therefore take fork-freedom of the run as a hypothesis; see `CORRESPONDENCE.md` §5.12.
-/

open Iris Iris.OFE Iris.BI Iris.Algebra Iris.Std Iris.ProofMode
open Iris.ProgramLogic Iris.ProgramLogic.PrimStep Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

namespace ProgramLogics

section SeqAdequacy

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Language Expr State Obs Val]
variable {GF : BundledGFunctors} [iG : IrisGS_gen hlc Expr GF]

/-- Along a fork-free run the thread pool never grows. -/
theorem nSteps_length_le {n : Nat} {es1 es2 : List Expr} {σ1 σ2 : State} {κs : List Obs}
    (h : (es1, σ1) -<κs>->ₜₚ^[n] (es2, σ2)) : es1.length ≤ es2.length := by
  generalize hρ1 : (es1, σ1) = ρ1 at h
  generalize hρ2 : (es2, σ2) = ρ2 at h
  induction h generalizing es1 σ1 es2 σ2 with
  | refl ρ => cases hρ1; cases hρ2; exact Nat.le_refl _
  | @cons _ _ ρ_mid _ _ _ hstep _ ih =>
    cases hρ1; cases hρ2
    cases ρ_mid with | mk e_mid σ_mid =>
    refine Nat.le_trans ?_ (ih rfl rfl)
    cases hstep with | atomic _ t₁ t₂ => simp [List.length_append]

/-- The thread pool of a *sequential* weakest precondition: every thread runs at mask `∅`. -/
abbrev swptp (s : Stuckness) (es : List Expr) (Φs : List (Val → IProp GF)) : IProp GF :=
  iprop([∗list] e;Φ ∈ es;Φs, WP e @ s ; (∅ : CoPset) {{ Φ }})

theorem swp_step (s : Stuckness) (e1 : Expr) (σ1 : State)
    (ns : Nat) (κ κs : List Obs) (e2 : Expr) (σ2 : State) (efs : List Expr) (nt : Nat)
    (Φ : Val → IProp GF)
    (Hstep : (e1, σ1) -<κ>-> (e2, σ2, efs)) (Hefs : efs = []) :
    ⊢ stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      WP e1 @ s ; (∅ : CoPset) {{ Φ }}
        ={(∅ : CoPset),∅}=∗
        |={(∅ : CoPset)}▷=>^[iG.numLatersPerStep ns + 1] |={(∅ : CoPset),∅}=>
        stateInterp σ2 (ns + 1) κs nt ∗
        WP e2 @ s ; (∅ : CoPset) {{ Φ }} := by
  subst Hefs
  rw [wp_unfold.to_eq]
  simp only [wp.pre, Language.val_stuck Hstep]
  iintro Hσ Hcred Hwp
  imod Hwp $$ %σ1 %ns %κ %κs %nt Hσ with ⟨%_, Hcont⟩
  imodintro
  ihave Hcont := Hcont $$ %e2 %σ2 %([] : List Expr) %Hstep Hcred
  iapply step_fupdN_wand $$ Hcont
  iintro >⟨HSI, Hwp2, _⟩
  imodintro
  simp only [List.length_nil, Nat.add_zero]
  iframe HSI
  iexact Hwp2

theorem swptp_step (s : Stuckness) (es1 es2 : List Expr)
    (κ κs : List Obs) (σ1 σ2 : State) (ns : Nat) (Φs : List (Val → IProp GF)) (nt : Nat)
    (Hstep : (es1, σ1) -<κ>->ₜₚ (es2, σ2)) (Hlen : es2.length = es1.length) :
    ⊢ stateInterp σ1 ns (κ ++ κs) nt -∗
      £ (iG.numLatersPerStep ns + 1) -∗
      swptp s es1 Φs -∗
      |={(∅ : CoPset),∅}=> |={(∅ : CoPset)}▷=>^[iG.numLatersPerStep ns + 1]
        |={(∅ : CoPset),∅}=>
        stateInterp σ2 (ns + 1) κs nt ∗ swptp s es2 Φs := by
  cases Hstep with | @atomic e1' _ _ e2' _ efs H_prim t₁ t₂ =>
  have Hefs : efs = [] := by
    simp only [List.length_append, List.length_cons] at Hlen
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst Hefs
  iintro Hσ Hcred Hwptp
  icases BigSepL2.bigSepL2_app_inv_left $$ Hwptp with ⟨%Φs1, %Φs2, %hΦs, Hwptp1, Hwptp2⟩
  icases BigSepL2.bigSepL2_cons_inv_left $$ Hwptp2 with ⟨%Φ_head, %Φs2', %hΦs2, Hwp_e1, Hwptp3⟩
  subst hΦs hΦs2
  imod swp_step (Hstep := H_prim) (Hefs := rfl) $$ Hσ Hcred Hwp_e1 with Hstep
  imodintro
  iapply step_fupdN_wand $$ Hstep
  iintro >⟨HSI, Hwp_e2⟩
  imodintro
  iframe HSI
  icases BigSepL2.bigSepL2_length $$ Hwptp1 with %Hlen1
  simp only [List.append_nil]
  iapply BigSepL2.bigSepL2_append (.inl Hlen1); iframe Hwptp1
  iapply BigSepL2.bigSepL2_cons; iframe Hwp_e2 Hwptp3

theorem swp_not_stuck (κs : List Obs) (nt : Nat) (e : Expr) (σ : State)
    (ns : Nat) (Φ : Val → IProp GF) :
    ⊢ stateInterp σ ns κs nt -∗
      WP e @ Stuckness.NotStuck ; (∅ : CoPset) {{ Φ }} ={(∅ : CoPset),∅}=∗
      ⌜NotStuck (e, σ)⌝ := by
  rw [wp_unfold.to_eq]
  unfold wp.pre
  match h : ToVal.toVal e with
  | some v =>
    dsimp only
    iintro _ _
    imodintro
    ipureintro
    exact .inl (by rw [h]; rfl)
  | none =>
    dsimp only
    iintro Hst Hcont
    ispecialize Hcont $$ %σ %ns %([]) %κs %nt
    rw [List.nil_append]
    imod Hcont $$ Hst with ⟨%H, _⟩
    imodintro
    ipureintro
    exact .inr H

theorem swptp_preservation (s : Stuckness) (n : Nat) (es1 es2 : List Expr)
    (κs κs' : List Obs) (σ1 σ2 : State) (ns : Nat)
    (Φs : List (Val → IProp GF)) (nt : Nat)
    (Hsteps : (es1, σ1) -<κs>->ₜₚ^[n] (es2, σ2)) (Hlen : es2.length = es1.length) :
    ⊢ stateInterp σ1 ns (κs ++ κs') nt -∗
      £ (steps_sum iG.numLatersPerStep ns n) -∗
      swptp s es1 Φs ={(∅ : CoPset),∅}=∗
      |={(∅ : CoPset)}▷=>^[steps_sum iG.numLatersPerStep ns n] |={(∅ : CoPset),∅}=>
        stateInterp σ2 (n + ns) κs' nt ∗ swptp s es2 Φs := by
  revert Hlen
  generalize hρ1 : (es1, σ1) = ρ1 at Hsteps
  generalize hρ2 : (es2, σ2) = ρ2 at Hsteps
  induction Hsteps generalizing nt κs' Φs ns es1 σ1 es2 σ2 with
  | refl ρ =>
    cases hρ1; cases hρ2; intro _
    simp only [Nat.zero_add, List.nil_append, steps_sum, Nat.repeat]
    iintro Hσ _ Hwptp
    imodintro
    imodintro
    iframe Hσ
    iexact Hwptp
  | @cons n_inner ρ1' ρ_mid ρ2' obs obs' hstep hrest ih =>
    cases hρ1; cases hρ2; intro Hlen
    cases ρ_mid with | mk e_mid σ_mid =>
    have Hmid : e_mid.length = es1.length := by
      have h1 : es1.length ≤ e_mid.length := nSteps_length_le (.cons hstep (.refl _))
      have h2 : e_mid.length ≤ es2.length := nSteps_length_le hrest
      omega
    rw [List.append_assoc obs obs' κs']
    dsimp only [steps_sum]
    rw [Nat.repeat_add]
    iintro Hσ ⟨Hcred1, Hcred2⟩ Hwptp
    icases swptp_step s es1 e_mid obs (obs' ++ κs') σ1 σ_mid ns Φs nt hstep Hmid
            $$ Hσ Hcred1 Hwptp with >Hwptp_step
    imodintro
    iapply step_fupdN_S_fupd.2
    iapply step_fupdN_wand $$ Hwptp_step
    iintro >⟨HSI, Hwptp_mid⟩
    imod ih _ _ _ _ _ _ _ _ rfl rfl (by omega) $$ HSI Hcred2 Hwptp_mid with Hih
    imodintro
    iapply step_fupdN_wand $$ Hih
    iintro >⟨HSI', Hwptp'⟩
    rw [Nat.add_comm _ 1, ←Nat.add_assoc]
    iframe HSI' Hwptp'

theorem swptp_postconditions (Φs : List (Val → IProp GF)) (s : Stuckness) (es : List Expr) :
    swptp s es Φs ={(∅ : CoPset)}=∗ [∗list] e;Φ ∈ es;Φs, (ToVal.toVal e).elim iprop(True) Φ := by
  iintro Ht
  iapply BigSepL2.bigSepL2_fupd
  iapply BigSepL2.bigSepL2_impl $$ Ht
  iintro !> %k %x1 %x2 %Hin %Hlen Hwp
  cases hv : ToVal.toVal x1
  · imodintro; apply true_intro
  · simp only [Option.elim_some]
    iapply wp_value_fupd $$ Hwp
    constructor; grind

/-! ## The adequacy theorem -/

omit iG in
theorem swp_strong_adequacy_gen [InvGpreS GF] (s : Stuckness) (es : List Expr) (σ1 : State)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (σ2 : State) (φ : Prop)
    (numLaters : Nat → Nat) (Hwp : ∀ [InvGS_gen hlc GF],
      ⊢ |={⊤,(∅ : CoPset)}=>
        ∃ (stateI : State → Nat → List Obs → Nat → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Val → IProp GF)
          (mono : ∀ σ ns obs nt, stateI σ ns obs nt ⊢ |={∅}=> stateI σ (ns + 1) obs nt),
        let _ : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLaters forkPost mono
        iprop(stateI σ1 0 κs 0 ∗
          ([∗list] e;Φ ∈ es;Φs, WP e @ s ; (∅ : CoPset) {{ Φ }}) ∗
          (⌜∀ e2, s = .NotStuck → e2 ∈ t2 → NotStuck (e2, σ2)⌝ -∗
            stateI σ2 n [] 0 -∗
            ([∗list] e;Φ ∈ t2;Φs, (toVal e).elim iprop(True) Φ) -∗
            |={(∅ : CoPset),∅}=> ⌜φ⌝)))
    (Hsteps : (es, σ1) -<κs>->ₜₚ^[n] (t2, σ2)) (Hlen : t2.length = es.length) :
    φ := by
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := steps_sum numLaters 0 n + 1)
  rw [(laterN_succ_right _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness hlc (steps_sum numLaters 0 n) ⊤
  iintro %Hinv Hf
  iapply fupd_fupd_finally ⊤ (∅ : CoPset)
  imod Hwp with ⟨%stateI, %Φs, %forkPost, %mono, HSI_init, Hwptp, Hφ⟩
  letI iG : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLaters forkPost mono
  imod swptp_preservation (κs' := []) (Hsteps := Hsteps) (Hlen := Hlen)
    $$ [HSI_init] Hf Hwptp with H
  · simp only [List.append_nil]; iframe
  rw [Nat.add_zero]
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  imodintro
  iintro >⟨Hσ, Ht⟩
  iapply fupd_finally_keep iprop(⌜∀ e2, s = .NotStuck → e2 ∈ t2 → NotStuck (e2, σ2)⌝)
  isplit
  · iintro %e %Heq %Hin
    subst s
    obtain ⟨i, He⟩ := List.getElem?_of_mem Hin
    icases BigSepL2.bigSepL2_lookup_left $$ Ht with ⟨%Φ', _, He⟩; exact He
    imod swp_not_stuck $$ Hσ He with %_
    itrivial
  iintro %_
  imod swptp_postconditions $$ Ht with Ht
  imod Hφ $$ [] Hσ Ht with %_ <;> ipureintro <;> assumption

omit iG in
theorem swp_adequacy_gen [InvGpreS GF] (s : Stuckness) (e : Expr) (σ : State) (φ : Val → Prop)
    (Hwp : ∀ [InvGS_gen hlc GF] (κs : List Obs),
        ⊢ iprop(|={⊤,(∅ : CoPset)}=>
          ∃ (stateI : State → List Obs → IProp GF) (forkPost : Val → IProp GF),
          letI _ : IrisGS_gen hlc Expr GF :=
            .mk (toStateInterp := ⟨fun σ _ κs _ => stateI σ κs⟩) (fun _ => 0) forkPost
              (fun _ _ _ _ => fupd_intro)
          iprop(stateI σ κs ∗ WP e @ s ; (∅ : CoPset) {{ v, ⌜φ v⌝ }})))
    (Hnf : ∀ (t2 : List Expr) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1) :
    AdequateNoFork s e σ (fun v _ => φ v) := by
  refine ⟨fun {t2 σ2} h => Hnf t2 σ2 h, ?_, ?_⟩ <;> intro t₂ σ₂
  · intro v₂ hreach
    obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
    have hlen1 : (ToVal.ofVal v₂ :: t₂).length = ([e] : List Expr).length := by
      simpa using Hnf _ _ hreach
    refine swp_strong_adequacy_gen (GF := GF) (hlc := hlc) s [e] σ n κs _ σ₂ _
      (fun _ => 0) ?_ hsteps hlen1
    iintro %Hinv
    imod Hwp κs with ⟨%Hst, %Hfork, ⟨Hst, Hwp⟩⟩
    iexists (fun σ _ κs _ => Hst σ κs), [(fun v => iprop(⌜φ v⌝))], Hfork,
      (fun _ _ _ _ => fupd_intro)
    dsimp only
    imodintro
    iframe
    isplitl
    · iapply BigSepL2.bigSepL2_nil; itrivial
    iintro %_ Hst Hpost
    icases BigSepL2.bigSepL2_cons_inv_left $$ Hpost with ⟨%Φ', %Φs', %Heq, Hpost, H⟩
    rw [List.cons.injEq] at Heq
    obtain ⟨rfl, rfl⟩ := Heq
    simp only [ToVal.toVal_coe, Option.elim_some]
    icases Hpost with %Hpost
    imodintro
    ipureintro
    exact Hpost
  · intro e₂ hs hreach hmem
    obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
    have hlen1 : t₂.length = ([e] : List Expr).length := by simpa using Hnf _ _ hreach
    refine swp_strong_adequacy_gen (GF := GF) (hlc := hlc) s [e] σ n κs _ σ₂ _
      (fun _ => 0) ?_ hsteps hlen1
    iintro %Hinv
    imod Hwp κs with ⟨%Hst, %Hfork, ⟨Hst, Hwp⟩⟩
    iexists (fun σ _ κs _ => Hst σ κs), [(fun v => iprop(⌜φ v⌝))], Hfork,
      (fun _ _ _ _ => fupd_intro)
    dsimp only
    imodintro
    iframe
    isplitl
    · iapply BigSepL2.bigSepL2_nil; itrivial
    iintro %HNS _ _
    imodintro
    ipureintro
    exact HNS e₂ hs hmem

/-- Shrinking the closing mask of a mask-changing update. -/
theorem fupd_mask_shrink {E1 E2 E3 : CoPset} {P : IProp GF}
    (h : E3 ⊆ E2) : iprop(|={E1,E2}=> P) ⊢ iprop(|={E1,E3}=> P) := by
  iintro H
  imod H
  iapply fupd_mask_intro_discard h
  iexact H

/-- A sequential weakest precondition with a pure postcondition is a mask-`∅` weakest
precondition behind one mask-closing update. -/
theorem swp_to_wp_pure {s : Stuckness} {e : Expr} {φ : Val → Prop} :
    swp s ⊤ ⊤ e (fun v => iprop(⌜φ v⌝)) ⊢
      (iprop(|={⊤,(∅ : CoPset)}=> WP e @ s ; (∅ : CoPset) {{ v, ⌜φ v⌝ }}) : IProp GF) := by
  unfold swp
  iintro H
  imod H
  imodintro
  iapply wp_fupd
  iapply wp_mono _ $$ H
  intro v
  exact fupd_mask_shrink LawfulSet.empty_subset

end SeqAdequacy

section HeapLangSeqAdequacy

open Iris.HeapLang Iris.Std.LawfulPartialMap

/-- `heap_adequacy` for the sequential weakest precondition, along a fork-free run. -/
theorem heap_swp_adequacy {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF]
    (e : Exp) (σ : Iris.HeapLang.State) (φ : Iris.HeapLang.Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF],
      ⊢@{IProp GF} swp .NotStuck ⊤ ⊤ e (fun v => iprop(⌜φ v⌝)))
    (Hnf : ∀ (t2 : List Exp) (σ2 : Iris.HeapLang.State),
      ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1) :
    AdequateNoFork .NotStuck e σ (fun v _ => φ v) := by
  refine swp_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck e σ φ ?_ Hnf
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun v : Option Iris.HeapLang.Val => toAgree (DiscreteO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (DiscreteO.mk g)) (∅ : HeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  imod (ProphMap.init (H := ProphMapF) κs σ.usedProphId) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC GF := ⟨⟨γh, γm⟩, Gproph⟩
  ihave Hswp := (@Hwp instHeapLangGS)
  imod swp_to_wp_pure $$ Hswp with Hw
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  iframe Hw Hproph
  simp only [Iris.genHeapInterp]
  iexists (∅ : HeapF GName)
  unfold ghost_map_auth
  iframe Hh Hm
  ipureintro
  intro k hk
  simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk

end HeapLangSeqAdequacy

end ProgramLogics
