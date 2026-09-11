import LeanLR.ProgramLogics.Reloc.Fundamental

/-!
# Adequacy for the binary logical relation

`program_logics/reloc/adequacy.v`. If `e` refines `e'` then `e` is safe and, whenever it returns,
the source returns a related value.

The fork-freedom side condition of `CORRESPONDENCE.md` §5.12 is inherited from
`ProgramLogics.heap_swp_adequacy`.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std FromMathlib
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation
open Iris.ProgramLogic.PrimStep Iris.ProgramLogic.EctxItemLanguage

namespace ProgramLogics.Reloc

/-- A thread step of the source is an erased step of the one-element thread pool. -/
theorem thread_erased_step {e e' : Exp} {σ σ' : State} (h : ThreadStep (e, σ) (e', σ')) :
    ([e], σ) -·->ₜₚ ([e'], σ') :=
  ⟨[], Language.Step.of_primStep (t₁ := []) (t₂ := []) h⟩

theorem rtc_thread_erased_step {e e' : Exp} {σ σ' : State}
    (h : Relation.ReflTransGen ThreadStep (e, σ) (e', σ')) : ([e], σ) -·->ₜₚ* ([e'], σ') := by
  generalize hp : (e, σ) = p at h
  generalize hq : (e', σ') = q at h
  induction h generalizing e σ e' σ' with
  | refl => cases hp; cases hq; exact .refl
  | @tail p q hpq hq' ih =>
    cases hp; cases hq
    cases q with | mk e'' σ'' =>
    exact (ih rfl rfl).tail (thread_erased_step hq')

variable {GF : BundledGFunctors}

/-- The adequacy theorem for `refines`. -/
theorem refines_adequate [RelocGpreS .hasLC GF] (τ : ∀ _ : RelocGS .hasLC GF, SemType GF)
    (φ : Val → Val → Prop) (e e' : Exp) (σ : State) (hσ : σ = mkstate σ.heap)
    (Hpost : ∀ [inst : RelocGS .hasLC GF] (v v' : Val), (τ inst) v v' ⊢ iprop(⌜φ v v'⌝))
    (Hlog : ∀ [inst : RelocGS .hasLC GF], ⊢ refines e e' (τ inst).car)
    (Hnf : ∀ (t2 : List Exp) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1) :
    AdequateNoFork .NotStuck e σ (fun v _ =>
      ∃ (v' : Val) (h' : State),
        Relation.ReflTransGen ThreadStep (e', σ) (hl(v(&v')), h') ∧ φ v v') := by
  refine heap_swp_adequacy (GF := GF) e σ _ ?_ Hnf
  intro instHL
  iapply fupd_swp (E₂ := ⊤)
  imod ghost_map_alloc (H := HeapF) σ.heap with ⟨%γheap, Hauth, _⟩
  imod ghost_var_alloc (A := Exp) e' with ⟨%γexpr, Hexpr⟩
  letI instReloc : RelocGS .hasLC GF :=
    ⟨RelocGpreS.sheap_pre, RelocGpreS.sexpr_pre, γexpr, γheap⟩
  icases ghost_var_split γexpr e' (1 : Qp).half (1 : Qp).half $$ [Hexpr] with ⟨He1, He2⟩
  · ieval (rewrite [Qp.half_add_half])
    iexact Hexpr
  imod Iris.inv_alloc srcN ⊤ (srcInv (hlc := .hasLC) e' σ.heap) $$ [He1 Hauth] with #Hinv
  · inext
    unfold srcInv
    iexists e', σ.heap
    unfold exprS heapSAuth
    iframe He1 Hauth
    ipureintro
    exact .refl
  imodintro
  iapply swp_fupd
  have Hlog' := @Hlog instReloc
  unfold refines at Hlog'
  ihave Hrefines := Hlog'
  have hname : RelocGS.sexprName (hlc := .hasLC) GF = γexpr := rfl
  ispecialize Hrefines $$ %([] : List ECtxItem) [He2]
  · unfold srcExpr srcCtx exprS
    simp only [fill_nil, hname]
    isplitr
    · iexists e', σ.heap
      iexact Hinv
    · iexact He2
  iapply swp_wand $$ Hrefines
  simp only [srcExpr, fill_nil]
  iintro %v ⟨%v', ⟨_, Hsrc⟩, Ht⟩
  simp only [srcInv]
  imod Fupd.fupd_inv_open (E := ⊤) srcN_subseteq_top $$ Hinv
    with ⟨>⟨%e'', %σ'', He, Hheap, %Hstep⟩, Hcl⟩
  icases exprS_agree' $$ [He Hsrc] with ⟨⟨He, Hsrc⟩, %Heq⟩
  · iframe He Hsrc
  subst Heq
  imod Hcl $$ [He Hheap] with _
  · inext
    iexists hl(v(&v')), σ''
    iframe He Hheap
    ipureintro
    exact Hstep
  icases Hpost v v' $$ Ht with %Hp
  imodintro
  ipureintro
  refine ⟨v', mkstate σ'', ?_, Hp⟩
  rw [hσ]
  exact Hstep

/-- Safety of the target, read off the adequacy theorem. -/
theorem refines_typesafety [RelocGpreS .hasLC GF] (τ : ∀ _ : RelocGS .hasLC GF, SemType GF)
    (e e' e₁ : Exp) (σ σ' : State) (hσ : σ = mkstate σ.heap)
    (Hlog : ∀ [inst : RelocGS .hasLC GF], ⊢ refines e e' (τ inst).car)
    (Hnf : ∀ (t2 : List Exp) (σ2 : State), ([e], σ) -·->ₜₚ* (t2, σ2) → t2.length = 1)
    (Hsteps : Relation.ReflTransGen ThreadStep (e, σ) (e₁, σ')) : NotStuck (e₁, σ') := by
  refine (refines_adequate (GF := GF) τ (fun _ _ => True) e e' σ hσ ?_ Hlog Hnf).not_stuck rfl
    (rtc_thread_erased_step Hsteps) (List.mem_singleton_self _)
  intro _ v v'
  exact BI.true_intro

end ProgramLogics.Reloc
