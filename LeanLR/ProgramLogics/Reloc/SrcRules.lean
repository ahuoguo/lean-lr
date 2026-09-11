import LeanLR.ProgramLogics.Reloc.GhostState

/-!
# Stepping the source program

`program_logics/reloc/src_rules.v`. The source is not run by any weakest precondition: its
progress is recorded in an invariant saying that the ghost expression and ghost heap are
*reachable* from the initial configuration. Taking a source step is then a fancy update that
opens that invariant, updates the two ghost pieces and extends the reachability proof.
-/

open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProofMode Iris.ProgramLogic
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation
open Iris.ProgramLogic.EctxLanguage FromMathlib

namespace ProgramLogics.Reloc

/-! ## Single-thread steps

Iris's language interface allows forking and observations; the source thread does neither. -/

/-- One step of the single source thread. -/
def ThreadStep (p q : Exp × State) : Prop :=
  (p.1, p.2) -<([] : List Observation)>-> (q.1, q.2, ([] : List Exp))

theorem prim_thread_step {e₁ e₂ : Exp} {σ₁ σ₂ : State}
    (h : (e₁, σ₁) -<([] : List Observation)>-> (e₂, σ₂, ([] : List Exp))) :
    ThreadStep (e₁, σ₁) (e₂, σ₂) := h

theorem pure_thread_step {e₁ e₂ : Exp} (σ : State) (h : e₁ -ᵖ-> e₂) :
    ThreadStep (e₁, σ) (e₂, σ) := by
  obtain ⟨e₂', σ₂', efs, hstep⟩ := h.safe σ
  obtain ⟨_, rfl, rfl, rfl⟩ := h.deterministic hstep
  exact hstep

theorem baseStep_thread_step {e e' : Exp} {σ σ' : State}
    (h : HeapLang.BaseStep e σ [] e' σ' []) : ThreadStep (e, σ) (e', σ') :=
  EctxLanguage.primStep_of_baseStep h

theorem fill_thread_step {e₁ e₂ : Exp} {σ₁ σ₂ : State} (K : List ECtxItem)
    (h : ThreadStep (e₁, σ₁) (e₂, σ₂)) : ThreadStep (fill K e₁, σ₁) (fill K e₂, σ₂) :=
  EctxLanguage.fill_primStep K h

theorem rtc_fill_thread_step {e₁ e₂ : Exp} {σ₁ σ₂ : State} (K : List ECtxItem)
    (h : Relation.ReflTransGen ThreadStep (e₁, σ₁) (e₂, σ₂)) :
    Relation.ReflTransGen ThreadStep (fill K e₁, σ₁) (fill K e₂, σ₂) := by
  generalize hp : (e₁, σ₁) = p at h
  generalize hq : (e₂, σ₂) = q at h
  induction h generalizing e₁ σ₁ e₂ σ₂ with
  | refl => cases hp; cases hq; exact .refl
  | @tail p q hpq hq' ih =>
    cases hp; cases hq
    cases q with | mk e' σ' =>
    exact (ih rfl rfl).tail (fill_thread_step K hq')

/-! ## Namespaces -/

def relocN : Namespace := nroot .@ "reloc"

/-- For the source invariant. -/
def srcN : Namespace := relocN .@ "src"

/-- For the location invariants of the logical relation. -/
def logN : Namespace := relocN .@ "log"

theorem srcN_subseteq_top : (↑srcN : CoPset) ⊆ (⊤ : CoPset) := fun _ _ => CoPset.mem_full

theorem logN_subseteq_top : (↑logN : CoPset) ⊆ (⊤ : CoPset) := fun _ _ => CoPset.mem_full

/-- The source invariant and the location invariants live in disjoint namespaces, so the former
is still available while one of the latter is open. -/
theorem srcN_subseteq_diff_logN : (↑srcN : CoPset) ⊆ (⊤ : CoPset) \ ↑logN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun hq => ndot_ne_disjoint relocN (by decide) p ⟨hp, hq⟩⟩

/-! ## The source invariant -/

/-- HeapLang's state carries prophecy variables as well as a heap; the source uses none. -/
def mkstate (σ : HeapF (Option Val)) : State := { heap := σ, usedProphId := ∅ }

section Invariant

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

/-- The source expression and heap are whatever the source has reached from `(e₀, σ₀)`. -/
def srcInv (e₀ : Exp) (σ₀ : HeapF (Option Val)) : IProp GF :=
  iprop(∃ (e : Exp) (σ : HeapF (Option Val)), exprS e ∗ heapSAuth σ ∗
    ⌜Relation.ReflTransGen ThreadStep (e₀, mkstate σ₀) (e, mkstate σ)⌝)

/-- The invariant, with the initial configuration hidden: this is what gets threaded through
every refinement proof. -/
def srcCtx : IProp GF :=
  iprop(∃ (e₀ : Exp) (σ₀ : HeapF (Option Val)), inv srcN (srcInv e₀ σ₀))

instance src_ctx_persistent : Persistent (srcCtx (hlc := hlc) (GF := GF)) := by
  unfold srcCtx; infer_instance

end Invariant

/-! ## Stepping the source -/

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]
variable {E : CoPset} {K : List ECtxItem} {e₁ e₂ : Exp} {l : Loc} {v w : Val}

theorem src_step_pure (hpure : e₁ -ᵖ-> e₂) (hE : ↑srcN ⊆ E) :
    ⊢@{IProp GF} srcCtx -∗ exprS (fill K e₁) ={E}=∗ exprS (fill K e₂) := by
  unfold srcCtx
  iintro ⟨%e₀, %σ₀, #Hinv⟩ Hsrc
  simp only [srcInv]
  imod Fupd.fupd_inv_open hE $$ Hinv with ⟨>⟨%e₁', %σ, He1', Hauth, %Hstep⟩, Hclose⟩
  icases exprS_agree' $$ [He1' Hsrc] with ⟨⟨He1', Hsrc⟩, %Heq⟩
  · iframe He1' Hsrc
  subst Heq
  imod exprS_update (fill K e₂) $$ Hsrc He1' with ⟨Hsrc, He2⟩
  imod Hclose $$ [He2 Hauth] with _
  · inext
    iexists (fill K e₂), σ
    iframe He2 Hauth
    ipureintro
    exact Hstep.tail (fill_thread_step K (pure_thread_step _ hpure))
  imodintro
  iexact Hsrc

private theorem src_step_iterate (hE : ↑srcN ⊆ E) :
    ∀ (n : Nat) (e₁ e₂ : Exp), Relation.Iterate Language.PurePrimStep n e₁ e₂ →
      ⊢@{IProp GF} srcCtx -∗ exprS (fill K e₁) ={E}=∗ exprS (fill K e₂) := by
  intro n
  induction n with
  | zero =>
    intro e₁ e₂ h
    cases h
    iintro _ $
  | succ n ih =>
    intro e₁ e₂ h
    cases h with | tail e' hrest hstep =>
    iintro #Hctx Hsrc
    imod ih e₁ e' hrest $$ Hctx Hsrc with Hsrc
    iapply src_step_pure hstep hE $$ Hctx Hsrc

theorem src_step_pures {φ : Prop} {n : Nat} (hφ : φ)
    [h : Language.PureExec φ n e₁ e₂] (hE : ↑srcN ⊆ E) :
    ⊢@{IProp GF} srcCtx -∗ exprS (fill K e₁) ={E}=∗ exprS (fill K e₂) :=
  src_step_iterate hE n e₁ e₂ (h.pureExec hφ)

theorem src_step_load (hE : ↑srcN ⊆ E) :
    ⊢@{IProp GF} srcCtx -∗ exprS (fill K hl(!#l)) -∗ (l ↦ₛ v) ={E}=∗
      (exprS (fill K hl(v(&v))) ∗ (l ↦ₛ v)) := by
  unfold srcCtx
  iintro ⟨%e₀, %σ₀, #Hinv⟩ Hsrc Hl
  simp only [srcInv]
  imod Fupd.fupd_inv_open hE $$ Hinv with ⟨>⟨%e₁', %σ, He1', Hauth, %Hstep⟩, Hclose⟩
  icases exprS_agree' $$ [He1' Hsrc] with ⟨⟨He1', Hsrc⟩, %Heq⟩
  · iframe He1' Hsrc
  subst Heq
  icases heapS_lookup' $$ [Hauth Hl] with ⟨⟨Hauth, Hl⟩, %Hlook⟩
  · iframe Hauth Hl
  imod exprS_update (fill K hl(v(&v))) $$ Hsrc He1' with ⟨Hsrc, He2⟩
  imod Hclose $$ [He2 Hauth] with _
  · inext
    iexists (fill K hl(v(&v))), σ
    iframe He2 Hauth
    ipureintro
    refine Hstep.tail (fill_thread_step K ?_)
    exact baseStep_thread_step (HeapLang.BaseStep.loadS l v (mkstate σ) Hlook)
  imodintro
  iframe Hsrc Hl

theorem src_step_store (hE : ↑srcN ⊆ E) :
    ⊢@{IProp GF} srcCtx -∗ exprS (fill K hl(#l ← v(&w))) -∗ (l ↦ₛ v) ={E}=∗
      (exprS (fill K hl(#())) ∗ (l ↦ₛ w)) := by
  unfold srcCtx
  iintro ⟨%e₀, %σ₀, #Hinv⟩ Hsrc Hl
  simp only [srcInv]
  imod Fupd.fupd_inv_open hE $$ Hinv with ⟨>⟨%e₁', %σ, He1', Hauth, %Hstep⟩, Hclose⟩
  icases exprS_agree' $$ [He1' Hsrc] with ⟨⟨He1', Hsrc⟩, %Heq⟩
  · iframe He1' Hsrc
  subst Heq
  icases heapS_lookup' $$ [Hauth Hl] with ⟨⟨Hauth, Hl⟩, %Hlook⟩
  · iframe Hauth Hl
  imod exprS_update (fill K hl(#())) $$ Hsrc He1' with ⟨Hsrc, He2⟩
  imod heapS_update (w := w) $$ Hauth Hl with ⟨Hauth, Hl⟩
  imod Hclose $$ [He2 Hauth] with _
  · inext
    iexists (fill K hl(#())), (insert (M := HeapF) σ l (some w))
    iframe He2 Hauth
    ipureintro
    refine Hstep.tail (fill_thread_step K ?_)
    have hstep := baseStep_thread_step (HeapLang.BaseStep.storeS l v w (mkstate σ) Hlook)
    rwa [State.initHeap_singleton] at hstep
  imodintro
  iframe Hsrc Hl

theorem src_step_alloc (hE : ↑srcN ⊆ E) :
    ⊢@{IProp GF} srcCtx -∗ exprS (fill K hl(ref(v(&v)))) ={E}=∗
      ∃ l : Loc, exprS (fill K hl(#l)) ∗ (l ↦ₛ v) := by
  unfold srcCtx
  iintro ⟨%e₀, %σ₀, #Hinv⟩ Hsrc
  simp only [srcInv]
  imod Fupd.fupd_inv_open hE $$ Hinv with ⟨>⟨%e₁', %σ, He1', Hauth, %Hstep⟩, Hclose⟩
  icases exprS_agree' $$ [He1' Hsrc] with ⟨⟨He1', Hsrc⟩, %Heq⟩
  · iframe He1' Hsrc
  subst Heq
  obtain ⟨l, hnone, hfresh⟩ : ∃ l : Loc, get? (M := HeapF) σ l = none ∧
      HeapLang.BaseStep hl(ref(v(&v))) (mkstate σ) [] hl(#l)
        ((mkstate σ).initHeap l 1 (some v)) [] := by
    refine ⟨Loc.fresh (mkstate σ).heap.keys, ?_,
      Iris.HeapLang.alloc_fresh v 1 (mkstate σ) Int.one_pos⟩
    have := Loc.fresh_fresh (mkstate σ).heap.keys (i := 0) (by omega)
    simpa [mkstate, PartialMap.get?, getElem?_eq_none_iff,
      ← Std.ExtTreeMap.mem_keys] using this
  imod exprS_update (fill K hl(#l)) $$ Hsrc He1' with ⟨Hsrc, He2⟩
  imod heapS_insert (v := v) hnone $$ Hauth with ⟨Hauth, Hl⟩
  imod Hclose $$ [He2 Hauth] with _
  · inext
    iexists (fill K hl(#l)), (insert (M := HeapF) σ l (some v))
    iframe He2 Hauth
    ipureintro
    refine Hstep.tail (fill_thread_step K ?_)
    have hstep := baseStep_thread_step hfresh
    rwa [State.initHeap_singleton] at hstep
  imodintro
  iexists l
  iframe Hsrc Hl

end Rules

end ProgramLogics.Reloc
