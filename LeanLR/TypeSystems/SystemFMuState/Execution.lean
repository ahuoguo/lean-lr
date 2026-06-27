/-
  System F with recursive types and mutable state - Execution
  Deterministic stepping, n-step reduction, and heap operation lemmas.
  Ported from semantics-2025/theories/type_systems/systemf_mu_state/execution.v
-/

import LeanLR.TypeSystems.SystemFMuState.Lang

namespace SystemFMuState

-- Deterministic step: e₁ reduces to e₂ purely (same heap) and deterministically
structure DetStep (e₁ e₂ : Expr) : Prop where
  safe : ∀ h, reducible e₁ h
  det : ∀ e₂' h h', ContextualStep (e₁, h) (e₂', h') → e₂' = e₂ ∧ h' = h

-- N-step reduction relation
inductive Nsteps : Nat → (Expr × Heap) → (Expr × Heap) → Prop where
  | zero : Nsteps 0 s s
  | step : ContextualStep s₁ s₂ → Nsteps n s₂ s₃ → Nsteps (n + 1) s₁ s₃

-- N-step reduction to an irreducible expression
def redNsteps (n : Nat) (e : Expr) (h : Heap) (e' : Expr) (h' : Heap) : Prop :=
  Nsteps n (e, h) (e', h') ∧ irreducible e' h'

-- Base step lifts to contextual step via empty context
theorem base_contextual_step {e₁ e₂ : Expr} {h₁ h₂ : Heap} :
    BaseStep (e₁, h₁) (e₂, h₂) → ContextualStep (e₁, h₁) (e₂, h₂) :=
  fun hb => ContextualStep.ectxStep [] e₁ e₂ h₁ h₂ hb

-- Fill with context lifts contextual steps
theorem fill_contextual_step {K : Ectx} {e₁ e₂ : Expr} {h₁ h₂ : Heap} :
    ContextualStep (e₁, h₁) (e₂, h₂) →
    ContextualStep (fill K e₁, h₁) (fill K e₂, h₂) := by
  intro ⟨K', e₁', e₂', _, _, hb⟩
  have hfill : ∀ (A B : Ectx) (x : Expr), fill (A ++ B) x = fill B (fill A x) := by
    intro A B x; simp [fill, List.foldl_append]
  rw [← hfill K' K e₁', ← hfill K' K e₂']
  exact ContextualStep.ectxStep (K' ++ K) e₁' e₂' _ _ hb

-- Values cannot take base steps
theorem val_no_base_step {e : Expr} {h : Heap} {e' : Expr} {h' : Heap} :
    Expr.isVal e → ¬ BaseStep (e, h) (e', h') := by
  intro hval hstep
  cases hstep <;> simp [Expr.isVal] at hval

-- fill lemmas
theorem fill_cons (ki : EctxItem) (K : Ectx) (e : Expr) :
    fill (ki :: K) e = fill K (fillItem ki e) := by
  simp [fill, List.foldl]

@[simp] theorem fill_nil (e : Expr) : fill [] e = e := rfl

-- Custom inversion for ContextualStep that avoids dependent elimination issues.
-- Instead of pattern matching (which requires solving fill K e₁ = specific_expr),
-- we extract the components as existentials.
theorem ContextualStep.inv {p₁ p₂ : Expr × Heap} (h : ContextualStep p₁ p₂) :
    ∃ (K : Ectx) (e₁ e₂ : Expr) (h₁ h₂ : Heap),
      p₁ = (fill K e₁, h₁) ∧ p₂ = (fill K e₂, h₂) ∧ BaseStep (e₁, h₁) (e₂, h₂) := by
  cases h with
  | ectxStep K e₁ e₂ h₁ h₂ hb =>
    exact ⟨K, e₁, e₂, h₁, h₂, rfl, rfl, hb⟩

-- From ContextualStep (expr, h) (e', h'), extract the decomposition
theorem contextual_step_inv {expr e' : Expr} {h h' : Heap}
    (hstep : ContextualStep (expr, h) (e', h')) :
    ∃ (K : Ectx) (e₁ e₂ : Expr),
      fill K e₁ = expr ∧ fill K e₂ = e' ∧ BaseStep (e₁, h) (e₂, h') := by
  obtain ⟨K, e₁, e₂, h₁, h₂, hp₁, hp₂, hbase⟩ := hstep.inv
  simp at hp₁ hp₂
  obtain ⟨hfill₁, hh₁⟩ := hp₁
  obtain ⟨hfill₂, hh₂⟩ := hp₂
  subst hh₁ hh₂
  exact ⟨K, e₁, e₂, hfill₁.symm, hfill₂.symm, hbase⟩

-- Unique decomposition of evaluation contexts.
-- For specific redex forms where all sub-expressions in "value position" are values,
-- the only valid eval context decomposition is K = [].

-- Core decomposition: if `fill K e₁ = redex` and `BaseStep (e₁, h) (e₂, h')`,
-- and the redex is fully applied (all sub-expressions in evaluation position are values),
-- then K must be [].

private theorem unique_decomp_beta (x : Binder) (body arg : Expr) (hval : Expr.isVal arg)
    (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hfill : fill K e₁ = Expr.app (Expr.lam x body) arg)
    (hbase : BaseStep (e₁, h) (e₂, h')) :
    K = [] ∧ e₁ = Expr.app (Expr.lam x body) arg := by
  sorry

private theorem unique_decomp_tBeta (body : Expr)
    (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hfill : fill K e₁ = Expr.tApp (Expr.tLam body))
    (hbase : BaseStep (e₁, h) (e₂, h')) :
    K = [] ∧ e₁ = Expr.tApp (Expr.tLam body) := by
  sorry

private theorem unique_decomp_unpack (x : Binder) (inner body : Expr) (hval : Expr.isVal inner)
    (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hfill : fill K e₁ = Expr.unpack x (Expr.pack inner) body)
    (hbase : BaseStep (e₁, h) (e₂, h')) :
    K = [] ∧ e₁ = Expr.unpack x (Expr.pack inner) body := by
  sorry

private theorem unique_decomp_ite (b : Bool) (et ef : Expr)
    (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hfill : fill K e₁ = Expr.ite (Expr.lit (BaseLit.litBool b)) et ef)
    (hbase : BaseStep (e₁, h) (e₂, h')) :
    K = [] ∧ e₁ = Expr.ite (Expr.lit (BaseLit.litBool b)) et ef := by
  sorry

private theorem unique_decomp_fst (e₁ e₂ : Expr)
    (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂)
    (K : Ectx) (e₁' e₂' : Expr) (h h' : Heap)
    (hfill : fill K e₁' = Expr.fst (Expr.pair e₁ e₂))
    (hbase : BaseStep (e₁', h) (e₂', h')) :
    K = [] ∧ e₁' = Expr.fst (Expr.pair e₁ e₂) := by
  sorry

private theorem unique_decomp_snd (e₁ e₂ : Expr)
    (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂)
    (K : Ectx) (e₁' e₂' : Expr) (h h' : Heap)
    (hfill : fill K e₁' = Expr.snd (Expr.pair e₁ e₂))
    (hbase : BaseStep (e₁', h) (e₂', h')) :
    K = [] ∧ e₁' = Expr.snd (Expr.pair e₁ e₂) := by
  sorry

private theorem unique_decomp_caseL (e e₁ e₂ : Expr) (hv : Expr.isVal e)
    (K : Ectx) (e₁' e₂' : Expr) (h h' : Heap)
    (hfill : fill K e₁' = Expr.case (Expr.injL e) e₁ e₂)
    (hbase : BaseStep (e₁', h) (e₂', h')) :
    K = [] ∧ e₁' = Expr.case (Expr.injL e) e₁ e₂ := by
  sorry

private theorem unique_decomp_caseR (e e₁ e₂ : Expr) (hv : Expr.isVal e)
    (K : Ectx) (e₁' e₂' : Expr) (h h' : Heap)
    (hfill : fill K e₁' = Expr.case (Expr.injR e) e₁ e₂)
    (hbase : BaseStep (e₁', h) (e₂', h')) :
    K = [] ∧ e₁' = Expr.case (Expr.injR e) e₁ e₂ := by
  sorry

private theorem unique_decomp_unroll (e : Expr) (hv : Expr.isVal e)
    (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hfill : fill K e₁ = Expr.unroll (Expr.roll e))
    (hbase : BaseStep (e₁, h) (e₂, h')) :
    K = [] ∧ e₁ = Expr.unroll (Expr.roll e) := by
  sorry

-- Base step determinism for specific redex forms
-- Once we know e₁ is a specific redex, BaseStep determines the unique result.

private theorem base_step_beta_det (x : Binder) (body arg : Expr) (_hval : Expr.isVal arg)
    (e₂ : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.app (Expr.lam x body) arg, h) (e₂, h')) :
    e₂ = subst' x arg body ∧ h' = h := by
  cases hbase with
  | betaS _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_tBeta_det (body : Expr)
    (e₂ : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.tApp (Expr.tLam body), h) (e₂, h')) :
    e₂ = body ∧ h' = h := by
  cases hbase with
  | tBetaS _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_unpack_det (x : Binder) (inner body : Expr) (_hval : Expr.isVal inner)
    (e₂ : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.unpack x (Expr.pack inner) body, h) (e₂, h')) :
    e₂ = subst' x inner body ∧ h' = h := by
  cases hbase with
  | unpackS _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_if_true_det (e₁ e₂ : Expr)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.ite (Expr.lit (BaseLit.litBool true)) e₁ e₂, h) (e₂', h')) :
    e₂' = e₁ ∧ h' = h := by
  cases hbase with
  | ifTrueS _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_if_false_det (e₁ e₂ : Expr)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.ite (Expr.lit (BaseLit.litBool false)) e₁ e₂, h) (e₂', h')) :
    e₂' = e₂ ∧ h' = h := by
  cases hbase with
  | ifFalseS _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_fst_det (e₁ e₂ : Expr)
    (_hv₁ : Expr.isVal e₁) (_hv₂ : Expr.isVal e₂)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.fst (Expr.pair e₁ e₂), h) (e₂', h')) :
    e₂' = e₁ ∧ h' = h := by
  cases hbase with
  | fstS _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_snd_det (e₁ e₂ : Expr)
    (_hv₁ : Expr.isVal e₁) (_hv₂ : Expr.isVal e₂)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.snd (Expr.pair e₁ e₂), h) (e₂', h')) :
    e₂' = e₂ ∧ h' = h := by
  cases hbase with
  | sndS _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_caseL_det (e e₁ e₂ : Expr) (_hv : Expr.isVal e)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.case (Expr.injL e) e₁ e₂, h) (e₂', h')) :
    e₂' = Expr.app e₁ e ∧ h' = h := by
  cases hbase with
  | caseLΞ _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_caseR_det (e e₁ e₂ : Expr) (_hv : Expr.isVal e)
    (e₂' : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.case (Expr.injR e) e₁ e₂, h) (e₂', h')) :
    e₂' = Expr.app e₂ e ∧ h' = h := by
  cases hbase with
  | caseRS _ _ _ _ _ => exact ⟨rfl, rfl⟩

private theorem base_step_unroll_det (e : Expr) (_hv : Expr.isVal e)
    (e₂ : Expr) (h h' : Heap)
    (hbase : BaseStep (Expr.unroll (Expr.roll e), h) (e₂, h')) :
    e₂ = e ∧ h' = h := by
  cases hbase with
  | unrollS _ _ _ => exact ⟨rfl, rfl⟩

-- Main deterministic step proofs.
-- Strategy: use contextual_step_inv to get the decomposition,
-- then unique_decomp to show K = [], then base_step_*_det for the result.

theorem det_step_beta (x : Binder) (e e₂ : Expr) :
    Expr.isVal e₂ → DetStep (.app (.lam x e) e₂) (subst' x e₂ e) := by
  intro hval
  constructor
  · intro h
    exact ⟨subst' x e₂ e, h, base_contextual_step (BaseStep.betaS x e e₂ h hval)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_beta x e e₂ hval K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_beta_det x e e₂ hval eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_tBeta (e : Expr) :
    DetStep (.tApp (.tLam e)) e := by
  constructor
  · intro h
    exact ⟨e, h, base_contextual_step (BaseStep.tBetaS e h)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_tBeta e K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_tBeta_det e eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_unpack (x : Binder) (e₁ e₂ : Expr) :
    Expr.isVal e₁ → DetStep (.unpack x (.pack e₁) e₂) (subst' x e₁ e₂) := by
  intro hval
  constructor
  · intro h
    exact ⟨subst' x e₁ e₂, h, base_contextual_step (BaseStep.unpackS x e₁ e₂ h hval)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_unpack x e₁ e₂ hval K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_unpack_det x e₁ e₂ hval eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_if_true (e₁ e₂ : Expr) :
    DetStep (.ite (.lit (.litBool true)) e₁ e₂) e₁ := by
  constructor
  · intro h
    exact ⟨e₁, h, base_contextual_step (BaseStep.ifTrueS e₁ e₂ h)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_ite true e₁ e₂ K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_if_true_det e₁ e₂ eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_if_false (e₁ e₂ : Expr) :
    DetStep (.ite (.lit (.litBool false)) e₁ e₂) e₂ := by
  constructor
  · intro h
    exact ⟨e₂, h, base_contextual_step (BaseStep.ifFalseS e₁ e₂ h)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_ite false e₁ e₂ K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_if_false_det e₁ e₂ eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_fst (e₁ e₂ : Expr) :
    Expr.isVal e₁ → Expr.isVal e₂ →
    DetStep (.fst (.pair e₁ e₂)) e₁ := by
  intro hv₁ hv₂
  constructor
  · intro h
    exact ⟨e₁, h, base_contextual_step (BaseStep.fstS e₁ e₂ h hv₁ hv₂)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_fst e₁ e₂ hv₁ hv₂ K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_fst_det e₁ e₂ hv₁ hv₂ eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_snd (e₁ e₂ : Expr) :
    Expr.isVal e₁ → Expr.isVal e₂ →
    DetStep (.snd (.pair e₁ e₂)) e₂ := by
  intro hv₁ hv₂
  constructor
  · intro h
    exact ⟨e₂, h, base_contextual_step (BaseStep.sndS e₁ e₂ h hv₁ hv₂)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_snd e₁ e₂ hv₁ hv₂ K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_snd_det e₁ e₂ hv₁ hv₂ eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_caseL (e e₁ e₂ : Expr) :
    Expr.isVal e →
    DetStep (.case (.injL e) e₁ e₂) (.app e₁ e) := by
  intro hv
  constructor
  · intro h
    exact ⟨.app e₁ e, h, base_contextual_step (BaseStep.caseLΞ e e₁ e₂ h hv)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_caseL e e₁ e₂ hv K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_caseL_det e e₁ e₂ hv eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_caseR (e e₁ e₂ : Expr) :
    Expr.isVal e →
    DetStep (.case (.injR e) e₁ e₂) (.app e₂ e) := by
  intro hv
  constructor
  · intro h
    exact ⟨.app e₂ e, h, base_contextual_step (BaseStep.caseRS e e₁ e₂ h hv)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_caseR e e₁ e₂ hv K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_caseR_det e e₁ e₂ hv eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

theorem det_step_unroll (e : Expr) :
    Expr.isVal e →
    DetStep (.unroll (.roll e)) e := by
  intro hv
  constructor
  · intro h
    exact ⟨e, h, base_contextual_step (BaseStep.unrollS e h hv)⟩
  · intro e₂' h h' hstep
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    have ⟨hK, hea⟩ := unique_decomp_unroll e hv K ea eb h h' hfill₁ hbase
    subst hK; simp [fill] at hfill₁ hfill₂ hea
    subst hea
    have ⟨hr, hh⟩ := base_step_unroll_det e hv eb h h' hbase
    rw [← hfill₂, hr, hh]
    exact ⟨rfl, rfl⟩

-- N-step lemmas
theorem contextual_step_red_nsteps {n : Nat} {e e' e'' : Expr} {h h' h'' : Heap} :
    ContextualStep (e, h) (e', h') →
    redNsteps n e' h' e'' h'' →
    redNsteps (n + 1) e h e'' h'' := by
  intro hstep ⟨hnsteps, hirred⟩
  exact ⟨Nsteps.step hstep hnsteps, hirred⟩

theorem det_step_red {e e' e'' : Expr} {h h'' : Heap} {n : Nat} :
    DetStep e e' →
    redNsteps n e h e'' h'' →
    1 ≤ n ∧ redNsteps (n - 1) e' h e'' h'' := by
  intro ⟨hsafe, hdet⟩ ⟨hnsteps, hirred⟩
  cases hnsteps with
  | zero =>
    exfalso
    exact hirred (hsafe _)
  | step hstep hnsteps' =>
    have ⟨heq, hheq⟩ := hdet _ _ _ hstep
    subst heq; subst hheq
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), ⟨hnsteps', hirred⟩⟩

end SystemFMuState
