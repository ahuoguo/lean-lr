import LeanLR.TypeSystems.Stlc.Operational
import LeanLR.TypeSystems.Stlc.Notation

/-!
# Exercise sheet 1

`stlc/exercises01_sol.v`: determinism of the operational semantics, a call-by-name and a
left-to-right semantics for comparison, the reflexive-transitive closure as a general
construction, and the equivalence of the big-step and small-step semantics.

The numbering follows the exercise file; the lecture-note exercise is given in parentheses.
-/

namespace STLC

/-! ## Exercise 4 (LN 3): the reflexive-transitive closure

`Operational.lean`'s `Steps` is this construction at `Step`; the exercise asks for it in
general. -/

inductive Rtc {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base (x : X) : Rtc R x x
  | step (x y z : X) : R x y → Rtc R y z → Rtc R x z

theorem Rtc.refl {X : Type} {R : X → X → Prop} (x : X) : Rtc R x x := .base x

theorem Rtc.trans {X : Type} {R : X → X → Prop} {x y z : X}
    (h₁ : Rtc R x y) (h₂ : Rtc R y z) : Rtc R x z := by
  induction h₁ with
  | base => exact h₂
  | step _ _ _ hr _ ih => exact .step _ _ _ hr (ih h₂)

theorem Rtc.subrel {X : Type} {R : X → X → Prop} {x y : X} (h : R x y) : Rtc R x y :=
  .step _ _ _ h (.base y)

/-- Rocq registers `Reflexive`/`Transitive` instances so that `reflexivity` and `transitivity`
apply; in Lean the corresponding hook is `Trans`, which `calc` uses. -/
instance {X : Type} {R : X → X → Prop} : Trans (Rtc R) (Rtc R) (Rtc R) := ⟨Rtc.trans⟩

theorem steps_iff_rtc {e e' : Expr} : (e ↠* e') ↔ Rtc Step e e' := by
  constructor
  · intro h; induction h with
    | refl => exact .base _
    | step hs _ ih => exact .step _ _ _ hs ih
  · intro h; induction h with
    | base => exact .refl
    | step _ _ _ hs _ ih => exact .step hs ih

/-! ## Exercise 2 (LN 1): deterministic operational semantics -/

private theorem no_step_lam {x : Binder} {e e' : Expr} (h : (Expr.lam x e) ↠ e') : False := by
  have := val_no_step h; simp [Expr.isValue] at this

private theorem no_step_lit {n : Int} {e' : Expr} (h : (Expr.litInt n) ↠ e') : False := by
  have := val_no_step h; simp [Expr.isValue] at this

private theorem step_not_isValue {e e' : Expr} (h : e ↠ e') (hv : e.isValue = true) : False := by
  rw [val_no_step h] at hv; exact Bool.noConfusion hv

theorem step_det {e e' e'' : Expr} (h₁ : e ↠ e') (h₂ : e ↠ e'') : e' = e'' := by
  induction h₁ generalizing e'' with
  | @stepBeta x e e' hv =>
    cases h₂ with
    | stepBeta => rfl
    | stepAppL _ hs => exact absurd hs no_step_lam
    | stepAppR hs => exact absurd (step_not_isValue hs hv) not_false
  | @stepAppL e₁ e₁' e₂ hv hs ih =>
    cases h₂ with
    | stepBeta => exact absurd hs no_step_lam
    | stepAppL _ hs' => rw [ih hs']
    | stepAppR hs' => exact absurd (step_not_isValue hs' hv) not_false
  | @stepAppR e₁ e₂ e₂' hs ih =>
    cases h₂ with
    | stepBeta hv => exact absurd (step_not_isValue hs hv) not_false
    | stepAppL hv _ => exact absurd (step_not_isValue hs hv) not_false
    | stepAppR hs' => rw [ih hs']
  | @stepPlusRed n₁ n₂ n₃ hn =>
    cases h₂ with
    | stepPlusRed hn' => rw [← hn, ← hn']
    | stepPlusL _ hs => exact absurd hs no_step_lit
    | stepPlusR hs => exact absurd hs no_step_lit
  | @stepPlusL e₁ e₁' e₂ hv hs ih =>
    cases h₂ with
    | stepPlusRed => exact absurd hs no_step_lit
    | stepPlusL _ hs' => rw [ih hs']
    | stepPlusR hs' => exact absurd (step_not_isValue hs' hv) not_false
  | @stepPlusR e₁ e₂ e₂' hs ih =>
    cases h₂ with
    | stepPlusRed => exact absurd hs no_step_lit
    | stepPlusL hv _ => exact absurd (step_not_isValue hs hv) not_false
    | stepPlusR hs' => rw [ih hs']

/-! ## Exercise 3 (LN 2): call-by-name semantics -/

inductive CbnStep : Expr → Expr → Prop where
  | beta {x e e'} : CbnStep (.app (.lam x e) e') (subst' x e' e)
  | appL {e₁ e₁' e₂} : CbnStep e₁ e₁' → CbnStep (.app e₁ e₂) (.app e₁' e₂)
  | plusRed {n₁ n₂ n₃ : Int} : n₁ + n₂ = n₃ →
      CbnStep (.plus (.litInt n₁) (.litInt n₂)) (.litInt n₃)
  | plusL {e₁ e₁' e₂} : e₂.isValue = true → CbnStep e₁ e₁' → CbnStep (.plus e₁ e₂) (.plus e₁' e₂)
  | plusR {e₁ e₂ e₂'} : CbnStep e₂ e₂' → CbnStep (.plus e₁ e₂) (.plus e₁ e₂')

theorem val_no_cbn_step {e e' : Expr} (h : CbnStep e e') : e.isValue = false := by
  cases h <;> rfl

private theorem cbn_no_step_lam {x : Binder} {e e' : Expr} (h : CbnStep (.lam x e) e') : False := by
  have := val_no_cbn_step h; simp [Expr.isValue] at this

private theorem cbn_no_step_lit {n : Int} {e' : Expr} (h : CbnStep (.litInt n) e') : False := by
  have := val_no_cbn_step h; simp [Expr.isValue] at this

private theorem cbn_not_isValue {e e' : Expr} (h : CbnStep e e') (hv : e.isValue = true) :
    False := by rw [val_no_cbn_step h] at hv; exact Bool.noConfusion hv

theorem cbn_step_det {e e' e'' : Expr} (h₁ : CbnStep e e') (h₂ : CbnStep e e'') : e' = e'' := by
  induction h₁ generalizing e'' with
  | beta =>
    cases h₂ with
    | beta => rfl
    | appL hs => exact absurd hs cbn_no_step_lam
  | @appL e₁ e₁' e₂ hs ih =>
    cases h₂ with
    | beta => exact absurd hs cbn_no_step_lam
    | appL hs' => rw [ih hs']
  | plusRed hn =>
    cases h₂ with
    | plusRed hn' => rw [← hn, ← hn']
    | plusL _ hs => exact absurd hs cbn_no_step_lit
    | plusR hs => exact absurd hs cbn_no_step_lit
  | @plusL e₁ e₁' e₂ hv hs ih =>
    cases h₂ with
    | plusRed => exact absurd hs cbn_no_step_lit
    | plusL _ hs' => rw [ih hs']
    | plusR hs' => exact absurd (cbn_not_isValue hs' hv) not_false
  | @plusR e₁ e₂ e₂' hs ih =>
    cases h₂ with
    | plusRed => exact absurd hs cbn_no_step_lit
    | plusL hv _ => exact absurd (cbn_not_isValue hs hv) not_false
    | plusR hs' => rw [ih hs']

/-- Call-by-name and call-by-value disagree on the *result*, not just the reduction order. -/
theorem different_results :
    ∃ (e e₁ e₂ : Expr), Rtc CbnStep e e₁ ∧ e ↠* e₂ ∧
      e₁.isValue = true ∧ e₂.isValue = true ∧ e₁ ≠ e₂ := by
  refine ⟨.app (.lam (.named "x") (.lam (.named "y") (.var "x")))
      (.plus (.litInt 4) (.litInt 1)),
    .lam (.named "y") (.plus (.litInt 4) (.litInt 1)),
    .lam (.named "y") (.litInt 5), ?_, ?_, rfl, rfl, by simp⟩
  · exact .step _ _ _ CbnStep.beta (.base _)
  · exact .step (Step.stepAppR (Step.stepPlusRed (by decide)))
      (.step (Step.stepBeta rfl) .refl)

/-! ## Exercise 5 (LN 4): big-step versus small-step -/

theorem plus_right {e₁ e₂ e₂' : Expr} (h : e₂ ↠* e₂') : (Expr.plus e₁ e₂) ↠* (Expr.plus e₁ e₂') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (Step.stepPlusR hs) ih

theorem plus_left {e₁ e₁' : Expr} {n : Int} (h : e₁ ↠* e₁') :
    (Expr.plus e₁ (.litInt n)) ↠* (Expr.plus e₁' (.litInt n)) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (Step.stepPlusL rfl hs) ih

theorem plus_to_consts {e₁ e₂ : Expr} {n m : Int}
    (h₁ : e₁ ↠* .litInt n) (h₂ : e₂ ↠* .litInt m) :
    (Expr.plus e₁ e₂) ↠* .litInt (n + m) :=
  (plus_right h₂).trans ((plus_left h₁).trans (Steps.single (Step.stepPlusRed rfl)))

theorem rtc_step_app_l {e₁ e₁' e₂ : Expr} (h : e₁ ↠* e₁') (hv : e₂.isValue = true) :
    (Expr.app e₁ e₂) ↠* (Expr.app e₁' e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (Step.stepAppL hv hs) ih

theorem rtc_step_app_r {e₁ e₂ e₂' : Expr} (h : e₂ ↠* e₂') :
    (Expr.app e₁ e₂) ↠* (Expr.app e₁ e₂') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (Step.stepAppR hs) ih

theorem rtc_step_plus_l {e₁ e₁' e₂ : Expr} (h : e₁ ↠* e₁') (hv : e₂.isValue = true) :
    (Expr.plus e₁ e₂) ↠* (Expr.plus e₁' e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (Step.stepPlusL hv hs) ih

theorem rtc_step_plus_r {e₁ e₂ e₂' : Expr} (h : e₂ ↠* e₂') :
    (Expr.plus e₁ e₂) ↠* (Expr.plus e₁ e₂') := plus_right h

theorem big_step_steps {e : Expr} {v : Val} (h : e ⇓ v) : e ↠* v.toExpr := by
  induction h with
  | litInt => exact .refl
  | lam => exact .refl
  | @plus e₁ e₂ n₁ n₂ _ _ ih₁ ih₂ =>
    refine (rtc_step_plus_r ih₂).trans ((rtc_step_plus_l ih₁ rfl).trans ?_)
    exact Steps.single (Step.stepPlusRed rfl)
  | @app e₁ e₂ x e v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    refine (rtc_step_app_r ih₂).trans ((rtc_step_app_l ih₁ (val_isValue v₂)).trans ?_)
    exact .step (Step.stepBeta (val_isValue v₂)) ih₃

theorem step_big_step_cons {e e' : Expr} {v : Val} (hs : e ↠ e') (hb : e' ⇓ v) : e ⇓ v := by
  induction hs generalizing v with
  | @stepBeta x e e' hv =>
    obtain ⟨w, rfl⟩ := isValue_exists hv
    exact .app .lam (val_evals_to_self w) hb
  | stepAppL _ _ ih => cases hb with | app h₁ h₂ h₃ => exact .app (ih h₁) h₂ h₃
  | stepAppR _ ih => cases hb with | app h₁ h₂ h₃ => exact .app h₁ (ih h₂) h₃
  | stepPlusRed hn => cases hb with | litInt => subst hn; exact .plus .litInt .litInt
  | stepPlusL _ _ ih => cases hb with | plus h₁ h₂ => exact .plus (ih h₁) h₂
  | stepPlusR _ ih => cases hb with | plus h₁ h₂ => exact .plus h₁ (ih h₂)

/-- A single step to a value is a big step. Rocq proves this first, by inversion; in Lean it
falls out of `step_big_step_cons`. -/
theorem single_step_big_step_cons {e : Expr} {v : Val} (h : e ↠ v.toExpr) : e ⇓ v :=
  step_big_step_cons h (val_evals_to_self v)

theorem steps_big_step_cons {e e' : Expr} {w : Val} (hs : e ↠* e') (hb : e' ⇓ w) : e ⇓ w := by
  induction hs with
  | refl => exact hb
  | step h _ ih => exact step_big_step_cons h (ih hb)

theorem steps_big_step {e : Expr} {v : Val} (h : e ↠* v.toExpr) : e ⇓ v :=
  steps_big_step_cons h (val_evals_to_self v)

/-! ## Exercise 6 (LN 5): left-to-right evaluation -/

inductive LtrStep : Expr → Expr → Prop where
  | beta {x e e'} : e'.isValue = true → LtrStep (.app (.lam x e) e') (subst' x e' e)
  | appL {e₁ e₁' e₂} : LtrStep e₁ e₁' → LtrStep (.app e₁ e₂) (.app e₁' e₂)
  | appR {e₁ e₂ e₂'} : LtrStep e₂ e₂' → e₁.isValue = true → LtrStep (.app e₁ e₂) (.app e₁ e₂')
  | plusRed {n₁ n₂ n₃ : Int} : n₁ + n₂ = n₃ →
      LtrStep (.plus (.litInt n₁) (.litInt n₂)) (.litInt n₃)
  | plusL {e₁ e₁' e₂} : LtrStep e₁ e₁' → LtrStep (.plus e₁ e₂) (.plus e₁' e₂)
  | plusR {e₁ e₂ e₂'} : e₁.isValue = true → LtrStep e₂ e₂' → LtrStep (.plus e₁ e₂) (.plus e₁ e₂')

/-- Left-to-right and right-to-left disagree on which summand runs first. -/
theorem different_steps_ltr_step :
    ∃ (e e₁ e₂ : Expr), LtrStep e e₁ ∧ e ↠ e₂ ∧ e₁ ≠ e₂ := by
  refine ⟨.plus (.plus (.litInt 4) (.litInt 1)) (.plus (.litInt 4) (.litInt 1)), _, _,
    LtrStep.plusL (LtrStep.plusRed rfl), Step.stepPlusR (Step.stepPlusRed rfl), ?_⟩
  simp

theorem rtc_ltr_step_app_l {e₁ e₁' e₂ : Expr} (h : Rtc LtrStep e₁ e₁') :
    Rtc LtrStep (.app e₁ e₂) (.app e₁' e₂) := by
  induction h with
  | base => exact .base _
  | step _ _ _ hs _ ih => exact .step _ _ _ (LtrStep.appL hs) ih

theorem rtc_ltr_step_app_r {e₁ e₂ e₂' : Expr} (h : Rtc LtrStep e₂ e₂') (hv : e₁.isValue = true) :
    Rtc LtrStep (.app e₁ e₂) (.app e₁ e₂') := by
  induction h with
  | base => exact .base _
  | step _ _ _ hs _ ih => exact .step _ _ _ (LtrStep.appR hs hv) ih

theorem rtc_ltr_step_plus_l {e₁ e₁' e₂ : Expr} (h : Rtc LtrStep e₁ e₁') :
    Rtc LtrStep (.plus e₁ e₂) (.plus e₁' e₂) := by
  induction h with
  | base => exact .base _
  | step _ _ _ hs _ ih => exact .step _ _ _ (LtrStep.plusL hs) ih

theorem rtc_ltr_step_plus_r {e₁ e₂ e₂' : Expr} (h : Rtc LtrStep e₂ e₂') (hv : e₁.isValue = true) :
    Rtc LtrStep (.plus e₁ e₂) (.plus e₁ e₂') := by
  induction h with
  | base => exact .base _
  | step _ _ _ hs _ ih => exact .step _ _ _ (LtrStep.plusR hv hs) ih

theorem big_step_ltr_steps {e : Expr} {v : Val} (h : e ⇓ v) : Rtc LtrStep e v.toExpr := by
  induction h with
  | litInt => exact .base _
  | lam => exact .base _
  | @plus e₁ e₂ n₁ n₂ _ _ ih₁ ih₂ =>
    refine Rtc.trans (rtc_ltr_step_plus_l ih₁) (Rtc.trans (rtc_ltr_step_plus_r ih₂ rfl) ?_)
    exact Rtc.subrel (LtrStep.plusRed rfl)
  | @app e₁ e₂ x e v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    refine Rtc.trans (rtc_ltr_step_app_l ih₁) (Rtc.trans (rtc_ltr_step_app_r ih₂ rfl) ?_)
    exact .step _ _ _ (LtrStep.beta (val_isValue v₂)) ih₃

theorem ltr_step_big_step_cons {e e' : Expr} {v : Val} (hs : LtrStep e e') (hb : e' ⇓ v) :
    e ⇓ v := by
  induction hs generalizing v with
  | @beta x e e' hv =>
    obtain ⟨w, rfl⟩ := isValue_exists hv
    exact .app .lam (val_evals_to_self w) hb
  | appL _ ih => cases hb with | app h₁ h₂ h₃ => exact .app (ih h₁) h₂ h₃
  | appR _ _ ih => cases hb with | app h₁ h₂ h₃ => exact .app h₁ (ih h₂) h₃
  | plusRed hn => cases hb with | litInt => cases hn; exact .plus .litInt .litInt
  | plusL _ ih => cases hb with | plus h₁ h₂ => exact .plus (ih h₁) h₂
  | plusR _ _ ih => cases hb with | plus h₁ h₂ => exact .plus h₁ (ih h₂)

theorem ltr_steps_big_step_cons {e e' : Expr} {w : Val} (hs : Rtc LtrStep e e') (hb : e' ⇓ w) :
    e ⇓ w := by
  induction hs with
  | base => exact hb
  | step _ _ _ h _ ih => exact ltr_step_big_step_cons h (ih hb)

theorem ltr_steps_big_step {e : Expr} {v : Val} (h : Rtc LtrStep e v.toExpr) : e ⇓ v :=
  ltr_steps_big_step_cons h (val_evals_to_self v)

end STLC
