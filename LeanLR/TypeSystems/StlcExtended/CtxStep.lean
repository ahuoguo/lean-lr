import LeanLR.TypeSystems.StlcExtended.Lang

/-!
# Extended STLC: contextual small-step semantics

Base reduction under an evaluation context. Evaluation is right to left: in a binary construct the
left operand may step only once the right one is a value, which is what the `…LCtx` frames record
by holding a `Val`.
-/

namespace StlcExtended

/-! ## Base reduction -/

inductive BaseStep : Expr → Expr → Prop where
  | betaS {x : Binder} {e₁ e₂ e' : Expr} :
      e₂.isVal →
      e' = subst' x e₂ e₁ →
      BaseStep (.app (.lam x e₁) e₂) e'
  | plusS {e₁ e₂ : Expr} {n₁ n₂ n₃ : Int} :
      e₁ = .litInt n₁ →
      e₂ = .litInt n₂ →
      n₁ + n₂ = n₃ →
      BaseStep (.plus e₁ e₂) (.litInt n₃)
  | fstS {e₁ e₂ : Expr} :
      e₁.isVal → e₂.isVal →
      BaseStep (.fst (.pair e₁ e₂)) e₁
  | sndS {e₁ e₂ : Expr} :
      e₁.isVal → e₂.isVal →
      BaseStep (.snd (.pair e₁ e₂)) e₂
  | caseLS {e e₁ e₂ : Expr} :
      e.isVal →
      BaseStep (.case (.injL e) e₁ e₂) (.app e₁ e)
  | caseRS {e e₁ e₂ : Expr} :
      e.isVal →
      BaseStep (.case (.injR e) e₁ e₂) (.app e₂ e)

/-! ## Evaluation contexts -/

/-- An evaluation context, given as a tree with a single hole. -/
inductive Ectx where
  | holeCtx
  | appLCtx (K : Ectx) (v₂ : Val)
  | appRCtx (e₁ : Expr) (K : Ectx)
  | plusLCtx (K : Ectx) (v₂ : Val)
  | plusRCtx (e₁ : Expr) (K : Ectx)
  | pairLCtx (K : Ectx) (v₂ : Val)
  | pairRCtx (e₁ : Expr) (K : Ectx)
  | fstCtx (K : Ectx)
  | sndCtx (K : Ectx)
  | injLCtx (K : Ectx)
  | injRCtx (K : Ectx)
  | caseCtx (K : Ectx) (e₁ e₂ : Expr)

/-- Plugs an expression into the hole of a context. -/
def fill : Ectx → Expr → Expr
  | .holeCtx, e => e
  | .appLCtx K v₂, e => .app (fill K e) v₂.toExpr
  | .appRCtx e₁ K, e => .app e₁ (fill K e)
  | .plusLCtx K v₂, e => .plus (fill K e) v₂.toExpr
  | .plusRCtx e₁ K, e => .plus e₁ (fill K e)
  | .pairLCtx K v₂, e => .pair (fill K e) v₂.toExpr
  | .pairRCtx e₁ K, e => .pair e₁ (fill K e)
  | .fstCtx K, e => .fst (fill K e)
  | .sndCtx K, e => .snd (fill K e)
  | .injLCtx K, e => .injL (fill K e)
  | .injRCtx K, e => .injR (fill K e)
  | .caseCtx K e₁ e₂, e => .case (fill K e) e₁ e₂

/-- Plugs a context into the hole of another context. -/
def compEctx : Ectx → Ectx → Ectx
  | .holeCtx, K' => K'
  | .appLCtx K v₂, K' => .appLCtx (compEctx K K') v₂
  | .appRCtx e₁ K, K' => .appRCtx e₁ (compEctx K K')
  | .plusLCtx K v₂, K' => .plusLCtx (compEctx K K') v₂
  | .plusRCtx e₁ K, K' => .plusRCtx e₁ (compEctx K K')
  | .pairLCtx K v₂, K' => .pairLCtx (compEctx K K') v₂
  | .pairRCtx e₁ K, K' => .pairRCtx e₁ (compEctx K K')
  | .fstCtx K, K' => .fstCtx (compEctx K K')
  | .sndCtx K, K' => .sndCtx (compEctx K K')
  | .injLCtx K, K' => .injLCtx (compEctx K K')
  | .injRCtx K, K' => .injRCtx (compEctx K K')
  | .caseCtx K e₁ e₂, K' => .caseCtx (compEctx K K') e₁ e₂

/-! ## Contextual steps -/

inductive ContextualStep : Expr → Expr → Prop where
  | ectxStep {e₁ e₂ : Expr} (K : Ectx) (e₁' e₂' : Expr) :
      e₁ = fill K e₁' →
      e₂ = fill K e₂' →
      BaseStep e₁' e₂' →
      ContextualStep e₁ e₂

/-- An expression is reducible when it can take a contextual step. -/
def reducible (e : Expr) : Prop := ∃ e', ContextualStep e e'

/-- The reflexive-transitive closure of `ContextualStep`. -/
inductive ContextualSteps : Expr → Expr → Prop where
  | refl {e} : ContextualSteps e e
  | step {e₁ e₂ e₃} : ContextualStep e₁ e₂ → ContextualSteps e₂ e₃ → ContextualSteps e₁ e₃

theorem ContextualSteps.trans {e₁ e₂ e₃ : Expr}
    (h₁ : ContextualSteps e₁ e₂) (h₂ : ContextualSteps e₂ e₃) : ContextualSteps e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem ContextualSteps.single {e₁ e₂ : Expr} (h : ContextualStep e₁ e₂) :
    ContextualSteps e₁ e₂ := .step h .refl

/-- The empty evaluation context. -/
def emptyEctx : Ectx := .holeCtx

@[simp] theorem fill_empty (e : Expr) : fill emptyEctx e = e := rfl

theorem fill_comp (K₁ K₂ : Ectx) (e : Expr) : fill K₁ (fill K₂ e) = fill (compEctx K₁ K₂) e := by
  induction K₁ <;> simp_all [fill, compEctx]

theorem base_contextual_step {e₁ e₂ : Expr} (h : BaseStep e₁ e₂) : ContextualStep e₁ e₂ :=
  .ectxStep emptyEctx e₁ e₂ rfl rfl h

theorem fill_contextual_step (K : Ectx) {e₁ e₂ : Expr} (h : ContextualStep e₁ e₂) :
    ContextualStep (fill K e₁) (fill K e₂) := by
  obtain ⟨K', e₁', e₂', rfl, rfl, hb⟩ := h
  rw [fill_comp, fill_comp]
  exact .ectxStep _ _ _ rfl rfl hb

/-! ## Structural congruence rules

These recover the shape of a structural operational semantics from the contextual one. -/

theorem contextual_step_app_l {e₁ e₁' e₂ : Expr} (hv : e₂.isVal) (h : ContextualStep e₁ e₁') :
    ContextualStep (.app e₁ e₂) (.app e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (.appLCtx .holeCtx v) h

theorem contextual_step_app_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.app e₁ e₂) (.app e₁ e₂') :=
  fill_contextual_step (.appRCtx e₁ .holeCtx) h

theorem contextual_step_plus_l {e₁ e₁' e₂ : Expr} (hv : e₂.isVal) (h : ContextualStep e₁ e₁') :
    ContextualStep (.plus e₁ e₂) (.plus e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (.plusLCtx .holeCtx v) h

theorem contextual_step_plus_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.plus e₁ e₂) (.plus e₁ e₂') :=
  fill_contextual_step (.plusRCtx e₁ .holeCtx) h

theorem contextual_step_pair_l {e₁ e₁' e₂ : Expr} (hv : e₂.isVal) (h : ContextualStep e₁ e₁') :
    ContextualStep (.pair e₁ e₂) (.pair e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (.pairLCtx .holeCtx v) h

theorem contextual_step_pair_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.pair e₁ e₂) (.pair e₁ e₂') :=
  fill_contextual_step (.pairRCtx e₁ .holeCtx) h

theorem contextual_step_fst {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.fst e) (.fst e') :=
  fill_contextual_step (.fstCtx .holeCtx) h

theorem contextual_step_snd {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.snd e) (.snd e') :=
  fill_contextual_step (.sndCtx .holeCtx) h

theorem contextual_step_injl {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.injL e) (.injL e') :=
  fill_contextual_step (.injLCtx .holeCtx) h

theorem contextual_step_injr {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.injR e) (.injR e') :=
  fill_contextual_step (.injRCtx .holeCtx) h

theorem contextual_step_case {e e' : Expr} (e₁ e₂ : Expr) (h : ContextualStep e e') :
    ContextualStep (.case e e₁ e₂) (.case e' e₁ e₂) :=
  fill_contextual_step (.caseCtx .holeCtx e₁ e₂) h

end StlcExtended
