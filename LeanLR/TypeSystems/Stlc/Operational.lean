import LeanLR.TypeSystems.Stlc.Lang

namespace STLC

def subst (x : String) (es : Expr) : Expr → Expr
  | Expr.var y => if x = y then es else Expr.var y
  | Expr.lam y e =>
      if Binder.named x = y then
        Expr.lam y e  -- Variable shadowing
      else
        Expr.lam y (subst x es e)
  | Expr.app e₁ e₂ =>
      Expr.app (subst x es e₁) (subst x es e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ =>
      Expr.plus (subst x es e₁) (subst x es e₂)

def subst' (b : Binder) (es : Expr): Expr → Expr :=
  match b with
  | Binder.named x => subst x es
  | _ => id

-- Notation for substitution
notation:90 e "[" x " := " es "]" => subst x es e

inductive BigStep : Expr → Val → Prop where
  | litInt : ∀ {n},
      BigStep (Expr.litInt n) (Val.litIntV n)

  | lam : ∀ {x e},
      BigStep (Expr.lam x e) (Val.lamV x e)

  | app : ∀ {e₁ e₂ x e v₂ v},
      BigStep e₁ (Val.lamV x e) →
      BigStep e₂ v₂ →
      BigStep (subst' x v₂.toExpr e) v →
      BigStep (Expr.app e₁ e₂) v

  | plus : ∀ {e₁ e₂ n₁ n₂},
      BigStep e₁ (Val.litIntV n₁) →
      BigStep e₂ (Val.litIntV n₂) →
      BigStep (Expr.plus e₁ e₂) (Val.litIntV (n₁ + n₂))

notation:50 e " ⇓ " v => BigStep e v

-- Helper: A value evaluates to itself
theorem val_evals_to_self (v : Val) : v.toExpr ⇓ v :=
  match v with
  | Val.litIntV _ => BigStep.litInt
  | Val.lamV _ _ => BigStep.lam

def terminates (e : Expr) : Prop :=
  ∃ v, e ⇓ v

theorem bigstep_deterministic {e : Expr} {v₁ v₂ : Val} (h₁ : e ⇓ v₁) (h₂ : e ⇓ v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | litInt => cases h₂; rfl
  | lam => cases h₂; rfl
  | app he₁ he₂ he₃ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | app he₁' he₂' he₃' =>
      have eq₁ := ih₁ he₁'
      injection eq₁ with h_x h_e
      have eq₂ := ih₂ he₂'
      subst h_x h_e eq₂
      exact ih₃ he₃'
  | plus hp₁ hp₂ ih₁ ih₂ =>
    cases h₂ with
    | plus hp₁' hp₂' =>
      have eq₁ := ih₁ hp₁'
      have eq₂ := ih₂ hp₂'
      injection eq₁ with heq₁
      injection eq₂ with heq₂
      cases heq₁; cases heq₂; rfl

/-! ## Small-step semantics

Evaluation is right to left: in a binary term the left operand may step only once the right one is
already a value. -/

/-- A single structural reduction step. -/
inductive Step : Expr → Expr → Prop where
  | stepBeta {x e e'} :
      e'.isValue = true →
      Step (Expr.app (Expr.lam x e) e') (subst' x e' e)
  | stepAppL {e₁ e₁' e₂} :
      e₂.isValue = true →
      Step e₁ e₁' →
      Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
  | stepAppR {e₁ e₂ e₂'} :
      Step e₂ e₂' →
      Step (Expr.app e₁ e₂) (Expr.app e₁ e₂')
  | stepPlusRed {n₁ n₂ n₃ : Int} :
      n₁ + n₂ = n₃ →
      Step (Expr.plus (Expr.litInt n₁) (Expr.litInt n₂)) (Expr.litInt n₃)
  | stepPlusL {e₁ e₁' e₂} :
      e₂.isValue = true →
      Step e₁ e₁' →
      Step (Expr.plus e₁ e₂) (Expr.plus e₁' e₂)
  | stepPlusR {e₁ e₂ e₂'} :
      Step e₂ e₂' →
      Step (Expr.plus e₁ e₂) (Expr.plus e₁ e₂')

@[inherit_doc] infixr:50 " ↠ " => Step

/-- The reflexive-transitive closure of `Step`. -/
inductive Steps : Expr → Expr → Prop where
  | refl {e} : Steps e e
  | step {e₁ e₂ e₃} : Step e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃

@[inherit_doc] infixr:50 " ↠* " => Steps

/-- `Steps` is transitive. -/
theorem Steps.trans {e₁ e₂ e₃ : Expr} (h₁ : e₁ ↠* e₂) (h₂ : e₂ ↠* e₃) : e₁ ↠* e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact Steps.step hs (ih h₂)

/-- A single step is a reduction sequence. -/
theorem Steps.single {e₁ e₂ : Expr} (h : e₁ ↠ e₂) : e₁ ↠* e₂ := Steps.step h Steps.refl

/-- An expression is reducible when it can take a step. -/
def reducible (e : Expr) : Prop := ∃ e', e ↠ e'

/-- Everything in the image of `Val.toExpr` is a value. -/
@[simp] theorem val_isValue (v : Val) : v.toExpr.isValue = true := by
  cases v <;> rfl

/-- Every value is in the image of `Val.toExpr`; the counterpart of -/
theorem isValue_exists {e : Expr} (h : e.isValue = true) : ∃ v : Val, e = v.toExpr := by
  cases e with
  | litInt n => exact ⟨.litIntV n, rfl⟩
  | lam x e => exact ⟨.lamV x e, rfl⟩
  | _ => simp [Expr.isValue] at h

/-- Values do not step. -/
theorem val_no_step {e e' : Expr} (h : e ↠ e') : e.isValue = false := by
  cases h <;> rfl

/-- A value in the image of `Val.toExpr` does not step. -/
theorem val_no_step' {v : Val} {e : Expr} (h : v.toExpr ↠ e) : False := by
  cases v <;> simp [Val.toExpr] at h <;> cases h

/-! ## Contextual semantics -/

/-- Reduction of a redex. -/
inductive BaseStep : Expr → Expr → Prop where
  | betaS {x e₁ e₂ e'} :
      e₂.isValue = true →
      e' = subst' x e₂ e₁ →
      BaseStep (Expr.app (Expr.lam x e₁) e₂) e'
  | plusS {e₁ e₂ : Expr} {n₁ n₂ n₃ : Int} :
      e₁ = Expr.litInt n₁ →
      e₂ = Expr.litInt n₂ →
      n₁ + n₂ = n₃ →
      BaseStep (Expr.plus e₁ e₂) (Expr.litInt n₃)

/-- An evaluation context, given as a tree with a single hole. -/
inductive Ectx where
  | holeCtx
  | appLCtx (K : Ectx) (v₂ : Val)
  | appRCtx (e₁ : Expr) (K : Ectx)
  | plusLCtx (K : Ectx) (v₂ : Val)
  | plusRCtx (e₁ : Expr) (K : Ectx)

/-- Plugs an expression into the hole of a context. -/
def fill : Ectx → Expr → Expr
  | .holeCtx, e => e
  | .appLCtx K v₂, e => Expr.app (fill K e) v₂.toExpr
  | .appRCtx e₁ K, e => Expr.app e₁ (fill K e)
  | .plusLCtx K v₂, e => Expr.plus (fill K e) v₂.toExpr
  | .plusRCtx e₁ K, e => Expr.plus e₁ (fill K e)

/-- Plugs a context into the hole of another context. -/
def compEctx : Ectx → Ectx → Ectx
  | .holeCtx, Ki => Ki
  | .appLCtx K v₂, Ki => .appLCtx (compEctx K Ki) v₂
  | .appRCtx e₁ K, Ki => .appRCtx e₁ (compEctx K Ki)
  | .plusLCtx K v₂, Ki => .plusLCtx (compEctx K Ki) v₂
  | .plusRCtx e₁ K, Ki => .plusRCtx e₁ (compEctx K Ki)

/-- A reduction step of the whole program: a `BaseStep` under an evaluation context. -/
inductive ContextualStep : Expr → Expr → Prop where
  | ectxStep {e₁ e₂ : Expr} (K : Ectx) (e₁' e₂' : Expr) :
      e₁ = fill K e₁' →
      e₂ = fill K e₂' →
      BaseStep e₁' e₂' →
      ContextualStep e₁ e₂

/-- An expression is contextually reducible when it can take a contextual step. -/
def contextualReducible (e : Expr) : Prop := ∃ e', ContextualStep e e'

/-- The reflexive-transitive closure of `ContextualStep`. -/
inductive ContextualSteps : Expr → Expr → Prop where
  | refl {e} : ContextualSteps e e
  | step {e₁ e₂ e₃} : ContextualStep e₁ e₂ → ContextualSteps e₂ e₃ → ContextualSteps e₁ e₃

/-- The empty evaluation context. -/
def emptyEctx : Ectx := .holeCtx

@[simp] theorem fill_empty (e : Expr) : fill emptyEctx e = e := rfl

/-- Every base step is a contextual step. -/
theorem base_contextual_step {e₁ e₂ : Expr} (h : BaseStep e₁ e₂) : ContextualStep e₁ e₂ :=
  .ectxStep emptyEctx e₁ e₂ rfl rfl h

/-- Nesting contexts corresponds to composing them. -/
theorem fill_comp (K₁ K₂ : Ectx) (e : Expr) : fill K₁ (fill K₂ e) = fill (compEctx K₁ K₂) e := by
  induction K₁ <;> simp_all [fill, compEctx]

/-- Contextual steps are closed under evaluation contexts. -/
theorem fill_contextual_step (K : Ectx) {e₁ e₂ : Expr} (h : ContextualStep e₁ e₂) :
    ContextualStep (fill K e₁) (fill K e₂) := by
  obtain ⟨K', e₁', e₂', rfl, rfl, hb⟩ := h
  rw [fill_comp, fill_comp]
  exact .ectxStep _ _ _ rfl rfl hb

/-! ## Big-step inversion -/

/-- A value evaluates only to itself. -/
theorem big_step_inv_vals {v w : Val} (h : v.toExpr ⇓ w) : v = w := by
  cases v <;> cases h <;> rfl

end STLC
