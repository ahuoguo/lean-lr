import LeanLR.TypeSystems.Stlc.Operational
import LeanLR.TypeSystems.Stlc.ParallelSubst
import LeanLR.TypeSystems.Stlc.Untyped
import LeanLR.TypeSystems.Stlc.TypeSafety

/-!
# STLC, exercise sheet 2

`stlc/exercises02_sol.v`. The structural and contextual semantics agree; Scott encodings of the
booleans and of pairs reduce as expected; a Church-style source calculus erases to the
Curry-style one, its typing is unique and decided by `inferType`; and `ust` is a safe term that
the type system rejects.
-/

namespace STLC

/-! ## Exercise 1: the structural and contextual semantics agree -/

theorem contextual_step_beta {x : Binder} {e e' : Expr} (h : e'.isValue = true) :
    ContextualStep (Expr.app (Expr.lam x e) e') (subst' x e' e) :=
  base_contextual_step (.betaS h rfl)

theorem contextual_step_app_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (Expr.app e₁ e₂) (Expr.app e₁ e₂') :=
  fill_contextual_step (.appRCtx e₁ .holeCtx) h

theorem contextual_step_app_l {e₁ e₁' e₂ : Expr} (hv : e₂.isValue = true)
    (h : ContextualStep e₁ e₁') : ContextualStep (Expr.app e₁ e₂) (Expr.app e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isValue_exists hv
  exact fill_contextual_step (.appLCtx .holeCtx v) h

theorem contextual_step_plus_red {n₁ n₂ n₃ : Int} (h : n₁ + n₂ = n₃) :
    ContextualStep (Expr.plus (Expr.litInt n₁) (Expr.litInt n₂)) (Expr.litInt n₃) :=
  base_contextual_step (.plusS rfl rfl h)

theorem contextual_step_plus_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (Expr.plus e₁ e₂) (Expr.plus e₁ e₂') :=
  fill_contextual_step (.plusRCtx e₁ .holeCtx) h

theorem contextual_step_plus_l {e₁ e₁' e₂ : Expr} (hv : e₂.isValue = true)
    (h : ContextualStep e₁ e₁') : ContextualStep (Expr.plus e₁ e₂) (Expr.plus e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isValue_exists hv
  exact fill_contextual_step (.plusLCtx .holeCtx v) h

theorem step_contextual_step {e₁ e₂ : Expr} (h : e₁ ↠ e₂) : ContextualStep e₁ e₂ := by
  induction h with
  | stepBeta hv => exact contextual_step_beta hv
  | stepAppL hv _ ih => exact contextual_step_app_l hv ih
  | stepAppR _ ih => exact contextual_step_app_r _ ih
  | stepPlusRed h => exact contextual_step_plus_red h
  | stepPlusL hv _ ih => exact contextual_step_plus_l hv ih
  | stepPlusR _ ih => exact contextual_step_plus_r _ ih

theorem base_step_step {e₁ e₂ : Expr} (h : BaseStep e₁ e₂) : e₁ ↠ e₂ := by
  cases h with
  | betaS hv heq => subst heq; exact .stepBeta hv
  | plusS h₁ h₂ h₃ => subst h₁; subst h₂; exact .stepPlusRed h₃

theorem fill_step (K : Ectx) {e₁ e₂ : Expr} (h : e₁ ↠ e₂) : fill K e₁ ↠ fill K e₂ := by
  induction K with
  | holeCtx => exact h
  | appLCtx K v₂ ih => exact .stepAppL (val_isValue v₂) ih
  | appRCtx e₁ K ih => exact .stepAppR ih
  | plusLCtx K v₂ ih => exact .stepPlusL (val_isValue v₂) ih
  | plusRCtx e₁ K ih => exact .stepPlusR ih

theorem contextual_step_step {e₁ e₂ : Expr} (h : ContextualStep e₁ e₂) : e₁ ↠ e₂ := by
  obtain ⟨K, e₁', e₂', rfl, rfl, hb⟩ := h
  exact fill_step K (base_step_step hb)

/-! ## Exercise 2: Scott encodings -/

section Scott

-- The reduction sequences below are written uniformly, with one simp set per step; not every
-- lemma in it fires at every step.
set_option linter.unusedSimpArgs false

def trueScott : Val := λᵥ: t f, "t"
def falseScott : Val := λᵥ: t f, "f"

def pairScott : Val := λᵥ: v1 v2, λ: d, (("d" : Expr) "v1") "v2"

def fstScott : Val := λᵥ: p, ("p" : Expr) (λ: a b, "a")
def sndScott : Val := λᵥ: p, ("p" : Expr) (λ: a b, "b")

/-! The `Val.toExpr` images of the encodings, so that proofs can unfold them without also
unfolding `Val.toExpr` at the arguments — `subst_closed_nil` needs those to stay folded. -/

@[local simp] theorem trueScott_toExpr :
    trueScott.toExpr = Expr.lam (.named "t") (Expr.lam (.named "f") (.var "t")) := rfl

@[local simp] theorem falseScott_toExpr :
    falseScott.toExpr = Expr.lam (.named "t") (Expr.lam (.named "f") (.var "f")) := rfl

@[local simp] theorem pairScott_toExpr :
    pairScott.toExpr = Expr.lam (.named "v1") (Expr.lam (.named "v2")
      (Expr.lam (.named "d") (Expr.app (Expr.app (.var "d") (.var "v1")) (.var "v2")))) := rfl

@[local simp] theorem fstScott_toExpr :
    fstScott.toExpr = Expr.lam (.named "p")
      (Expr.app (.var "p") (Expr.lam (.named "a") (Expr.lam (.named "b") (.var "a")))) := rfl

@[local simp] theorem sndScott_toExpr :
    sndScott.toExpr = Expr.lam (.named "p")
      (Expr.app (.var "p") (Expr.lam (.named "a") (Expr.lam (.named "b") (.var "b")))) := rfl

theorem true_red {v₁ v₂ : Val} (h₁ : v₁.toExpr.closed [] = true)
    (_h₂ : v₂.toExpr.closed [] = true) :
    Expr.app (Expr.app trueScott.toExpr v₁.toExpr) v₂.toExpr ↠* v₁.toExpr := by
  refine .step (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁))) ?_
  simp only [trueScott_toExpr, subst', subst, reduceIte]
  refine .step (.stepBeta (val_isValue v₂)) ?_
  rw [subst', subst_closed_nil h₁]
  exact .refl

theorem false_red {v₁ v₂ : Val} (_h₁ : v₁.toExpr.closed [] = true)
    (_h₂ : v₂.toExpr.closed [] = true) :
    Expr.app (Expr.app falseScott.toExpr v₁.toExpr) v₂.toExpr ↠* v₂.toExpr := by
  refine .step (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁))) ?_
  simp only [falseScott_toExpr, subst', subst, reduceIte]
  refine .step (.stepBeta (val_isValue v₂)) ?_
  rw [subst']
  exact .refl

theorem fst_red {v₁ v₂ : Val} (h₁ : v₁.toExpr.closed [] = true)
    (h₂ : v₂.toExpr.closed [] = true) :
    Expr.app fstScott.toExpr
      (Expr.app (Expr.app pairScott.toExpr v₁.toExpr) v₂.toExpr) ↠* v₁.toExpr := by
  refine .step (.stepAppR (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁)))) ?_
  simp only [pairScott_toExpr, subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepAppR (.stepBeta (val_isValue v₂))) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta rfl) ?_
  simp only [fstScott_toExpr, subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta rfl) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁))) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta (val_isValue v₂)) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂]
  exact .refl

theorem snd_red {v₁ v₂ : Val} (h₁ : v₁.toExpr.closed [] = true)
    (h₂ : v₂.toExpr.closed [] = true) :
    Expr.app sndScott.toExpr
      (Expr.app (Expr.app pairScott.toExpr v₁.toExpr) v₂.toExpr) ↠* v₂.toExpr := by
  refine .step (.stepAppR (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁)))) ?_
  simp only [pairScott_toExpr, subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepAppR (.stepBeta (val_isValue v₂))) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta rfl) ?_
  simp only [sndScott_toExpr, subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta rfl) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepAppL (val_isValue v₂) (.stepBeta (val_isValue v₁))) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂,
    Binder.named.injEq, reduceCtorEq, String.reduceEq, reduceIte, decide_eq_true_eq]
  refine .step (.stepBeta (val_isValue v₂)) ?_
  simp only [subst', subst, subst_closed_nil h₁, subst_closed_nil h₂]
  exact .refl

end Scott

/-! ## Bonus: type erasure -/

/-- Church-style source expressions: lambdas carry the type of their argument. -/
inductive SrcExpr where
  | litInt (n : Int)
  | var (x : String)
  | lam (x : Binder) (A : Ty) (e : SrcExpr)
  | app (e₁ e₂ : SrcExpr)
  | plus (e₁ e₂ : SrcExpr)
  deriving Repr, DecidableEq

/-- Forgetting the type annotations. -/
def erase : SrcExpr → Expr
  | .litInt n => Expr.litInt n
  | .var x => Expr.var x
  | .lam x _ e => Expr.lam x (erase e)
  | .app e₁ e₂ => Expr.app (erase e₁) (erase e₂)
  | .plus e₁ e₂ => Expr.plus (erase e₁) (erase e₂)

/-- Church-style typing of source expressions. -/
inductive SrcTyped : Context → SrcExpr → Ty → Prop where
  | var {Γ x A} : Γ.lookup x = some A → SrcTyped Γ (.var x) A
  | lam {Γ x E A B} : SrcTyped (Γ <[ x := A ]>) E B → SrcTyped Γ (.lam (.named x) A E) (A ⇒ B)
  | int {Γ z} : SrcTyped Γ (.litInt z) Ty.int
  | app {Γ E₁ E₂ A B} :
      SrcTyped Γ E₁ (A ⇒ B) → SrcTyped Γ E₂ A → SrcTyped Γ (.app E₁ E₂) B
  | add {Γ E₁ E₂} :
      SrcTyped Γ E₁ Ty.int → SrcTyped Γ E₂ Ty.int → SrcTyped Γ (.plus E₁ E₂) Ty.int

@[inherit_doc] notation:74 Γ " ⊢S " E " : " A => SrcTyped Γ E A

private theorem type_erasure_correctness_gen {Γ : Context} {E : SrcExpr} {A : Ty}
    (h : Γ ⊢S E : A) : Γ ⊢ erase E : A := by
  induction h with
  | var hx => exact .var hx
  | lam _ ih => exact .lam_named ih
  | int => exact .litInt
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | add _ _ ih₁ ih₂ => exact .plus ih₁ ih₂

theorem type_erasure_correctness {E : SrcExpr} {A : Ty} (h : Context.empty ⊢S E : A) :
    Context.empty ⊢ erase E : A :=
  type_erasure_correctness_gen h

/-! ## Exercise 4: unique typing -/

theorem src_typing_unique {Γ : Context} {E : SrcExpr} {A B : Ty}
    (h₁ : Γ ⊢S E : A) (h₂ : Γ ⊢S E : B) : A = B := by
  induction h₁ generalizing B with
  | var hx => cases h₂ with | var hx' => rw [hx] at hx'; exact Option.some.inj hx'
  | lam _ ih => cases h₂ with | lam h' => exact congrArg _ (ih h')
  | int => cases h₂ with | int => rfl
  | app _ _ ih₁ _ => cases h₂ with | app h₁' _ => exact (Ty.fun.inj (ih₁ h₁')).2
  | add _ _ _ _ => cases h₂ with | add _ _ => rfl

/-- Curry-style typing is *not* unique: the identity has both of the following types. -/
theorem id_int : Context.empty ⊢ (λ: x, "x") : (Ty.int ⇒ Ty.int) :=
  .lam_named (.var (by simp))

theorem id_int_to_int :
    Context.empty ⊢ (λ: x, "x") : ((Ty.int ⇒ Ty.int) ⇒ (Ty.int ⇒ Ty.int)) :=
  .lam_named (.var (by simp))

/-! ## Bonus: type inference -/

def typeEq : Ty → Ty → Bool
  | .int, .int => true
  | .fun A B, .fun A' B' => typeEq A A' && typeEq B B'
  | _, _ => false

theorem type_eq_iff {A B : Ty} : typeEq A B = true ↔ A = B := by
  induction A generalizing B with
  | int => cases B <;> simp [typeEq]
  | «fun» A₁ A₂ ih₁ ih₂ => cases B <;> simp [typeEq, ih₁, ih₂, Ty.fun.injEq]

def inferType (Γ : Context) : SrcExpr → Option Ty
  | .var x => Γ.lookup x
  | .lam (.named x) A E =>
      match inferType (Γ <[ x := A ]>) E with
      | some B => some (A ⇒ B)
      | none => none
  | .litInt _ => some Ty.int
  | .app E₁ E₂ =>
      match inferType Γ E₁, inferType Γ E₂ with
      | some (.fun A B), some C => if typeEq A C then some B else none
      | _, _ => none
  | .plus E₁ E₂ =>
      match inferType Γ E₁, inferType Γ E₂ with
      | some .int, some .int => some Ty.int
      | _, _ => none
  | .lam .anon _ _ => none

theorem infer_type_typing {Γ : Context} {E : SrcExpr} {A : Ty}
    (h : inferType Γ E = some A) : Γ ⊢S E : A := by
  induction E generalizing Γ A with
  | litInt n => cases h; exact .int
  | var x => exact .var h
  | lam x B E ih =>
    cases x with
    | anon => exact absurd h (by simp [inferType])
    | named x =>
      simp only [inferType] at h
      cases heq : inferType (Γ <[ x := B ]>) E with
      | none => rw [heq] at h; exact absurd h (by simp)
      | some C =>
        rw [heq] at h
        cases h
        exact .lam (ih heq)
  | app E₁ E₂ ih₁ ih₂ =>
    simp only [inferType] at h
    cases heq₁ : inferType Γ E₁ with
    | none => rw [heq₁] at h; exact absurd h (by simp)
    | some B =>
      cases B with
      | int => rw [heq₁] at h; exact absurd h (by simp)
      | «fun» B₁ B₂ =>
        cases heq₂ : inferType Γ E₂ with
        | none => rw [heq₁, heq₂] at h; exact absurd h (by simp)
        | some C =>
          rw [heq₁, heq₂] at h
          simp only at h
          split at h
          · rename_i heq₃
            cases h
            rw [type_eq_iff.mp heq₃] at heq₁
            exact .app (ih₁ heq₁) (ih₂ heq₂)
          · exact absurd h (by simp)
  | plus E₁ E₂ ih₁ ih₂ =>
    simp only [inferType] at h
    cases heq₁ : inferType Γ E₁ with
    | none => rw [heq₁] at h; exact absurd h (by simp)
    | some B =>
      cases B with
      | «fun» B₁ B₂ => rw [heq₁] at h; exact absurd h (by simp)
      | int =>
        cases heq₂ : inferType Γ E₂ with
        | none => rw [heq₁, heq₂] at h; exact absurd h (by simp)
        | some C =>
          cases C with
          | «fun» C₁ C₂ => rw [heq₁, heq₂] at h; exact absurd h (by simp)
          | int => cases (by rw [heq₁, heq₂] at h; exact h : some Ty.int = some A); exact .add (ih₁ heq₁) (ih₂ heq₂)

theorem typing_infer_type {Γ : Context} {E : SrcExpr} {A : Ty}
    (h : Γ ⊢S E : A) : inferType Γ E = some A := by
  induction h with
  | var hx => exact hx
  | lam _ ih => simp only [inferType, ih]
  | int => rfl
  | app _ _ ih₁ ih₂ =>
    simp only [inferType, ih₁, ih₂]
    rw [if_pos (type_eq_iff.mpr rfl)]
  | add _ _ ih₁ ih₂ => simp only [inferType, ih₁, ih₂]

/-! ## Exercise 5: an untypable but safe term -/

/-- `(λ f, 5) (λ x, 0 0)`: the ill-typed argument is never used. -/
def ust : Expr := Expr.app (λ: f, ((5 : Int) : Expr)) (λ: x, ((0 : Int) : Expr) ((0 : Int) : Expr))

private theorem ust_step_inv {e : Expr} (h : ust ↠ e) : e = Expr.litInt 5 := by
  cases h with
  | stepBeta hv => rfl
  | stepAppL _ h => exact absurd (val_no_step h) (by simp [Expr.isValue])
  | stepAppR h => exact absurd (val_no_step h) (by simp [Expr.isValue])

theorem ust_safe {e' : Expr} (h : ust ↠* e') : e'.isValue = true ∨ reducible e' := by
  cases h with
  | refl => exact Or.inr ⟨Expr.litInt 5, .stepBeta rfl⟩
  | step h₁ h₂ =>
    rw [ust_step_inv h₁] at h₂
    cases h₂ with
    | refl => exact Or.inl rfl
    | step h => exact absurd (val_no_step h) (by simp [Expr.isValue])

theorem ust_no_type {Γ : Context} {A : Ty} : ¬ (Γ ⊢ ust : A) := by
  intro h
  cases h with
  | app _ h₂ =>
    cases h₂ with
    | lam_named h₃ =>
      cases h₃ with
      | app h₄ _ => cases h₄

end STLC
