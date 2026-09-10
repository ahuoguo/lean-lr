import LeanLR.TypeSystems.StlcExtended.Lang

/-!
# Extended STLC: big-step semantics

The judgment `e ⇓ v` relates an expression directly to the value it evaluates to. Compare
`StlcExtended.CtxStep`, which gives the same language a contextual small-step semantics.
-/

namespace StlcExtended

/-- The big-step evaluation judgment. -/
inductive BigStep : Expr → Val → Prop where
  | bs_lit (n : Int) :
      BigStep (.litInt n) (.litIntV n)
  | bs_lam (x : Binder) (e : Expr) :
      BigStep (.lam x e) (.lamV x e)
  | bs_add {e₁ e₂ : Expr} {z₁ z₂ : Int} :
      BigStep e₁ (.litIntV z₁) →
      BigStep e₂ (.litIntV z₂) →
      BigStep (.plus e₁ e₂) (.litIntV (z₁ + z₂))
  | bs_app {e₁ e₂ : Expr} {x : Binder} {e : Expr} {v₂ v : Val} :
      BigStep e₁ (.lamV x e) →
      BigStep e₂ v₂ →
      BigStep (subst' x v₂.toExpr e) v →
      BigStep (.app e₁ e₂) v
  | bs_pair {e₁ e₂ : Expr} {v₁ v₂ : Val} :
      BigStep e₁ v₁ →
      BigStep e₂ v₂ →
      BigStep (.pair e₁ e₂) (.pairV v₁ v₂)
  | bs_fst {e : Expr} {v₁ v₂ : Val} :
      BigStep e (.pairV v₁ v₂) →
      BigStep (.fst e) v₁
  | bs_snd {e : Expr} {v₁ v₂ : Val} :
      BigStep e (.pairV v₁ v₂) →
      BigStep (.snd e) v₂
  | bs_injl {e : Expr} {v : Val} :
      BigStep e v →
      BigStep (.injL e) (.injLV v)
  | bs_injr {e : Expr} {v : Val} :
      BigStep e v →
      BigStep (.injR e) (.injRV v)
  | bs_casel {e e₁ e₂ : Expr} {v v' : Val} :
      BigStep e (.injLV v) →
      BigStep (.app e₁ v.toExpr) v' →
      BigStep (.case e e₁ e₂) v'
  | bs_caser {e e₁ e₂ : Expr} {v v' : Val} :
      BigStep e (.injRV v) →
      BigStep (.app e₂ v.toExpr) v' →
      BigStep (.case e e₁ e₂) v'

@[inherit_doc BigStep] notation:50 e " ⇓ " v => BigStep e v

/-- Termination: some value is reached. -/
def terminates (e : Expr) : Prop := ∃ v, e ⇓ v

/-- Every value evaluates to itself. -/
theorem big_step_of_val : ∀ v : Val, v.toExpr ⇓ v
  | .litIntV n => .bs_lit n
  | .lamV x e => .bs_lam x e
  | .pairV v₁ v₂ => .bs_pair (big_step_of_val v₁) (big_step_of_val v₂)
  | .injLV v => .bs_injl (big_step_of_val v)
  | .injRV v => .bs_injr (big_step_of_val v)

/-- A value evaluates only to itself. -/
theorem big_step_val {v v' : Val} (h : v.toExpr ⇓ v') : v' = v := by
  induction v generalizing v' with
  | litIntV n => cases h; rfl
  | lamV x e => cases h; rfl
  | pairV v₁ v₂ ih₁ ih₂ =>
    cases h with
    | bs_pair h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]
  | injLV v ih => cases h with | bs_injl h' => rw [ih h']
  | injRV v ih => cases h with | bs_injr h' => rw [ih h']

/-- The big-step semantics is deterministic. -/
theorem big_step_det {e : Expr} {v₁ v₂ : Val} (h₁ : e ⇓ v₁) (h₂ : e ⇓ v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | bs_lit _ => cases h₂; rfl
  | bs_lam _ _ => cases h₂; rfl
  | bs_add _ _ ih₁ ih₂ =>
    cases h₂ with
    | bs_add h₁' h₂' =>
      injection ih₁ h₁' with e₁; injection ih₂ h₂' with e₂; rw [e₁, e₂]
  | bs_app _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | bs_app h₁' h₂' h₃' =>
      injection ih₁ h₁' with ex ee
      subst ex; subst ee
      rw [ih₂ h₂'] at ih₃
      exact ih₃ h₃'
  | bs_pair _ _ ih₁ ih₂ =>
    cases h₂ with
    | bs_pair h₁' h₂' => rw [ih₁ h₁', ih₂ h₂']
  | bs_fst _ ih =>
    cases h₂ with
    | bs_fst h' => injection ih h'
  | bs_snd _ ih =>
    cases h₂ with
    | bs_snd h' => injection ih h'
  | bs_injl _ ih => cases h₂ with | bs_injl h' => rw [ih h']
  | bs_injr _ ih => cases h₂ with | bs_injr h' => rw [ih h']
  | bs_casel _ _ ih₁ ih₂ =>
    cases h₂ with
    | bs_casel h₁' h₂' => injection ih₁ h₁' with ev; subst ev; exact ih₂ h₂'
    | bs_caser h₁' _ => exact absurd (ih₁ h₁') (by simp)
  | bs_caser _ _ ih₁ ih₂ =>
    cases h₂ with
    | bs_casel h₁' _ => exact absurd (ih₁ h₁') (by simp)
    | bs_caser h₁' h₂' => injection ih₁ h₁' with ev; subst ev; exact ih₂ h₂'

end StlcExtended
