import LeanLR.TypeSystems.Stlc.Operational

/-!
# STLC: inversion for the small-step relation

`stlc/lecture2.v`. The Rocq file restates the language of `lang.v` verbatim so that the lecture is
self-contained; only its second half is ported here — the eliminator and the two inversion
operators for `Step`, and the proof that values do not step that one gets from them.
-/

namespace STLC

/-- The non-recursive eliminator for `Step`. -/
theorem Step.elim (P : Expr → Expr → Prop)
    (hbeta : ∀ (x : Binder) (e₁ e₂ : Expr), e₂.isValue = true →
      P (.app (.lam x e₁) e₂) (subst' x e₂ e₁))
    (happl : ∀ e₁ e₁' e₂ : Expr, e₂.isValue = true → e₁ ↠ e₁' → P (.app e₁ e₂) (.app e₁' e₂))
    (happr : ∀ e₁ e₂ e₂' : Expr, e₂ ↠ e₂' → P (.app e₁ e₂) (.app e₁ e₂'))
    (hplus : ∀ n₁ n₂ n₃ : Int, n₁ + n₂ = n₃ →
      P (.plus (.litInt n₁) (.litInt n₂)) (.litInt n₃))
    (hplusl : ∀ e₁ e₁' e₂ : Expr, e₂.isValue = true → e₁ ↠ e₁' → P (.plus e₁ e₂) (.plus e₁' e₂))
    (hplusr : ∀ e₁ e₂ e₂' : Expr, e₂ ↠ e₂' → P (.plus e₁ e₂) (.plus e₁ e₂')) :
    ∀ e e' : Expr, e ↠ e' → P e e' := by
  intro e e' h
  cases h with
  | stepBeta hv => exact hbeta _ _ _ hv
  | stepAppL hv h => exact happl _ _ _ hv h
  | stepAppR h => exact happr _ _ _ h
  | stepPlusRed h => exact hplus _ _ _ h
  | stepPlusL hv h => exact hplusl _ _ _ hv h
  | stepPlusR h => exact hplusr _ _ _ h

/-- The inversion operator: like `Step.elim`, but each case also records the equations that
identify `e` and `e'`, so that a case can be discharged by contradiction. -/
theorem Step.inversion (P : Expr → Expr → Prop) (e e' : Expr)
    (hbeta : ∀ (x : Binder) (e₁ e₂ : Expr), e = .app (.lam x e₁) e₂ → e' = subst' x e₂ e₁ →
      e₂.isValue = true → P (.app (.lam x e₁) e₂) (subst' x e₂ e₁))
    (happl : ∀ e₁ e₁' e₂ : Expr, e = .app e₁ e₂ → e' = .app e₁' e₂ →
      e₂.isValue = true → e₁ ↠ e₁' → P (.app e₁ e₂) (.app e₁' e₂))
    (happr : ∀ e₁ e₂ e₂' : Expr, e = .app e₁ e₂ → e' = .app e₁ e₂' →
      e₂ ↠ e₂' → P (.app e₁ e₂) (.app e₁ e₂'))
    (hplus : ∀ n₁ n₂ n₃ : Int, e = .plus (.litInt n₁) (.litInt n₂) → e' = .litInt n₃ →
      n₁ + n₂ = n₃ → P (.plus (.litInt n₁) (.litInt n₂)) (.litInt n₃))
    (hplusl : ∀ e₁ e₁' e₂ : Expr, e = .plus e₁ e₂ → e' = .plus e₁' e₂ →
      e₂.isValue = true → e₁ ↠ e₁' → P (.plus e₁ e₂) (.plus e₁' e₂))
    (hplusr : ∀ e₁ e₂ e₂' : Expr, e = .plus e₁ e₂ → e' = .plus e₁ e₂' →
      e₂ ↠ e₂' → P (.plus e₁ e₂) (.plus e₁ e₂'))
    (h : e ↠ e') : P e e' := by
  cases h with
  | stepBeta hv => exact hbeta _ _ _ rfl rfl hv
  | stepAppL hv h => exact happl _ _ _ rfl rfl hv h
  | stepAppR h => exact happr _ _ _ rfl rfl h
  | stepPlusRed h => exact hplus _ _ _ rfl rfl h
  | stepPlusL hv h => exact hplusl _ _ _ rfl rfl hv h
  | stepPlusR h => exact hplusr _ _ _ rfl rfl h

/-- Values do not step, proved through `Step.inversion` rather than by `cases`. -/
theorem val_no_step_inversion {v : Val} {e : Expr} (h : v.toExpr ↠ e) : False := by
  refine Step.inversion (fun _ _ => False) _ _ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
    intro _ _ _ heq <;> cases v <;> exact Expr.noConfusion heq

/-- What a step out of `e` can look like, read off the shape of `e`. -/
def stepInv : Expr → Expr → Prop
  | .app e₁ e₂, e' =>
      (∃ x f, e₁ = .lam x f ∧ e' = subst' x e₂ f) ∨
      (∃ e₁', e₂.isValue = true ∧ e₁ ↠ e₁') ∨
      (∃ e₂', e₂ ↠ e₂')
  | .plus e₁ e₂, e' =>
      (∃ n₁ n₂, e₁ = .litInt n₁ ∧ e₂ = .litInt n₂ ∧ Expr.litInt (n₁ + n₂) = e') ∨
      (∃ e₁', e₂.isValue = true ∧ e₁ ↠ e₁') ∨
      (∃ e₂', e₂ ↠ e₂')
  | _, _ => False

theorem Step.inv {e e' : Expr} (h : e ↠ e') : stepInv e e' := by
  cases h with
  | stepBeta hv => exact Or.inl ⟨_, _, rfl, rfl⟩
  | stepAppL hv h => exact Or.inr (Or.inl ⟨_, hv, h⟩)
  | stepAppR h => exact Or.inr (Or.inr ⟨_, h⟩)
  | stepPlusRed h => exact Or.inl ⟨_, _, rfl, rfl, by rw [h]⟩
  | stepPlusL hv h => exact Or.inr (Or.inl ⟨_, hv, h⟩)
  | stepPlusR h => exact Or.inr (Or.inr ⟨_, h⟩)

end STLC
