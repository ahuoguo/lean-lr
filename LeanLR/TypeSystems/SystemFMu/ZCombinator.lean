import LeanLR.TypeSystems.SystemFMu.LogRel

/-!
# The Z combinator, semantically

`systemf_mu/z_combinator.v`. Recursion needs no recursive type: the untyped `Z` combinator is
*semantically* well typed, and the logical relation's step index is what makes the argument go
through — the proof is a Löb induction on it.

Everything is in `SystemFMu.ZCombinator`, since `Fix` and `Fix'` clash with the recursion
combinator of exercise sheet 5.
-/

open Iris.Std

namespace SystemFMu

/-- A λ-abstraction that is semantically related at a function type *is* in the value relation.
At a positive index this is `sem_expr_rel_of_val`; at index `0` the expression relation is
vacuous, and so is what a value has to satisfy. -/
theorem sem_expr_rel_lambda_val (A B : Ty) (δ : TyVarInterp) (k : Nat) (x : Binder) (e : Expr)
    (hcl : closed [] (Expr.lam x e)) (h : exprRel δ (.fn A B) k (Expr.lam x e)) :
    valRel δ (.fn A B) k (.lamV x e) := by
  cases k with
  | succ k => exact sem_expr_rel_of_val (.fn A B) δ (k + 1) (.lamV x e) (by omega) h
  | zero =>
    simp only [valRel]
    refine ⟨x, e, rfl, hcl, fun v' k' hk' _ => ?_⟩
    obtain rfl : k' = 0 := Nat.le_zero.mp hk'
    exact sem_expr_rel_zero_trivial _ _ _

namespace ZCombinator

/-! ## The combinator from the lecture

`Fix' Fix' s` unfolds to `s (λ x, Fix' Fix' s x)`, so `Fix s` is a fixpoint of `s` without any
recursive type. -/

def Fix' : Val :=
  λᵥ: z y, Expr.app (.var "y")
    (λ: x, Expr.app (Expr.app (Expr.app (.var "z") (.var "z")) (.var "y")) (.var "x"))

def Fix (s : Val) : Val :=
  λᵥ: x, Expr.app (Expr.app (Expr.app Fix'.toExpr Fix'.toExpr) s.toExpr) (.var "x")

/-- `Fix' Fix'` after one β-step. -/
private def FixStep : Val :=
  λᵥ: y, Expr.app (.var "y")
    (λ: x, Expr.app (Expr.app (Expr.app Fix'.toExpr Fix'.toExpr) (.var "y")) (.var "x"))

private theorem Fix'_closed : closed [] Fix'.toExpr := by decide

private theorem FixStep_closed : closed [] FixStep.toExpr := by decide

private theorem Fix_closed {s : Val} (hs : closed [] s.toExpr) :
    closed [] (Fix s).toExpr := by
  have h : s.toExpr.isClosed ["x"] = true := closed_weaken_nil hs
  simp [Fix, Val.toExpr, closed, Expr.isClosed, Binder.cons, h,
    closed_weaken_nil Fix'_closed]

private theorem Fix'_beta :
    subst' (Binder.bNamed "z") Fix'.toExpr
      (Expr.lam (.bNamed "y") (Expr.app (.var "y")
        (Expr.lam (.bNamed "x") (Expr.app (Expr.app (Expr.app (.var "z") (.var "z"))
          (.var "y")) (.var "x")))))
    = FixStep.toExpr := by
  simp +decide [FixStep, Fix', Val.toExpr, subst', subst]

/-- The Löb induction: `Fix' Fix'` is semantically a function from `(A → B) → A → B` to
`A → B`, at every step index. -/
private theorem fix_app_safe (A B : Ty) (δ : TyVarInterp) :
    ∀ k, exprRel δ (.fn (.fn (.fn A B) (.fn A B)) (.fn A B)) k
      (Expr.app Fix'.toExpr Fix'.toExpr) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
  match k, IH with
  | 0, _ => exact sem_expr_rel_zero_trivial _ _ _
  | (k + 1), IH =>
  refine expr_det_step_closure (det_step_beta (.bNamed "z") _ Fix'.toExpr trivial) ?_
  rw [Fix'_beta]
  refine sem_val_expr_rel _ δ _ FixStep ?_
  simp only [FixStep, valRel]
  refine ⟨.bNamed "y", _, rfl, by decide, fun vF k₁ hk₁ hvF => ?_⟩
  have hvFcl : closed [] vF.toExpr := by
    obtain ⟨x, e, rfl, hcl, -⟩ := hvF
    exact hcl
  simp +decide only [subst', subst, reduceIte, subst_closed_nil Fix'_closed]
  obtain ⟨xF, eF, rfl, hclF, hbodyF⟩ := hvF
  refine expr_det_step_closure (det_step_beta xF eF _ trivial) ?_
  refine hbodyF (.lamV (.bNamed "x") (Expr.app (Expr.app (Expr.app Fix'.toExpr Fix'.toExpr)
    (Val.lamV xF eF).toExpr) (.var "x"))) (k₁ - 1) (by omega) ?_
  have hFx : Expr.isClosed ["x"] Fix'.toExpr = true := closed_weaken_nil Fix'_closed
  have hvx : Expr.isClosed ["x"] (Val.lamV xF eF).toExpr = true := closed_weaken_nil hvFcl
  refine ⟨.bNamed "x", _, rfl, ?_, fun v' k₂ hk₂ hv' => ?_⟩
  · simp [closed, Expr.isClosed, Binder.cons, hFx, hvx]
  · simp +decide only [subst', subst, reduceIte, subst_closed_nil Fix'_closed,
      subst_closed_nil hvFcl]
    refine semantic_app A B δ k₂ _ _ ?_ (sem_val_expr_rel A δ k₂ v' hv')
    refine semantic_app (.fn (.fn A B) (.fn A B)) (.fn A B) δ k₂ _ _
      (IH k₂ (by omega)) ?_
    refine sem_val_expr_rel _ δ k₂ (Val.lamV xF eF) ?_
    simp only [valRel]
    exact ⟨xF, eF, rfl, hclF, fun v k hk hv => hbodyF v k (by omega) hv⟩

theorem Z_safe' (A B : Ty) (s : Val) (hcl : closed [] s.toExpr)
    (hF : semTyped (PartialMap.empty (M := TyMapStr) (V := Ty)) s.toExpr
      (.fn (.fn A B) (.fn A B))) :
    semTyped (PartialMap.empty (M := TyMapStr) (V := Ty)) (Fix s).toExpr (.fn A B) := by
  obtain ⟨-, hFsem⟩ := hF
  refine ⟨closed_weaken_nil (Fix_closed hcl), fun θ δ k hctx => ?_⟩
  rw [substMap_is_closed (X := []) (Fix_closed hcl) (by simp)]
  refine sem_val_expr_rel (.fn A B) δ k (Fix s) ?_
  simp only [Fix, valRel]
  refine ⟨.bNamed "x", _, rfl, ?_, fun v' k' hk' hv' => ?_⟩
  · simp [closed, Expr.isClosed, Binder.cons, closed_weaken_nil Fix'_closed,
      closed_weaken_nil hcl]
  · simp +decide only [subst', subst, reduceIte, subst_closed_nil Fix'_closed,
      subst_closed_nil hcl]
    refine semantic_app A B δ k' _ _ ?_ (sem_val_expr_rel A δ k' v' hv')
    refine semantic_app (.fn (.fn A B) (.fn A B)) (.fn A B) δ k' _ _
      (fix_app_safe A B δ k') ?_
    have hs := hFsem (PartialMap.empty (M := MapStr) (V := Expr)) δ k' .empty
    rwa [substMap_empty] at hs

/-! ## The combinator of Section 3.4

`g g` unfolds to `λ x, e[f := Z]`, so `Z` is a fixpoint of the template `e` with `f` standing for
the recursive call. -/

private theorem delete_delete_comm (m : SubstMap) (x y : String) :
    delete (M := MapStr) (delete (M := MapStr) m x) y
      = delete (M := MapStr) (delete (M := MapStr) m y) x := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun z => ?_
  by_cases hy : y = z
  · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hy]
    by_cases hx : x = z
    · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hx]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hx,
        LawfulPartialMap.get?_delete_eq (M := MapStr) hy]
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hy]
    by_cases hx : x = z
    · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hx,
        LawfulPartialMap.get?_delete_eq (M := MapStr) hx]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hx,
        LawfulPartialMap.get?_delete_ne (M := MapStr) hx,
        LawfulPartialMap.get?_delete_ne (M := MapStr) hy]

private theorem delete_delete_self (m : SubstMap) (x : String) :
    delete (M := MapStr) (delete (M := MapStr) m x) x = delete (M := MapStr) m x := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun z => ?_
  by_cases hx : x = z
  · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hx,
      LawfulPartialMap.get?_delete_eq (M := MapStr) hx]
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hx,
      LawfulPartialMap.get?_delete_ne (M := MapStr) hx]

def g (e : Expr) : Val :=
  λᵥ: f, Expr.app (Expr.lam (.bNamed "f") (Expr.lam (.bNamed "x") e))
    (λ: x, Expr.app (Expr.app (.var "f") (.var "f")) (.var "x"))

def Z (e : Expr) : Val :=
  λᵥ: x, Expr.app (Expr.app (g e).toExpr (g e).toExpr) (.var "x")

/-- Closing `Z e` with `θ` is closing the template with `θ` minus the two bound names. -/
private theorem Z_substMap (θ : SubstMap) (e : Expr) :
    substMap θ (Z e).toExpr
      = (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr := by
  simp only [Z, g, Val.toExpr, substMap, binderDelete, delete_delete_self]
  rw [delete_delete_comm (delete (M := MapStr) θ "x") "f" "x", delete_delete_self]
  simp only [LawfulPartialMap.get?_delete_ne (M := MapStr)
      (show ("f" : String) ≠ "x" by decide),
    LawfulPartialMap.get?_delete_eq (M := MapStr) (k := "f") (k' := "f") rfl,
    LawfulPartialMap.get?_delete_eq (M := MapStr) (k := "x") (k' := "x") rfl]
/-- Exercise-sheet-style statement: `e` is the template, with `f` the recursive call and `x` the
argument. Rocq's `n` (the number of type variables) is not a parameter of the port's `semTyped`. -/
theorem Z_safe (Γ : TypingContext) (A B : Ty) (e : Expr)
    (_hx : get? (M := TyMapStr) Γ "x" = none) (_hf : get? (M := TyMapStr) Γ "f" = none)
    (hcl : closed ("f" :: "x" :: Γ.domList) e)
    (he : semTyped (insert (M := TyMapStr) (insert (M := TyMapStr) Γ "x" A) "f" (.fn A B)) e B) :
    semTyped Γ (Z e).toExpr (.fn A B) := by
  obtain ⟨-, hesem⟩ := he
  have hcl4 : e.isClosed ("x" :: "f" :: "f" :: "x" :: Γ.domList) = true := by
    refine closed_weaken hcl fun y hy => ?_
    simp only [List.mem_cons] at hy ⊢
    rcases hy with rfl | rfl | hy
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  refine ⟨by simp [Z, g, Val.toExpr, closed, Expr.isClosed, Binder.cons, hcl4],
    fun θ δ k hctx => ?_⟩
  rw [Z_substMap]
  -- `θ'` is `θ` with the two bound names removed, and `e'` the template closed with it.
  have hθcl : substIsClosed [] θ := sem_context_rel_closed hctx
  have hθ'cl : substIsClosed [] (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") := by
    intro y ey hy
    refine hθcl y ey ?_
    by_cases h1 : ("f" : String) = y
    · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) h1] at hy; simp at hy
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) h1] at hy
      by_cases h2 : ("x" : String) = y
      · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) h2] at hy; simp at hy
      · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) h2] at hy
  have he'cl : closed ["f", "x"] (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e) := by
    refine substMap_closed' hcl fun y hy => ?_
    by_cases h1 : ("f" : String) = y
    · subst h1
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
      simp
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) h1]
      by_cases h2 : ("x" : String) = y
      · subst h2
        rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
        simp
      · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) h2]
        cases hget : get? (M := MapStr) θ y with
        | none =>
          simp only [List.mem_cons] at hy
          rcases hy with rfl | rfl | hy
          · exact absurd rfl h1
          · exact absurd rfl h2
          · exact absurd hget ((sem_context_rel_dom hctx y).mp
              (by rw [mem_ctx_domList] at hy; obtain ⟨A', hA'⟩ := hy; rw [hA']; simp))
        | some ey => exact closed_weaken_nil (hθcl y ey hget)
  have hgcl : closed [] (g (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr := by
    have h : (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e).isClosed
        ["x", "f", "f"] = true := closed_weaken he'cl (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl)
    simp [g, Val.toExpr, closed, Expr.isClosed, Binder.cons, h]
  have hZcl : closed [] (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr := by
    have h : (g (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr.isClosed
        ["x"] = true := closed_weaken_nil hgcl
    simp [Z, Val.toExpr, closed, Expr.isClosed, Binder.cons, h]
  -- Löb induction on the step index
  suffices H : ∀ m, SemCtxRel δ m Γ θ →
      exprRel δ (.fn A B) m
        (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr from
    H k hctx
  intro m
  induction m using Nat.strongRecOn with
  | _ m IH =>
  intro hctxm
  refine sem_val_expr_rel (.fn A B) δ m _ ?_
  simp only [Z, valRel]
  refine ⟨.bNamed "x", _, rfl, hZcl, fun v' k' hk' hv' => ?_⟩
  have hv'cl : closed [] v'.toExpr := val_rel_is_closed v' δ k' A hv'
  simp +decide only [subst', subst, reduceIte, subst_closed_nil hgcl]
  refine expr_det_step_closure (det_step_app_l (val_isVal v')
    (det_step_beta (.bNamed "f") _ _ trivial)) ?_
  simp +decide only [subst', subst, reduceIte]
  refine expr_det_step_closure (det_step_app_l (val_isVal v')
    (det_step_beta (.bNamed "f") _ _ trivial)) ?_
  simp +decide only [subst', subst, reduceIte]
  refine expr_det_step_closure (det_step_beta (.bNamed "x") _ _ (val_isVal v')) ?_
  have hZE : (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr
      = Expr.lam (.bNamed "x")
        (Expr.app (Expr.app
          (g (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr
          (g (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr)
          (.var "x")) := rfl
  rw [← hZE]
  have hθxcl : substIsClosed [] (delete (M := MapStr) θ "x") := by
    intro y ey hy
    refine hθcl y ey ?_
    by_cases h2 : ("x" : String) = y
    · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) h2] at hy; simp at hy
    · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) h2] at hy
  rw [subst_substMap "f" _ (delete (M := MapStr) θ "x") e hθxcl,
    ← LawfulPartialMap.delete_insert_of_ne (M := MapStr)
      (show ("f" : String) ≠ "x" by decide), subst']
  have hθfcl : substIsClosed []
      (Iris.Std.insert (M := MapStr) θ "f"
        (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)).toExpr) :=
    substIsClosed_insert hZcl (by
      intro y ey hy
      refine hθcl y ey ?_
      by_cases h1 : ("f" : String) = y
      · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) h1] at hy; simp at hy
      · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) h1] at hy)
  rw [subst_substMap "x" _ _ e hθfcl,
    LawfulPartialMap.insert_insert_comm (M := MapStr)
      (show ("f" : String) ≠ "x" by decide)]
  have hZval : valRel δ (.fn A B) (k' - 1 - 1 - 1)
      (Z (substMap (delete (M := MapStr) (delete (M := MapStr) θ "x") "f") e)) := by
    refine sem_expr_rel_lambda_val A B δ _ (.bNamed "x") _ hZcl ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain rfl : k' = 0 := Nat.le_zero.mp hk'
      exact sem_expr_rel_zero_trivial _ _ _
    · exact IH (k' - 1 - 1 - 1) (by omega) (sem_context_rel_mono (by omega) hctxm)
  exact hesem _ δ (k' - 1 - 1 - 1)
    (.insert _ "f" (.fn A B) hZval
      (.insert v' "x" A (val_rel_mono A δ k' _ v' (by omega) hv')
        (sem_context_rel_mono (by omega) hctxm)))

end ZCombinator

end SystemFMu
