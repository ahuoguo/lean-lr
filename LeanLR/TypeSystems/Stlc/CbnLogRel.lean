import LeanLR.TypeSystems.Stlc.LogRel

/-!
# STLC: a logical relation for call-by-name

`stlc/cbn_logrel_sol.v`. The call-by-name big-step semantics does not evaluate the argument of an
application, so the value relation at a function type quantifies over *expressions* in the
expression relation rather than over values, and semantic contexts map variables to expressions.
Closedness is therefore no longer implied by membership in the value relation and has to be
carried explicitly by the expression relation.
-/

open Iris.Std

namespace STLC.Cbn

/-! ## Call-by-name big-step semantics -/

/-- Call-by-name big-step evaluation: the argument of an application is substituted
unevaluated. -/
inductive BigStep : Expr → Val → Prop where
  | litInt {n : Int} : BigStep (Expr.litInt n) (Val.litIntV n)
  | lam {x : Binder} {e : Expr} : BigStep (Expr.lam x e) (Val.lamV x e)
  | plus {e₁ e₂ : Expr} {z₁ z₂ : Int} :
      BigStep e₁ (Val.litIntV z₁) →
      BigStep e₂ (Val.litIntV z₂) →
      BigStep (Expr.plus e₁ e₂) (Val.litIntV (z₁ + z₂))
  | app {e₁ e₂ : Expr} {x : Binder} {e : Expr} {v : Val} :
      BigStep e₁ (Val.lamV x e) →
      BigStep (subst' x e₂ e) v →
      BigStep (Expr.app e₁ e₂) v

notation:50 e " ⇓ₙ " v => BigStep e v

theorem big_step_vals (v : Val) : v.toExpr ⇓ₙ v := by
  cases v <;> constructor

theorem big_step_inv_vals {v w : Val} (h : v.toExpr ⇓ₙ w) : v = w := by
  cases v <;> cases h <;> rfl

/-! ## The logical relation -/

/-- The termination measure for the mutual definition below: a function type is larger than both
of its components *plus one*, which leaves room for the expression relation. -/
def typeSize : Ty → Nat
  | .int => 1
  | .fun A B => typeSize A + typeSize B + 2

mutual

/-- The value relation. Unlike in call-by-value, a function is related at `A ⇒ B` when it maps
*expressions* in the `A` expression relation into the `B` expression relation. -/
def valRel (τ : Ty) (v : Val) : Prop :=
  match τ, v with
  | Ty.int, Val.litIntV _ => True
  | Ty.int, _ => False
  | Ty.fun A B, Val.lamV x e =>
      Expr.closed (x :b: []) e ∧ ∀ e', exprRel A e' → exprRel B (subst' x e' e)
  | Ty.fun _ _, _ => False
termination_by typeSize τ
decreasing_by all_goals (simp only [typeSize]; omega)

/-- The expression relation. Closedness is part of the definition: an argument is substituted
without being evaluated, so a related expression must be closed in its own right. -/
def exprRel (τ : Ty) (e : Expr) : Prop :=
  ∃ w : Val, (e ⇓ₙ w) ∧ e.closed [] ∧ valRel τ w
termination_by typeSize τ + 1
decreasing_by omega

end

/-! ## Semantic typing -/

inductive semContextRel : Context → Subst → Prop where
  | empty : semContextRel Context.empty Subst.empty
  | insert (Γ : Context) (σ : Subst) (e : Expr) (x : String) (A : Ty) :
      exprRel A e →
      semContextRel Γ σ →
      semContextRel (Γ.insert x A) (σ.insert x e)

def semTyped (Γ : Context) (e : Expr) (τ : Ty) : Prop :=
  Expr.closed Γ.domList e ∧
  ∀ σ : Subst, semContextRel Γ σ → exprRel τ (substMap σ e)

/-! ## Helper lemmas -/

theorem sem_expr_rel_of_val {A : Ty} {v : Val} (h : exprRel A v.toExpr) : valRel A v := by
  unfold exprRel at h
  obtain ⟨w, hbs, _, hw⟩ := h
  rwa [big_step_inv_vals hbs]

theorem val_rel_closed {A : Ty} {v : Val} (h : valRel A v) : (v.toExpr).closed [] := by
  cases A with
  | int =>
    unfold valRel at h
    cases v with
    | litIntV _ => rfl
    | lamV _ _ => exact h.elim
  | «fun» A B =>
    unfold valRel at h
    cases v with
    | litIntV _ => exact h.elim
    | lamV x e => obtain ⟨hcl, _⟩ := h; exact hcl

theorem val_inclusion {A : Ty} {v : Val} (h : valRel A v) : exprRel A v.toExpr := by
  unfold exprRel
  exact ⟨v, big_step_vals v, val_rel_closed h, h⟩

theorem expr_rel_closed {A : Ty} {e : Expr} (h : exprRel A e) : e.closed [] := by
  unfold exprRel at h
  obtain ⟨_, _, hcl, _⟩ := h
  exact hcl

theorem semContextRel_closed {Γ : Context} {σ : Subst} (h : semContextRel Γ σ) : σ.closed [] := by
  induction h with
  | empty =>
    intro x e hlookup
    simp only [Subst.empty, Subst.lookup] at hlookup
    change (none = some _) at hlookup
    contradiction
  | insert Γ σ e x A he _ ih =>
    intro y e' hlookup
    simp only [Subst.insert, Subst.lookup] at hlookup
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hlookup
      injection hlookup with heq
      exact heq ▸ expr_rel_closed he
    · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hlookup
      exact ih y e' hlookup

/-- Inversion for `semContextRel`: every variable of the context is substituted by a semantically
well-typed expression. -/
theorem semContextRel_exprs {Γ : Context} {σ : Subst} {x : String} {A : Ty}
    (hctx : semContextRel Γ σ) (hlookup : Γ.lookup x = some A) :
    ∃ e, σ.lookup x = some e ∧ exprRel A e := by
  induction hctx with
  | empty =>
    simp only [Context.empty, Context.lookup] at hlookup
    change (none = some _) at hlookup
    contradiction
  | insert Γ' σ' e y B he _ ih =>
    simp only [Context.insert, Context.lookup] at hlookup
    by_cases hxy : y = x
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hlookup
      injection hlookup with heq
      refine ⟨e, ?_, heq ▸ he⟩
      simp only [Subst.insert, Subst.lookup]
      exact LawfulPartialMap.get?_insert_eq (M := MapStr) rfl
    · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy,
          LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at hlookup
      obtain ⟨e', hσ, he'⟩ := ih hlookup
      refine ⟨e', ?_, he'⟩
      simp only [Subst.insert, Subst.lookup]
      rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      simpa only [Subst.lookup] using hσ

theorem semContextRel_dom {Γ : Context} {σ : Subst} (h : semContextRel Γ σ) : Γ.dom = σ.dom := by
  induction h with
  | empty => rfl
  | insert Γ' σ' e x A _ _ ih =>
    simp only [Context.dom, Subst.dom, Context.insert, Subst.insert]
    apply LawfulSet.ext
    intro k
    simp only [LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]
    by_cases hxk : x = k
    · subst hxk
      simp [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
    · constructor <;> intro hk
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
            LawfulPartialMap.get?_delete_ne (M := MapStr) hxk] at hk
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk]
        have hmem : k ∈ Context.dom Γ' := by
          rw [Context.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]; exact hk
        rw [ih, Subst.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)] at hmem
        exact hmem
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk] at hk
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
            LawfulPartialMap.get?_delete_ne (M := MapStr) hxk]
        have hmem : k ∈ Subst.dom σ' := by
          rw [Subst.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]; exact hk
        rw [← ih, Context.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)] at hmem
        exact hmem

/-! ## Compatibility lemmas -/

theorem compat_int {Γ : Context} {z : Int} : semTyped Γ (Expr.litInt z) Ty.int := by
  refine ⟨rfl, fun σ _ => ?_⟩
  unfold exprRel
  exact ⟨Val.litIntV z, BigStep.litInt, rfl, by unfold valRel; trivial⟩

theorem compat_var {Γ : Context} {x : String} {A : Ty} (hx : Γ.lookup x = some A) :
    semTyped Γ (Expr.var x) A := by
  refine ⟨by simp [Expr.closed]; exact lookup_mem_domList hx, fun σ hctx => ?_⟩
  obtain ⟨e, hσ, he⟩ := semContextRel_exprs hctx hx
  show exprRel A (substMap σ (Expr.var x))
  unfold substMap
  simp only [hσ]
  exact he

theorem compat_app {Γ : Context} {e₁ e₂ : Expr} {A B : Ty}
    (h₁ : semTyped Γ e₁ (A ⇒ B)) (h₂ : semTyped Γ e₂ A) :
    semTyped Γ (Expr.app e₁ e₂) B := by
  obtain ⟨hfuncl, hfun⟩ := h₁
  obtain ⟨hargcl, harg⟩ := h₂
  refine ⟨by simp [Expr.closed, hfuncl, hargcl], fun σ hctx => ?_⟩
  have hf := hfun σ hctx
  rw [exprRel] at hf
  obtain ⟨v₁, hbs₁, hcl₁, hv₁⟩ := hf
  unfold valRel at hv₁
  cases v₁ with
  | litIntV n => exact hv₁.elim
  | lamV x e =>
    obtain ⟨_, hbody⟩ := hv₁
    have ha := harg σ hctx
    have hacl := expr_rel_closed ha
    have hres := hbody _ ha
    unfold exprRel at hres ⊢
    obtain ⟨v, hbs, _, hv⟩ := hres
    refine ⟨v, BigStep.app hbs₁ hbs, ?_, hv⟩
    show Expr.closed [] (Expr.app (substMap σ e₁) (substMap σ e₂)) = true
    simp only [Expr.closed, Bool.and_eq_true]
    exact ⟨hcl₁, hacl⟩

theorem lam_closed (Γ : Context) (σ : Subst) (x : String) (A : Ty) (e : Expr)
    (hcl : e.closed ((Γ.insert x A).domList)) (hctx : semContextRel Γ σ) :
    (Expr.lam (Binder.named x) (substMap (Subst.delete x σ) e)).closed [] := by
  simp only [Expr.closed, Binder.cons]
  refine substMapClosed (σ := Subst.delete x σ) (X := [x]) ?_
    (Subst.closed_delete_weaken (semContextRel_closed hctx))
  refine closed_weaken hcl fun y hy => ?_
  rw [mem_domList_insert] at hy
  cases hy with
  | inl heq => subst heq; exact List.mem_append.mpr (Or.inl (List.Mem.head _))
  | inr h =>
    obtain ⟨hmem, hne⟩ := h
    by_cases hyx : y = x
    · subst hyx; exact List.mem_append.mpr (Or.inl (List.Mem.head _))
    · refine List.mem_append.mpr (Or.inr ?_)
      rw [mem_domList_iff_lookup_ctx] at hmem
      obtain ⟨B, hB⟩ := hmem
      obtain ⟨e', hσ, _⟩ := semContextRel_exprs hctx hB
      rw [mem_domList_iff_lookup]
      exact ⟨e', by rw [lookup_delete_ne hyx]; exact hσ⟩

theorem compat_lam {Γ : Context} {x : String} {e : Expr} {A B : Ty}
    (h : semTyped (Γ.insert x A) e B) :
    semTyped Γ (Expr.lam (Binder.named x) e) (A ⇒ B) := by
  obtain ⟨hbodycl, hbody⟩ := h
  refine ⟨?_, fun σ hctx => ?_⟩
  · simp only [Expr.closed, Binder.cons]
    refine closed_weaken hbodycl fun y hy => ?_
    rw [mem_domList_insert] at hy
    cases hy with
    | inl heq => subst heq; exact List.Mem.head _
    | inr h => exact List.Mem.tail _ h.1
  · show exprRel (A ⇒ B) (substMap σ (Expr.lam (Binder.named x) e))
    rw [substMap]
    unfold exprRel
    refine ⟨Val.lamV (Binder.named x) (substMap (Subst.delete x σ) e), BigStep.lam,
      lam_closed Γ σ x A e hbodycl hctx, ?_⟩
    unfold valRel
    refine ⟨lam_closed Γ σ x A e hbodycl hctx, fun e' he' => ?_⟩
    show exprRel B (subst' (Binder.named x) e' (substMap (Subst.delete x σ) e))
    rw [subst', subst_substMap_compose (semContextRel_closed hctx)]
    exact hbody _ (semContextRel.insert Γ σ e' x A he' hctx)

theorem compat_add {Γ : Context} {e₁ e₂ : Expr}
    (h₁ : semTyped Γ e₁ Ty.int) (h₂ : semTyped Γ e₂ Ty.int) :
    semTyped Γ (Expr.plus e₁ e₂) Ty.int := by
  obtain ⟨hcl₁, hsem₁⟩ := h₁
  obtain ⟨hcl₂, hsem₂⟩ := h₂
  refine ⟨by simp [Expr.closed, hcl₁, hcl₂], fun σ hctx => ?_⟩
  have h1 := hsem₁ σ hctx
  have h2 := hsem₂ σ hctx
  unfold exprRel at h1 h2
  obtain ⟨v₁, hbs₁, hclv₁, hv₁⟩ := h1
  obtain ⟨v₂, hbs₂, hclv₂, hv₂⟩ := h2
  unfold valRel at hv₁ hv₂
  cases v₁ with
  | lamV _ _ => exact hv₁.elim
  | litIntV z₁ =>
    cases v₂ with
    | lamV _ _ => exact hv₂.elim
    | litIntV z₂ =>
      unfold exprRel
      refine ⟨Val.litIntV (z₁ + z₂), BigStep.plus hbs₁ hbs₂, ?_, by unfold valRel; trivial⟩
      show Expr.closed [] (Expr.plus (substMap σ e₁) (substMap σ e₂)) = true
      simp only [Expr.closed, Bool.and_eq_true]
      exact ⟨hclv₁, hclv₂⟩

/-! ## Soundness and termination -/

theorem sem_soundness {Γ : Context} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) : semTyped Γ e A := by
  induction h with
  | var hx => exact compat_var hx
  | lam_named _ ih => exact compat_lam ih
  | litInt => exact compat_int
  | app _ _ ih₁ ih₂ => exact compat_app ih₁ ih₂
  | plus _ _ ih₁ ih₂ => exact compat_add ih₁ ih₂

theorem termination {e : Expr} {A : Ty} (h : Context.empty ⊢ e : A) : ∃ v, e ⇓ₙ v := by
  obtain ⟨_, hsem⟩ := sem_soundness h
  have hs := hsem Subst.empty semContextRel.empty
  rw [substMap_empty] at hs
  unfold exprRel at hs
  obtain ⟨v, hbs, _⟩ := hs
  exact ⟨v, hbs⟩

end STLC.Cbn
