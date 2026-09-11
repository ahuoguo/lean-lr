import LeanLR.TypeSystems.SystemFMu.Tactics
import LeanLR.TypeSystems.SystemFMu.Pure
import LeanLR.TypeSystems.SystemFMu.LogRel

/-!
# System F + μ, exercise sheet 5

`systemf_mu/exercises05_sol.v`. A recursion combinator built from a recursive type, an encoding
of arithmetic expressions, and a semantically well-typed implementation of lists behind an
existential.
-/

open Iris.Std

namespace SystemFMu

-- The recursive `det_step1`/`solve_typing` macros nest deeply.
set_option maxRecDepth 8000

/-- `Γ` is contained in `Γ` extended at a name it does not bind. -/
theorem subseteq_insert {Γ : TypingContext} {y : String} {C : Ty}
    (hy : get? (M := TyMapStr) Γ y = none) : Γ ⊑ insert (M := TyMapStr) Γ y C := by
  intro z D hz
  by_cases hyz : y = z
  · subst hyz; rw [hy] at hz; exact absurd hz (by simp)
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hyz]; exact hz

/-! ## Exercise 5: a recursion combinator -/

section RecursionCombinator

variable (f x : String) (Hfx : f ≠ x)

/-- The body of `rec_body`, split out so that `rec_body` can be kept folded in proofs. -/
def rec_inner (t : Expr) : Expr :=
  .lam (.bNamed f) (.lam (.bNamed x)
    (.app (.app t (.lam (.bNamed x)
      (.app (.app (.unroll (.var f)) (.var f)) (.var x)))) (.var x)))

def rec_body (t : Expr) : Expr := .roll (rec_inner f x t)

def Rec (t : Expr) : Val :=
  .lamV (.bNamed x) (.app (.app (.unroll (rec_body f x t)) (rec_body f x t)) (.var x))

theorem is_val_rec_inner (t : Expr) : Expr.isVal (rec_inner f x t) := trivial

theorem is_val_rec_body (t : Expr) : Expr.isVal (rec_body f x t) := trivial

theorem is_val_Rec (t : Expr) : Expr.isVal (Rec f x t).toExpr := trivial

theorem closed_rec_body {t : Expr} (h : closed [] t) : closed [] (rec_body f x t) := by
  have ht : t.isClosed [x, f] = true := closed_weaken_nil h
  simp [rec_body, rec_inner, closed, Expr.isClosed, Binder.cons, ht]

theorem closed_Rec {t : Expr} (h : closed [] t) : closed [] (Rec f x t).toExpr := by
  have hR : (rec_body f x t).isClosed [x] = true := closed_weaken_nil (closed_rec_body f x h)
  simp [Rec, Val.toExpr, closed, Expr.isClosed, Binder.cons, hR]

include Hfx in
theorem rec_body_subst_x (e t : Expr) : subst x e (rec_body f x t) = rec_body f x t := by
  simp [rec_body, rec_inner, subst, Ne.symm Hfx]

theorem rec_body_subst_f (e t : Expr) : subst f e (rec_body f x t) = rec_body f x t := by
  simp [rec_body, rec_inner, subst]

include Hfx in
theorem Rec_red (t e : Expr) (hve : Expr.isVal e) (_hvt : Expr.isVal t)
    (_hce : closed [] e) (hct : closed [] t) :
    ContextualSteps (.app (Rec f x t).toExpr e) (.app (.app t (Rec f x t).toExpr) e) := by
  have hRcl : closed [] (rec_body f x t) := closed_rec_body f x hct
  have hReccl : closed [] (Rec f x t).toExpr := closed_Rec f x hct
  -- β: unfold the outer `Rec`
  refine .step (app_step_beta x _ _ hve) ?_
  rw [show subst x e (.app (.app (.unroll (rec_body f x t)) (rec_body f x t)) (.var x))
      = .app (.app (.unroll (rec_body f x t)) (rec_body f x t)) e from by
    simp [subst, rec_body_subst_x f x Hfx]]
  -- unroll the recursive type
  refine .step (app_step_l (app_step_l (unroll_roll_step (is_val_rec_inner f x t))
    (is_val_rec_body f x t)) hve) ?_
  -- β: pass the body to itself
  refine .step (app_step_l (app_step_beta f _ _ (is_val_rec_body f x t)) hve) ?_
  rw [show subst f (rec_body f x t) (.lam (.bNamed x)
        (.app (.app t (.lam (.bNamed x)
          (.app (.app (.unroll (.var f)) (.var f)) (.var x)))) (.var x)))
      = .lam (.bNamed x) (.app (.app t (Rec f x t).toExpr) (.var x)) from by
    simp [subst, Rec, Val.toExpr, Hfx, subst_closed_nil hct]]
  -- β: pass the argument
  refine .step (app_step_beta x _ _ hve) ?_
  rw [show subst x e (.app (.app t (Rec f x t).toExpr) (.var x))
      = .app (.app t (Rec f x t).toExpr) e from by
    simp [subst, subst_closed_nil hct, subst_closed_nil hReccl]]
  exact .refl

include Hfx in
theorem rec_body_typing (n : Nat) (Γ : TypingContext) (A B : Ty) (t : Expr)
    (hx : get? (M := TyMapStr) Γ x = none) (hf : get? (M := TyMapStr) Γ f = none)
    (hA : TypeWf n A) (hB : TypeWf n B)
    (ht : SynTyped n Γ t (.fn (.fn A B) (.fn A B))) :
    SynTyped n Γ (rec_body f x t)
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) := by
  have hAup : TypeWf (n + 1) (A.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA
  have hBup : TypeWf (n + 1) (B.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) B (fun m hm => Nat.succ_lt_succ hm) hB
  have heq : (Ty.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1)))).subst1
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1)))))
      = .fn (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) (.fn A B) := by
    simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id]
  have hMUwf : TypeWf n (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) :=
    .mu_wf (.fn_wf (.tVar_wf (by omega)) (.fn_wf hAup hBup))
  have hx' : get? (M := TyMapStr) (insert (M := TyMapStr) Γ f
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1)))))) x = none := by
    rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) Hfx]; exact hx
  refine .typed_roll n Γ _ _ ?_
  rw [heq]
  refine .typed_lam n Γ f _ _ (.fn A B) hMUwf ?_
  refine .typed_lam n _ x _ A B hA ?_
  refine .typed_app n _ _ _ A B ?_ (.typed_var _ _ x _ lookup_here)
  refine .typed_app n _ _ _ (.fn A B) (.fn A B) ?_ ?_
  · exact typed_weakening ht
      (CtxSubseteq.trans (subseteq_insert hf) (subseteq_insert hx')) (Nat.le_refl n)
  · refine .typed_lam n _ x _ A B hA ?_
    refine .typed_app n _ _ _ A B ?_ (.typed_var _ _ x _ lookup_here)
    refine .typed_app n _ _ _
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) (.fn A B) ?_
      (.typed_var _ _ f _
        (lookup_there (Ne.symm Hfx) (lookup_there (Ne.symm Hfx) lookup_here)))
    exact typed_unroll'
      (.typed_var _ _ f _ (lookup_there (Ne.symm Hfx) (lookup_there (Ne.symm Hfx) lookup_here)))
      heq.symm

include Hfx in
theorem Rec_typing (n : Nat) (Γ : TypingContext) (A B : Ty) (t : Expr)
    (hA : TypeWf n A) (hB : TypeWf n B)
    (hx : get? (M := TyMapStr) Γ x = none) (hf : get? (M := TyMapStr) Γ f = none)
    (ht : SynTyped n Γ t (.fn (.fn A B) (.fn A B))) :
    SynTyped n Γ (Rec f x t).toExpr (.fn A B) := by
  have heq : (Ty.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1)))).subst1
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1)))))
      = .fn (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) (.fn A B) := by
    simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id]
  have hrec : SynTyped n (insert (M := TyMapStr) Γ x A) (rec_body f x t)
      (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) :=
    typed_weakening (rec_body_typing f x Hfx n Γ A B t hx hf hA hB ht)
      (subseteq_insert hx) (Nat.le_refl n)
  refine .typed_lam n Γ x _ A B hA ?_
  refine .typed_app n _ _ _ A B ?_ (.typed_var _ _ x _ lookup_here)
  exact .typed_app n _ _ _
    (.mu (.fn (.tVar 0) (.fn (A.rename (· + 1)) (B.rename (· + 1))))) (.fn A B)
    (typed_unroll' hrec heq.symm) hrec

end RecursionCombinator

/-! ### The fixpoint combinator

Rocq seals `Fix` so that `solve_typing` cannot unfold it; Lean's `solve_typing` never unfolds a
definition, so the seal — `Fix_aux`, `Fix'`, `Fix_eq` — has no counterpart here. -/

def Fix (f x : String) (e : Expr) : Val := Rec f x (.lam (.bNamed f) (.lam (.bNamed x) e))

theorem fix_red (f x : String) (e e' : Expr) (He : closed [x, f] e) (Hcl : closed [] e')
    (Hval : Expr.isVal e') (Hfx : f ≠ x) :
    ContextualSteps (.app (Fix f x e).toExpr e')
      (subst x e' (subst f (Fix f x e).toExpr e)) := by
  have ht : closed [] (Expr.lam (.bNamed f) (.lam (.bNamed x) e)) := He
  refine ContextualSteps.trans (Rec_red f x Hfx _ e' Hval trivial Hcl ht) ?_
  refine .step (app_step_l (app_step_beta f _ _ (is_val_Rec f x _)) Hval) ?_
  rw [show subst f (Rec f x (Expr.lam (.bNamed f) (.lam (.bNamed x) e))).toExpr
        (Expr.lam (.bNamed x) e)
      = .lam (.bNamed x) (subst f (Fix f x e).toExpr e) from by simp [Fix, subst, Hfx]]
  refine .step (app_step_beta x _ _ Hval) ?_
  exact .refl

theorem delete_delete_subseteq (Γ : TypingContext) (f x : String) :
    delete (M := TyMapStr) (delete (M := TyMapStr) Γ f) x ⊑ Γ := by
  intro z D hz
  by_cases hxz : x = z
  · subst hxz
    rw [LawfulPartialMap.get?_delete_eq (M := TyMapStr) rfl] at hz
    exact absurd hz (by simp)
  · rw [LawfulPartialMap.get?_delete_ne (M := TyMapStr) hxz] at hz
    by_cases hfz : f = z
    · subst hfz
      rw [LawfulPartialMap.get?_delete_eq (M := TyMapStr) rfl] at hz
      exact absurd hz (by simp)
    · rwa [LawfulPartialMap.get?_delete_ne (M := TyMapStr) hfz] at hz

theorem insert_insert_delete_delete {Γ : TypingContext} {f x : String} {T A : Ty}
    (_h : f ≠ x) :
    insert (M := TyMapStr) (insert (M := TyMapStr)
      (delete (M := TyMapStr) (delete (M := TyMapStr) Γ f) x) f T) x A
    = insert (M := TyMapStr) (insert (M := TyMapStr) Γ f T) x A := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
  by_cases hxk : x = k
  · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxk,
      LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxk]
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk,
      LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxk]
    by_cases hfk : f = k
    · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hfk,
        LawfulPartialMap.get?_insert_eq (M := TyMapStr) hfk]
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hfk,
        LawfulPartialMap.get?_insert_ne (M := TyMapStr) hfk,
        LawfulPartialMap.get?_delete_ne (M := TyMapStr) hxk,
        LawfulPartialMap.get?_delete_ne (M := TyMapStr) hfk]

theorem fix_typing (n : Nat) (Γ : TypingContext) (f x : String) (A B : Ty) (e : Expr)
    (hA : TypeWf n A) (hB : TypeWf n B) (Hfx : f ≠ x)
    (he : SynTyped n (insert (M := TyMapStr) (insert (M := TyMapStr) Γ f (.fn A B)) x A) e B) :
    SynTyped n Γ (Fix f x e).toExpr (.fn A B) := by
  refine typed_weakening (Γ := delete (M := TyMapStr) (delete (M := TyMapStr) Γ f) x) ?_
    (delete_delete_subseteq Γ f x) (Nat.le_refl n)
  refine Rec_typing f x Hfx n _ A B _ hA hB
    (LawfulPartialMap.get?_delete_eq (M := TyMapStr) rfl) ?_ ?_
  · rw [LawfulPartialMap.get?_delete_ne (M := TyMapStr) (Ne.symm Hfx)]
    exact LawfulPartialMap.get?_delete_eq (M := TyMapStr) rfl
  · refine .typed_lam n _ f _ (.fn A B) (.fn A B) (.fn_wf hA hB) ?_
    refine .typed_lam n _ x _ A B hA ?_
    rw [insert_insert_delete_delete Hfx]
    exact he

/-! ## Exercise 1: arithmetic expressions -/

/-- `μ α. (Int + α × α) + α × α`: literals, sums and products. -/
def aexpr : Ty :=
  .mu (.sum (.sum .int (.prod (.tVar 0) (.tVar 0))) (.prod (.tVar 0) (.tVar 0)))

def num_val (v : Val) : Val := .rollV (.injLV (.injLV v))
def num_expr (e : Expr) : Expr := .roll (.injL (.injL e))

def plus_val (v₁ v₂ : Val) : Val := .rollV (.injLV (.injRV (.pairV v₁ v₂)))
def plus_expr (e₁ e₂ : Expr) : Expr := .roll (.injL (.injR (.pair e₁ e₂)))

def mul_val (v₁ v₂ : Val) : Val := .rollV (.injRV (.pairV v₁ v₂))
def mul_expr (e₁ e₂ : Expr) : Expr := .roll (.injR (.pair e₁ e₂))

theorem aexpr_wf (n : Nat) : TypeWf n aexpr :=
  .mu_wf (.sum_wf (.sum_wf .int_wf (.prod_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))))
    (.prod_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))))

theorem num_expr_typed (n : Nat) (Γ : TypingContext) (e : Expr) (h : SynTyped n Γ e .int) :
    SynTyped n Γ (num_expr e) aexpr := by
  refine .typed_roll n Γ _ _ ?_
  exact .typed_injL n Γ _ (.sum .int (.prod aexpr aexpr)) (.prod aexpr aexpr)
    (.prod_wf (aexpr_wf n) (aexpr_wf n))
    (.typed_injL n Γ _ .int (.prod aexpr aexpr) (.prod_wf (aexpr_wf n) (aexpr_wf n)) h)

theorem plus_expr_typed (n : Nat) (Γ : TypingContext) (e₁ e₂ : Expr)
    (h₁ : SynTyped n Γ e₁ aexpr) (h₂ : SynTyped n Γ e₂ aexpr) :
    SynTyped n Γ (plus_expr e₁ e₂) aexpr := by
  refine .typed_roll n Γ _ _ ?_
  exact .typed_injL n Γ _ (.sum .int (.prod aexpr aexpr)) (.prod aexpr aexpr)
    (.prod_wf (aexpr_wf n) (aexpr_wf n))
    (.typed_injR n Γ _ .int (.prod aexpr aexpr) .int_wf (.typed_pair n Γ _ _ _ _ h₁ h₂))

theorem mul_expr_typed (n : Nat) (Γ : TypingContext) (e₁ e₂ : Expr)
    (h₁ : SynTyped n Γ e₁ aexpr) (h₂ : SynTyped n Γ e₂ aexpr) :
    SynTyped n Γ (mul_expr e₁ e₂) aexpr := by
  refine .typed_roll n Γ _ _ ?_
  exact .typed_injR n Γ _ (.sum .int (.prod aexpr aexpr)) (.prod aexpr aexpr)
    (.sum_wf .int_wf (.prod_wf (aexpr_wf n) (aexpr_wf n)))
    (.typed_pair n Γ _ _ _ _ h₁ h₂)

def eval_aexpr : Val :=
  Fix "rec" "e"
    (matchE (Expr.unroll (.var "e")) (.bNamed "e'")
      (matchE (.var "e'") (.bNamed "n") (.var "n") (.bNamed "es")
        (Expr.binOp .plusOp (Expr.app (.var "rec") (Expr.fst (.var "es")))
          (Expr.app (.var "rec") (Expr.snd (.var "es")))))
      (.bNamed "es")
      (Expr.binOp .multOp (Expr.app (.var "rec") (Expr.fst (.var "es")))
        (Expr.app (.var "rec") (Expr.snd (.var "es")))))

theorem eval_aexpr_typed (Γ : TypingContext) (n : Nat) :
    SynTyped n Γ eval_aexpr.toExpr (.fn aexpr .int) := by
  refine fix_typing n Γ "rec" "e" aexpr .int _ (aexpr_wf n) .int_wf (by decide) ?_
  refine .typed_case n _ _ _ _ (.sum .int (.prod aexpr aexpr)) (.prod aexpr aexpr) .int ?_ ?_ ?_
  · exact typed_unroll' (.typed_var _ _ "e" _ lookup_here) rfl
  · refine .typed_lam n _ "e'" _ (.sum .int (.prod aexpr aexpr)) .int
      (.sum_wf .int_wf (.prod_wf (aexpr_wf n) (aexpr_wf n))) ?_
    refine .typed_case n _ _ _ _ .int (.prod aexpr aexpr) .int
      (.typed_var _ _ "e'" _ lookup_here) ?_ ?_
    · exact .typed_lam n _ "n" _ .int .int .int_wf (.typed_var _ _ "n" _ lookup_here)
    · refine .typed_lam n _ "es" _ (.prod aexpr aexpr) .int
        (.prod_wf (aexpr_wf n) (aexpr_wf n)) ?_
      refine .typed_binOp n _ .plusOp _ _ .int .int .int .plus_typed ?_ ?_ <;>
        refine .typed_app n _ _ _ aexpr .int
          (.typed_var _ _ "rec" _ (by solve_lookup)) ?_
      · exact .typed_fst n _ _ aexpr aexpr (.typed_var _ _ "es" _ lookup_here)
      · exact .typed_snd n _ _ aexpr aexpr (.typed_var _ _ "es" _ lookup_here)
  · refine .typed_lam n _ "es" _ (.prod aexpr aexpr) .int
      (.prod_wf (aexpr_wf n) (aexpr_wf n)) ?_
    refine .typed_binOp n _ .multOp _ _ .int .int .int .mult_typed ?_ ?_ <;>
      refine .typed_app n _ _ _ aexpr .int
        (.typed_var _ _ "rec" _ (by solve_lookup)) ?_
    · exact .typed_fst n _ _ aexpr aexpr (.typed_var _ _ "es" _ lookup_here)
    · exact .typed_snd n _ _ aexpr aexpr (.typed_var _ _ "es" _ lookup_here)

/-! ## Exercise 3: lists -/

/-- `∃ α. α × (A → α → α) × (∀ β. α → β → (A → α → β) → β)`: nil, cons and a case analysis. -/
def list_t (A : Ty) : Ty :=
  .exist (.prod (.prod (.tVar 0) (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))))
    (.all (.fn (.tVar 1) (.fn (.tVar 0)
      (.fn (.fn (A.rename (fun n => n + 2)) (.fn (.tVar 1) (.tVar 0))) (.tVar 0))))))

/-- A list is a length paired with a right-nested tuple of its elements. -/
def mylist_impl : Val :=
  .packV (.pairV
    (.pairV
      (.pairV (.litV (.litInt 0)) (.litV .litUnit))
      (λᵥ: a l, Expr.pair (Expr.binOp .plusOp (.lit (.litInt 1)) (Expr.fst (.var "l")))
        (Expr.pair (.var "a") (Expr.snd (.var "l")))))
    (.tLamV (λ: l n c,
      Expr.ite (Expr.binOp .eqOp (Expr.fst (.var "l")) (.lit (.litInt 0))) (.var "n")
        (Expr.app (Expr.app (.var "c") (Expr.fst (Expr.snd (.var "l"))))
          (Expr.pair (Expr.binOp .minusOp (Expr.fst (.var "l")) (.lit (.litInt 1)))
            (Expr.snd (Expr.snd (.var "l"))))))))

/-- The elements of `l`, nested to the right and terminated by `()`. -/
def represents_list_rec : List Val → Val → Prop
  | [], v => v = .litV .litUnit
  | h :: l', v => ∃ v' : Val, v = .pairV h v' ∧ represents_list_rec l' v'

/-- A full list also stores its length: nothing inside the language can tell `()` from a pair. -/
def represents_list (l : List Val) (v : Val) : Prop :=
  ∃ (n : Int) (v' : Val), n = (l.length : Int) ∧ v = .pairV (.litV (.litInt n)) v' ∧
    represents_list_rec l v'

theorem represents_list_rec_closed (A : Ty) (k : Nat) :
    ∀ (l : List Val) (v : Val), represents_list_rec l v →
      (∀ w ∈ l, valRel δ_any A k w) → closed [] v.toExpr := by
  intro l
  induction l with
  | nil => intro v h _; subst h; rfl
  | cons h l' ih =>
    rintro v ⟨v', rfl, hrec⟩ hl
    have h₁ : closed [] h.toExpr := val_rel_is_closed h δ_any k A (hl h (by simp))
    have h₂ : closed [] v'.toExpr := ih v' hrec (fun w hw => hl w (by simp [hw]))
    simp only [Val.toExpr, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨h₁, h₂⟩

/-- The semantic type of the hidden representation. -/
def listSemType (A : Ty) : SemType where
  car k v := ∃ l : List Val, represents_list l v ∧ ∀ w ∈ l, valRel δ_any A k w
  closed_val k v := by
    rintro ⟨l, ⟨n, v', rfl, rfl, hrec⟩, hl⟩
    have := represents_list_rec_closed A k l v' hrec hl
    simp only [Val.toExpr, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨trivial, this⟩
  mono k k' v := by
    rintro ⟨l, hrep, hl⟩ hle
    exact ⟨l, hrep, fun w hw => val_rel_mono A δ_any k k' w hle (hl w hw)⟩

theorem sem_val_expr_rel_lam (A : Ty) (δ : TyVarInterp) (k : Nat) (x : Binder) (e : Expr)
    (h : valRel δ A k (.lamV x e)) : exprRel δ A k (.lam x e) :=
  sem_val_expr_rel A δ k (.lamV x e) h

theorem sem_val_expr_rel_pair (A : Ty) (δ : TyVarInterp) (k : Nat) (v₁ v₂ : Val)
    (h : valRel δ A k (.pairV v₁ v₂)) : exprRel δ A k (.pair v₁.toExpr v₂.toExpr) :=
  sem_val_expr_rel A δ k (.pairV v₁ v₂) h

theorem mylist_impl_sem_typed (A : Ty) (_hA : TypeWf 0 A) (k : Nat) :
    valRel δ_any (list_t A) k mylist_impl := by
  simp only [list_t, mylist_impl, valRel]
  refine ⟨_, rfl, listSemType A, ?_⟩
  refine ⟨_, _, rfl, ⟨_, _, rfl, ?_, ?_⟩, ?_⟩
  · -- mynil
    exact ⟨[], ⟨0, .litV .litUnit, rfl, rfl, rfl⟩, by simp⟩
  · -- mycons
    refine ⟨.bNamed "a", _, rfl, by decide, fun v₂ k' hk' hv₂ => ?_⟩
    have hv₂cl : closed [] v₂.toExpr :=
      val_rel_is_closed v₂ _ k' (A.rename (· + 1)) hv₂
    have hv₂' : valRel δ_any A k' v₂ := (sem_val_rel_cons A δ_any k' v₂ (listSemType A)).mpr hv₂
    simp +decide only [subst', subst, reduceIte]
    refine sem_val_expr_rel_lam _ _ _ _ _ ?_
    simp only [valRel]
    refine ⟨.bNamed "l", _, rfl, ?_, fun v₃ k'' hk'' hv₃ => ?_⟩
    · have h₂ : v₂.toExpr.isClosed ["l"] = true := closed_weaken_nil hv₂cl
      simp [closed, Expr.isClosed, Binder.cons, h₂]
    obtain ⟨l, ⟨n, hv, rfl, rfl, hrec⟩, hl⟩ := hv₃
    simp +decide only [subst', subst, reduceIte, subst_closed_nil hv₂cl, Val.toExpr]
    have hpv : Expr.isVal (Expr.pair v₂.toExpr hv.toExpr) := ⟨val_isVal v₂, val_isVal hv⟩
    refine expr_det_step_closure
      (det_step_pair_r _ (det_step_pair_r _ (det_step_snd _ _ trivial (val_isVal hv)))) ?_
    refine expr_det_step_closure
      (det_step_pair_l hpv (det_step_binop_r _ _ (det_step_fst _ _ trivial (val_isVal hv)))) ?_
    refine expr_det_step_closure
      (det_step_pair_l hpv (det_step_binOp .plusOp _ _ (.litV (.litInt 1))
        (.litV (.litInt (l.length : Int))) (.litV (.litInt (1 + (l.length : Int))))
        rfl rfl rfl)) ?_
    refine sem_val_expr_rel_pair _ _ _ (.litV (.litInt (1 + (l.length : Int))))
      (.pairV v₂ hv) ?_
    simp only [valRel]
    refine ⟨v₂ :: l, ⟨1 + (l.length : Int), .pairV v₂ hv, by simp; omega, rfl, hv, rfl, hrec⟩, ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact val_rel_mono A δ_any k' _ w (by omega) hv₂'
    · exact val_rel_mono A δ_any k'' _ w (by omega) (hl w hw)
  · -- mycase
    refine ⟨_, rfl, by decide, fun τ' => ?_⟩
    refine sem_val_expr_rel_lam _ _ _ _ _ ?_
    simp only [valRel]
    refine ⟨.bNamed "l", _, rfl, by decide, fun v₂ k₁ hk₁ hv₂ => ?_⟩
    obtain ⟨l, ⟨len, vl, rfl, rfl, hrec⟩, hl⟩ := hv₂
    have hvlcl : closed [] vl.toExpr := represents_list_rec_closed A k₁ l vl hrec hl
    have hvlcl' : ∀ X : List String, vl.toExpr.isClosed X = true :=
      fun X => closed_weaken_nil hvlcl
    simp +decide only [subst', subst, reduceIte, Val.toExpr]
    refine sem_val_expr_rel_lam _ _ _ _ _ ?_
    simp only [valRel]
    refine ⟨.bNamed "n", _, rfl, by simp [closed, Expr.isClosed, Binder.cons, hvlcl'],
      fun v₃ k₂ hk₂ hv₃ => ?_⟩
    have hv₃' : valRel (τ' .: (listSemType A) .: δ_any) (.tVar 0) k₂ v₃ := by
      simp only [valRel]; exact hv₃
    have hv₃cl : closed [] v₃.toExpr := τ'.closed_val k₂ v₃ hv₃
    have hv₃cl' : ∀ X : List String, v₃.toExpr.isClosed X = true :=
      fun X => closed_weaken_nil hv₃cl
    simp +decide only [subst', subst, reduceIte, subst_closed_nil hvlcl]
    refine sem_val_expr_rel_lam _ _ _ _ _ ?_
    simp only [valRel]
    refine ⟨.bNamed "c", _, rfl,
      by simp [closed, Expr.isClosed, Binder.cons, hvlcl', hv₃cl'],
      fun v₄ k₃ hk₃ hv₄ => ?_⟩
    have hv₄' : valRel (τ' .: (listSemType A) .: δ_any)
        (.fn (A.rename (fun n => n + 2)) (.fn (.tVar 1) (.tVar 0))) k₃ v₄ := by
      simp only [valRel]; exact hv₄
    simp +decide only [subst', subst, reduceIte, subst_closed_nil hvlcl,
      subst_closed_nil hv₃cl]
    cases l with
    | nil =>
      subst hrec
      refine expr_det_step_closure
        (det_step_if _ _ (det_step_binop_l _ trivial (det_step_fst _ _ trivial trivial))) ?_
      refine expr_det_step_closure
        (det_step_if _ _ (det_step_binOp .eqOp _ _ (.litV (.litInt 0)) (.litV (.litInt 0))
          (.litV (.litBool true)) rfl rfl rfl)) ?_
      refine expr_det_step_closure (det_step_if_true _ _) ?_
      refine sem_val_expr_rel _ _ _ v₃ ?_
      exact val_rel_mono (.tVar 0) _ k₂ _ v₃ (by omega) hv₃'
    | cons h l' =>
      obtain ⟨vl', rfl, hrec'⟩ := hrec
      have hvl'cl : closed [] vl'.toExpr :=
        represents_list_rec_closed A k₁ l' vl' hrec' (fun w hw => hl w (by simp [hw]))
      refine expr_det_step_closure
        (det_step_if _ _ (det_step_binop_l _ trivial
          (det_step_fst _ _ trivial ⟨val_isVal h, val_isVal vl'⟩))) ?_
      refine expr_det_step_closure
        (det_step_if _ _ (det_step_binOp .eqOp _ _
          (.litV (.litInt ((h :: l').length : Int))) (.litV (.litInt 0))
          (.litV (.litBool false)) rfl rfl (by simp [binOpEval] <;> omega))) ?_
      refine expr_det_step_closure (det_step_if_false _ _) ?_
      refine semantic_app (.tVar 1) (.tVar 0) _ _ _ _ ?_ ?_
      · refine semantic_app (A.rename (fun n => n + 2)) (.fn (.tVar 1) (.tVar 0)) _ _ _ _ ?_ ?_
        · exact sem_val_expr_rel _ _ _ v₄ (val_rel_mono _ _ k₃ _ v₄ (by omega) hv₄')
        · refine expr_det_step_closure
            (det_step_fst_lift (det_step_snd _ _ trivial ⟨val_isVal h, val_isVal vl'⟩)) ?_
          refine expr_det_step_closure
            (det_step_fst _ _ (val_isVal h) (val_isVal vl')) ?_
          refine sem_val_expr_rel _ _ _ h ?_
          have hshift : A.rename (fun n => n + 2) = (A.rename (· + 1)).rename (· + 1) :=
            (Ty.rename_rename A (· + 1) (· + 1)).symm
          rw [hshift]
          refine (sem_val_rel_cons (A.rename (· + 1)) _ _ h τ').mp ?_
          refine (sem_val_rel_cons A δ_any _ h (listSemType A)).mp ?_
          exact val_rel_mono A δ_any k₁ _ h (by omega) (hl h (by simp))
      · refine expr_det_step_closure
          (det_step_pair_r _ (det_step_snd_lift
            (det_step_snd _ _ trivial ⟨val_isVal h, val_isVal vl'⟩))) ?_
        refine expr_det_step_closure
          (det_step_pair_r _ (det_step_snd _ _ (val_isVal h) (val_isVal vl'))) ?_
        refine expr_det_step_closure
          (det_step_pair_l (val_isVal vl') (det_step_binop_l _ trivial
            (det_step_fst _ _ trivial ⟨val_isVal h, val_isVal vl'⟩))) ?_
        refine expr_det_step_closure
          (det_step_pair_l (val_isVal vl') (det_step_binOp .minusOp _ _
            (.litV (.litInt ((h :: l').length : Int))) (.litV (.litInt 1))
            (.litV (.litInt (l'.length : Int))) rfl rfl (by simp [binOpEval] <;> omega))) ?_
        refine sem_val_expr_rel_pair _ _ _ (.litV (.litInt (l'.length : Int))) vl' ?_
        simp only [valRel]
        refine ⟨l', ⟨(l'.length : Int), vl', rfl, rfl, hrec'⟩, fun w hw => ?_⟩
        exact val_rel_mono A δ_any k₁ _ w (by omega) (hl w (by simp [hw]))

end SystemFMu
