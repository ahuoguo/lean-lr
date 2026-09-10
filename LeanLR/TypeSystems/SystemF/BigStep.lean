import LeanLR.TypeSystems.SystemF.Lang
import LeanLR.TypeSystems.SystemF.Notation
import LeanLR.TypeSystems.SystemF.Pure
import LeanLR.TypeSystems.SystemF.ParallelSubst

/-!
# System F: big-step semantics

`systemf/bigstep.v`. A call-by-value big-step evaluation relation, and the proof that it agrees
with the contextual semantics: `big_step e v` implies `e ↠* v`.
-/

open Iris.Std

namespace SystemF

/-- Call-by-value evaluation to a value. -/
inductive BigStep : Expr → Val → Prop where
  | bs_lit (l : BaseLit) : BigStep (.lit l) (.litV l)
  | bs_lam (x : Binder) (e : Expr) : BigStep (.lam x e) (.lamV x e)
  | bs_binop e₁ e₂ v₁ v₂ v' op :
      BigStep e₁ v₁ → BigStep e₂ v₂ → binOpEval op v₁ v₂ = some v' →
      BigStep (.binOp op e₁ e₂) v'
  | bs_unop e v v' op :
      BigStep e v → unOpEval op v = some v' → BigStep (.unOp op e) v'
  | bs_app e₁ e₂ x e v₂ v :
      BigStep e₁ (.lamV x e) → BigStep e₂ v₂ → BigStep (subst' x v₂.toExpr e) v →
      BigStep (.app e₁ e₂) v
  | bs_tapp e₁ e₂ v :
      BigStep e₁ (.tLamV e₂) → BigStep e₂ v → BigStep (.tApp e₁) v
  | bs_tlam e : BigStep (.tLam e) (.tLamV e)
  | bs_pack e v : BigStep e v → BigStep (.pack e) (.packV v)
  | bs_unpack e₁ e₂ v₁ v₂ x :
      BigStep e₁ (.packV v₁) → BigStep (subst' x v₁.toExpr e₂) v₂ →
      BigStep (.unpack x e₁ e₂) v₂
  | bs_if_true e₀ e₁ e₂ v :
      BigStep e₀ (.litV (.litBool true)) → BigStep e₁ v → BigStep (.ite e₀ e₁ e₂) v
  | bs_if_false e₀ e₁ e₂ v :
      BigStep e₀ (.litV (.litBool false)) → BigStep e₂ v → BigStep (.ite e₀ e₁ e₂) v
  | bs_pair e₁ e₂ v₁ v₂ :
      BigStep e₁ v₁ → BigStep e₂ v₂ → BigStep (.pair e₁ e₂) (.pairV v₁ v₂)
  | bs_fst e v₁ v₂ : BigStep e (.pairV v₁ v₂) → BigStep (.fst e) v₁
  | bs_snd e v₁ v₂ : BigStep e (.pairV v₁ v₂) → BigStep (.snd e) v₂
  | bs_injl e v : BigStep e v → BigStep (.injL e) (.injLV v)
  | bs_injr e v : BigStep e v → BigStep (.injR e) (.injRV v)
  | bs_casel e e₁ e₂ v v' :
      BigStep e (.injLV v) → BigStep (.app e₁ v.toExpr) v' → BigStep (.case e e₁ e₂) v'
  | bs_caser e e₁ e₂ v v' :
      BigStep e (.injRV v) → BigStep (.app e₂ v.toExpr) v' → BigStep (.case e e₁ e₂) v'

theorem fill_contextual_steps {K : Ectx} {e₁ e₂ : Expr} (h : ContextualSteps e₁ e₂) :
    ContextualSteps (fill K e₁) (fill K e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (fill_contextual_step hs) ih

/-- Big-step evaluation is contextual reduction to a value. -/
theorem big_step_contextual {e : Expr} {v : Val} (h : BigStep e v) :
    ContextualSteps e v.toExpr := by
  induction h with
  | bs_lit _ | bs_lam _ _ | bs_tlam _ => exact .refl
  | bs_binop e₁ e₂ v₁ v₂ v' op _ _ hop ih₁ ih₂ =>
    refine .trans (fill_contextual_steps (K := [.binOpRCtx op e₁]) ih₂) ?_
    refine .trans (fill_contextual_steps (K := [.binOpLCtx op v₂]) ih₁) ?_
    exact .single (base_contextual_step
      (.binOpS op v₁.toExpr v₂.toExpr v₁ v₂ v' (toVal?_toExpr v₁) (toVal?_toExpr v₂) hop))
  | bs_unop e v v' op _ hop ih =>
    refine .trans (fill_contextual_steps (K := [.unOpCtx op]) ih) ?_
    exact .single (base_contextual_step (.unOpS op v.toExpr v v' (toVal?_toExpr v) hop))
  | bs_app e₁ e₂ x e v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    refine .trans (fill_contextual_steps (K := [.appRCtx e₁]) ih₂) ?_
    refine .trans (fill_contextual_steps (K := [.appLCtx v₂]) ih₁) ?_
    exact .step (base_contextual_step (.betaS x e v₂.toExpr (val_isVal v₂))) ih₃
  | bs_tapp e₁ e₂ v _ _ ih₁ ih₂ =>
    refine .trans (fill_contextual_steps (K := [.tAppCtx]) ih₁) ?_
    exact .step (base_contextual_step (.tBetaS e₂)) ih₂
  | bs_pack e v _ ih => exact fill_contextual_steps (K := [.packCtx]) ih
  | bs_unpack e₁ e₂ v₁ v₂ x _ _ ih₁ ih₂ =>
    refine .trans (fill_contextual_steps (K := [.unpackCtx x e₂]) ih₁) ?_
    exact .step (base_contextual_step (.unpackS x v₁.toExpr e₂ (val_isVal v₁))) ih₂
  | bs_if_true e₀ e₁ e₂ v _ _ ih₀ ih₁ =>
    refine .trans (fill_contextual_steps (K := [.ifCtx e₁ e₂]) ih₀) ?_
    exact .step (base_contextual_step (.ifTrueS e₁ e₂)) ih₁
  | bs_if_false e₀ e₁ e₂ v _ _ ih₀ ih₂ =>
    refine .trans (fill_contextual_steps (K := [.ifCtx e₁ e₂]) ih₀) ?_
    exact .step (base_contextual_step (.ifFalseS e₁ e₂)) ih₂
  | bs_pair e₁ e₂ v₁ v₂ _ _ ih₁ ih₂ =>
    refine .trans (fill_contextual_steps (K := [.pairRCtx e₁]) ih₂) ?_
    exact fill_contextual_steps (K := [.pairLCtx v₂]) ih₁
  | bs_fst e v₁ v₂ _ ih =>
    refine .trans (fill_contextual_steps (K := [.fstCtx]) ih) ?_
    exact .single (base_contextual_step
      (.fstS v₁.toExpr v₂.toExpr (val_isVal v₁) (val_isVal v₂)))
  | bs_snd e v₁ v₂ _ ih =>
    refine .trans (fill_contextual_steps (K := [.sndCtx]) ih) ?_
    exact .single (base_contextual_step
      (.sndS v₁.toExpr v₂.toExpr (val_isVal v₁) (val_isVal v₂)))
  | bs_injl e v _ ih => exact fill_contextual_steps (K := [.injLCtx]) ih
  | bs_injr e v _ ih => exact fill_contextual_steps (K := [.injRCtx]) ih
  | bs_casel e e₁ e₂ v v' _ _ ih ih' =>
    refine .trans (fill_contextual_steps (K := [.caseCtx e₁ e₂]) ih) ?_
    exact .step (base_contextual_step (.caseLS v.toExpr e₁ e₂ (val_isVal v))) ih'
  | bs_caser e e₁ e₂ v v' _ _ ih ih' =>
    refine .trans (fill_contextual_steps (K := [.caseCtx e₁ e₂]) ih) ?_
    exact .step (base_contextual_step (.caseRS v.toExpr e₁ e₂ (val_isVal v))) ih'

theorem big_step_of_val {e : Expr} {v : Val} (h : e = v.toExpr) : BigStep e v := by
  subst h
  induction v with
  | litV l => exact .bs_lit l
  | lamV x e => exact .bs_lam x e
  | tLamV e => exact .bs_tlam e
  | packV v ih => exact .bs_pack _ v ih
  | pairV v₁ v₂ ih₁ ih₂ => exact .bs_pair _ _ v₁ v₂ ih₁ ih₂
  | injLV v ih => exact .bs_injl _ v ih
  | injRV v ih => exact .bs_injr _ v ih

/-- Values evaluate to themselves. -/
theorem big_step_val {v v' : Val} (h : BigStep v.toExpr v') : v' = v := by
  suffices hgen : ∀ (e : Expr) (w : Val), BigStep e w → ∀ u : Val, e = u.toExpr → w = u by
    exact hgen _ _ h v rfl
  clear h v v'
  intro e w hb
  induction hb with
  | bs_lit l => intro u hu; cases u <;> simp_all [Val.toExpr]
  | bs_lam x e => intro u hu; cases u <;> simp_all [Val.toExpr]
  | bs_tlam e => intro u hu; cases u <;> simp_all [Val.toExpr]
  | bs_pack e v _ ih =>
    intro u hu
    cases u <;> simp only [Val.toExpr] at hu <;>
      solve
        | (exfalso; simp at hu)
        | (rename_i w; simp only [Expr.pack.injEq] at hu; exact congrArg Val.packV (ih w hu))
  | bs_injl e v _ ih =>
    intro u hu
    cases u <;> simp only [Val.toExpr] at hu <;>
      solve
        | (exfalso; simp at hu)
        | (rename_i w; simp only [Expr.injL.injEq] at hu; exact congrArg Val.injLV (ih w hu))
  | bs_injr e v _ ih =>
    intro u hu
    cases u <;> simp only [Val.toExpr] at hu <;>
      solve
        | (exfalso; simp at hu)
        | (rename_i w; simp only [Expr.injR.injEq] at hu; exact congrArg Val.injRV (ih w hu))
  | bs_pair e₁ e₂ v₁ v₂ _ _ ih₁ ih₂ =>
    intro u hu
    cases u <;> simp only [Val.toExpr] at hu <;>
      solve
        | (exfalso; simp at hu)
        | (rename_i w₁ w₂
           simp only [Expr.pair.injEq] at hu
           rw [ih₁ w₁ hu.1, ih₂ w₂ hu.2])
  | _ => intro u hu; cases u <;> simp [Val.toExpr] at hu

/-- The result of a binary operation is a closed literal. -/
theorem binOpEval_closed {op : BinOp} {v₁ v₂ v' : Val} (h : binOpEval op v₁ v₂ = some v') :
    closed [] v'.toExpr := by
  unfold binOpEval at h
  split at h <;>
    solve
      | (exfalso; simp at h)
      | (injection h with h; subst h; rfl)

/-- The result of a unary operation is a closed literal. -/
theorem unOpEval_closed {op : UnOp} {v v' : Val} (h : unOpEval op v = some v') :
    closed [] v'.toExpr := by
  unfold unOpEval at h
  split at h <;>
    solve
      | (exfalso; simp at h)
      | (injection h with h; subst h; rfl)

theorem big_step_preserve_closed {e : Expr} {v : Val} (hcl : closed [] e) (h : BigStep e v) :
    closed [] v.toExpr := by
  induction h with
  | bs_lit l => exact hcl
  | bs_lam x e => exact hcl
  | bs_tlam e => exact hcl
  | bs_binop e₁ e₂ v₁ v₂ v' op _ _ hop _ _ => exact binOpEval_closed hop
  | bs_unop e v v' op _ hop _ => exact unOpEval_closed hop
  | bs_app e₁ e₂ x e v₂ v h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    refine ih₃ ?_
    have hlam := ih₁ hcl.1
    have hv₂ := ih₂ hcl.2
    simp only [closed, Val.toExpr, Expr.isClosed] at hlam
    exact closed_do_subst' hv₂ hlam
  | bs_tapp e₁ e₂ v _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed] at hcl
    exact ih₂ (ih₁ hcl)
  | bs_pack e v _ ih => exact ih hcl
  | bs_unpack e₁ e₂ v₁ v₂ x h₁ h₂ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    refine ih₂ ?_
    have hv₁ := ih₁ hcl.1
    simp only [closed, Val.toExpr, Expr.isClosed] at hv₁
    exact closed_do_subst' hv₁ hcl.2
  | bs_if_true e₀ e₁ e₂ v _ _ _ ih₁ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    exact ih₁ hcl.1.2
  | bs_if_false e₀ e₁ e₂ v _ _ _ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    exact ih₂ hcl.2
  | bs_pair e₁ e₂ v₁ v₂ _ _ ih₁ ih₂ =>
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true] at hcl ⊢
    exact ⟨ih₁ hcl.1, ih₂ hcl.2⟩
  | bs_fst e v₁ v₂ _ ih =>
    simp only [closed, Expr.isClosed] at hcl
    have := ih hcl
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true] at this
    exact this.1
  | bs_snd e v₁ v₂ _ ih =>
    simp only [closed, Expr.isClosed] at hcl
    have := ih hcl
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true] at this
    exact this.2
  | bs_injl e v _ ih => exact ih hcl
  | bs_injr e v _ ih => exact ih hcl
  | bs_casel e e₁ e₂ v v' _ _ ih ih' =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    refine ih' ?_
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨hcl.1.2, ih hcl.1.1⟩
  | bs_caser e e₁ e₂ v v' _ _ ih ih' =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hcl
    refine ih' ?_
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨hcl.2, ih hcl.1.1⟩

end SystemF
