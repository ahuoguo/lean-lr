import LeanLR.TypeSystems.SystemF.Lang
import LeanLR.TypeSystems.SystemF.Notation
import LeanLR.TypeSystems.SystemF.Types
import LeanLR.TypeSystems.SystemF.TypeSafety
import LeanLR.TypeSystems.SystemF.BigStep
import LeanLR.TypeSystems.SystemF.ParallelSubst

/-!
# System F: Church encodings

`systemf/church_encodings.v`. Unit, booleans, products and the natural numbers, all encoded with
polymorphism alone, together with their typing rules and their big-step behaviour.
-/

open Iris.Std

namespace SystemF

/-! ## Context lookup helpers

Rocq discharges these with `simplify_map_eq`; the port needs them spelled out. -/

theorem lookup_here {Γ : TypingContext} {x : String} {A : Ty} :
    get? (M := TyMapStr) (insert (M := TyMapStr) Γ x A) x = some A :=
  LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl

theorem lookup_there {Γ : TypingContext} {x y : String} {A B : Ty} (h : x ≠ y)
    (hy : get? (M := TyMapStr) Γ y = some B) :
    get? (M := TyMapStr) (insert (M := TyMapStr) Γ x A) y = some B := by
  rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) h]
  exact hy

/-! ## The empty type -/

def empty_type : Ty := .all (.tVar 0)

/-! ## Unit -/

def unit_type : Ty := .all (.fn (.tVar 0) (.tVar 0))

def unit_inh : Val := .tLamV (.lam (.bNamed "x") (.var "x"))

theorem unit_wf (n : Nat) : TypeWf n unit_type :=
  .all_wf (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega)))

theorem unit_inh_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ unit_inh.toExpr unit_type :=
  .typed_tLam n Γ _ _
    (.typed_lam (n + 1) (shiftCtx Γ) "x" (.var "x") (.tVar 0) (.tVar 0)
      (.tVar_wf (by omega))
      (.typed_var _ _ "x" _ lookup_here))

/-! ## Booleans -/

def bool_type : Ty := .all (.fn (.tVar 0) (.fn (.tVar 0) (.tVar 0)))

def bool_true : Val := .tLamV (.lam (.bNamed "t") (.lam (.bNamed "f") (.var "t")))

def bool_false : Val := .tLamV (.lam (.bNamed "t") (.lam (.bNamed "f") (.var "f")))

def bool_if (e e₁ e₂ : Expr) : Expr :=
  .app (.app (.app (.tApp e) (.lam .bAnon e₁)) (.lam .bAnon e₂)) unit_inh.toExpr

theorem bool_true_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ bool_true.toExpr bool_type :=
  .typed_tLam n Γ _ _
    (.typed_lam (n + 1) (shiftCtx Γ) "t" _ (.tVar 0) (.fn (.tVar 0) (.tVar 0))
      (.tVar_wf (by omega))
      (.typed_lam (n + 1) _ "f" (.var "t") (.tVar 0) (.tVar 0) (.tVar_wf (by omega))
        (.typed_var _ _ "t" _ (lookup_there (by decide) lookup_here))))

theorem bool_false_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ bool_false.toExpr bool_type :=
  .typed_tLam n Γ _ _
    (.typed_lam (n + 1) (shiftCtx Γ) "t" _ (.tVar 0) (.fn (.tVar 0) (.tVar 0))
      (.tVar_wf (by omega))
      (.typed_lam (n + 1) _ "f" (.var "f") (.tVar 0) (.tVar 0) (.tVar_wf (by omega))
        (.typed_var _ _ "f" _ lookup_here)))

theorem bool_if_typed (n : Nat) (Γ : TypingContext) (e e₁ e₂ : Expr) (A : Ty)
    (hA : TypeWf n A) (h₁ : SynTyped n Γ e₁ A) (h₂ : SynTyped n Γ e₂ A)
    (he : SynTyped n Γ e bool_type) : SynTyped n Γ (bool_if e e₁ e₂) A := by
  refine .typed_app n Γ _ _ unit_type A ?_ (unit_inh_typed n Γ)
  refine .typed_app n Γ _ _ (.fn unit_type A) (.fn unit_type A) ?_
    (.typed_lam_anon n Γ e₂ unit_type A (unit_wf n) h₂)
  refine .typed_app n Γ _ _ (.fn unit_type A)
    (.fn (.fn unit_type A) (.fn unit_type A)) ?_
    (.typed_lam_anon n Γ e₁ unit_type A (unit_wf n) h₁)
  exact .typed_tApp n Γ e _ (.fn unit_type A) (.fn_wf (unit_wf n) hA) he

theorem bool_if_true_red (e₁ e₂ : Expr) (v : Val) (hcl : closed [] e₁) (h : BigStep e₁ v) :
    BigStep (bool_if bool_true.toExpr e₁ e₂) v := by
  refine .bs_app _ _ .bAnon e₁ unit_inh v ?_ (big_step_of_val rfl) (by simpa only [subst', id_eq] using h)
  refine .bs_app _ _ (.bNamed "f") (.lam .bAnon e₁) (.lamV .bAnon e₂) _ ?_
    (big_step_of_val rfl) ?_
  · refine .bs_app _ _ (.bNamed "t") (.lam (.bNamed "f") (.var "t")) (.lamV .bAnon e₁) _ ?_
      (big_step_of_val rfl) ?_
    · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
    · simp +decide only [subst', subst, Val.toExpr]
      exact .bs_lam _ _
  · simp +decide only [subst', subst, Val.toExpr, subst_closed_nil hcl]
    exact .bs_lam _ _

/-- Rocq keeps the `is_closed [] e₂` premise here for symmetry with `bool_if_true_red`; the Lean
proof does not need it, since `bool_false` discards its first argument. -/
theorem bool_if_false_red (e₁ e₂ : Expr) (v : Val) (_hcl : closed [] e₂) (h : BigStep e₂ v) :
    BigStep (bool_if bool_false.toExpr e₁ e₂) v := by
  refine .bs_app _ _ .bAnon e₂ unit_inh v ?_ (big_step_of_val rfl) (by simpa only [subst', id_eq] using h)
  refine .bs_app _ _ (.bNamed "f") (.var "f") (.lamV .bAnon e₂) _ ?_
    (big_step_of_val rfl) ?_
  · refine .bs_app _ _ (.bNamed "t") (.lam (.bNamed "f") (.var "f")) (.lamV .bAnon e₁) _ ?_
      (big_step_of_val rfl) ?_
    · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
    · simp +decide only [subst', subst, Val.toExpr]
      exact .bs_lam _ _
  · simp +decide only [subst', subst, Val.toExpr]
    exact big_step_of_val rfl

/-! ## Products -/

def product_type (A B : Ty) : Ty :=
  .all (.fn (.fn (A.rename (· + 1)) (.fn (B.rename (· + 1)) (.tVar 0))) (.tVar 0))

def pair_val (v₁ v₂ : Val) : Val :=
  .tLamV (.lam (.bNamed "p") (.app (.app (.var "p") v₁.toExpr) v₂.toExpr))

def pair_expr (e₁ e₂ : Expr) : Expr :=
  .app (.lam (.bNamed "x2")
    (.app (.lam (.bNamed "x1")
      (.tLam (.lam (.bNamed "p") (.app (.app (.var "p") (.var "x1")) (.var "x2"))))) e₁)) e₂

def proj1_expr (e : Expr) : Expr :=
  .app (.tApp e) (.lam (.bNamed "x") (.lam (.bNamed "y") (.var "x")))

def proj2_expr (e : Expr) : Expr :=
  .app (.tApp e) (.lam (.bNamed "x") (.lam (.bNamed "y") (.var "y")))

theorem proj1_red (v₁ v₂ : Val) (h₁ : closed [] v₁.toExpr) (h₂ : closed [] v₂.toExpr) :
    BigStep (proj1_expr (pair_val v₁ v₂).toExpr) v₁ := by
  refine .bs_app _ _ (.bNamed "p") (.app (.app (.var "p") v₁.toExpr) v₂.toExpr)
    (.lamV (.bNamed "x") (.lam (.bNamed "y") (.var "x"))) v₁ ?_ (big_step_of_val rfl) ?_
  · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
  · simp +decide only [subst', subst, Val.toExpr, subst_closed_nil h₁, subst_closed_nil h₂]
    refine .bs_app _ _ (.bNamed "y") v₁.toExpr v₂ v₁ ?_ (big_step_of_val rfl) ?_
    · refine .bs_app _ _ (.bNamed "x") (.lam (.bNamed "y") (.var "x")) v₁ _
        (big_step_of_val rfl) (big_step_of_val rfl) ?_
      simp +decide only [subst', subst]
      exact .bs_lam _ _
    · simp +decide only [subst', subst_closed_nil h₁]
      exact big_step_of_val rfl

theorem proj2_red (v₁ v₂ : Val) (h₁ : closed [] v₁.toExpr) (h₂ : closed [] v₂.toExpr) :
    BigStep (proj2_expr (pair_val v₁ v₂).toExpr) v₂ := by
  refine .bs_app _ _ (.bNamed "p") (.app (.app (.var "p") v₁.toExpr) v₂.toExpr)
    (.lamV (.bNamed "x") (.lam (.bNamed "y") (.var "y"))) v₂ ?_ (big_step_of_val rfl) ?_
  · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
  · simp +decide only [subst', subst, Val.toExpr, subst_closed_nil h₁, subst_closed_nil h₂]
    refine .bs_app _ _ (.bNamed "y") (.var "y") v₂ v₂ ?_ (big_step_of_val rfl) ?_
    · refine .bs_app _ _ (.bNamed "x") (.lam (.bNamed "y") (.var "y")) v₁ _
        (big_step_of_val rfl) (big_step_of_val rfl) ?_
      simp +decide only [subst', subst]
      exact .bs_lam _ _
    · simp +decide only [subst']
      exact big_step_of_val rfl

theorem pair_red (e₁ e₂ : Expr) (v₁ v₂ : Val) (h₂cl : closed [] v₂.toExpr)
    (h₁cl : closed [] e₁) (h₁ : BigStep e₁ v₁) (h₂ : BigStep e₂ v₂) :
    BigStep (pair_expr e₁ e₂) (pair_val v₁ v₂) := by
  refine .bs_app _ _ (.bNamed "x2")
    (.app (.lam (.bNamed "x1")
      (.tLam (.lam (.bNamed "p") (.app (.app (.var "p") (.var "x1")) (.var "x2"))))) e₁)
    v₂ _ (.bs_lam _ _) h₂ ?_
  simp +decide only [subst', subst, subst_closed_nil h₁cl]
  refine .bs_app _ _ (.bNamed "x1")
    (.tLam (.lam (.bNamed "p") (.app (.app (.var "p") (.var "x1")) v₂.toExpr)))
    v₁ _ (.bs_lam _ _) h₁ ?_
  simp +decide only [subst', subst, subst_closed_nil h₂cl]
  exact .bs_tlam _

theorem proj1_typed (n : Nat) (Γ : TypingContext) (e : Expr) (A B : Ty)
    (hA : TypeWf n A) (hB : TypeWf n B) (he : SynTyped n Γ e (product_type A B)) :
    SynTyped n Γ (proj1_expr e) A := by
  have htapp : SynTyped n Γ (.tApp e)
      (Ty.subst1 (.fn (.fn (A.rename (· + 1)) (.fn (B.rename (· + 1)) (.tVar 0))) (.tVar 0)) A) :=
    .typed_tApp n Γ e _ A hA he
  simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id] at htapp
  refine .typed_app n Γ _ _ (.fn A (.fn B A)) A htapp ?_
  exact .typed_lam n Γ "x" _ A (.fn B A) hA
    (.typed_lam n _ "y" (.var "x") B A hB
      (.typed_var _ _ "x" _ (lookup_there (by decide) lookup_here)))

theorem proj2_typed (n : Nat) (Γ : TypingContext) (e : Expr) (A B : Ty)
    (hA : TypeWf n A) (hB : TypeWf n B) (he : SynTyped n Γ e (product_type A B)) :
    SynTyped n Γ (proj2_expr e) B := by
  have htapp : SynTyped n Γ (.tApp e)
      (Ty.subst1 (.fn (.fn (A.rename (· + 1)) (.fn (B.rename (· + 1)) (.tVar 0))) (.tVar 0)) B) :=
    .typed_tApp n Γ e _ B hB he
  simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id] at htapp
  refine .typed_app n Γ _ _ (.fn A (.fn B B)) B htapp ?_
  exact .typed_lam n Γ "x" _ A (.fn B B) hA
    (.typed_lam n _ "y" (.var "y") B B hB (.typed_var _ _ "y" _ lookup_here))

theorem pair_expr_typed (n : Nat) (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (hx2 : get? (M := TyMapStr) Γ "x2" = none) (hA : TypeWf n A) (hB : TypeWf n B)
    (h₁ : SynTyped n Γ e₁ A) (h₂ : SynTyped n Γ e₂ B) :
    SynTyped n Γ (pair_expr e₁ e₂) (product_type A B) := by
  have hAup : TypeWf (n + 1) (A.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA
  have hBup : TypeWf (n + 1) (B.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) B (fun m hm => Nat.succ_lt_succ hm) hB
  -- `e₁` is still typed after `x2` is bound, because `Γ` does not bind `x2`.
  have h₁' : SynTyped n (insert (M := TyMapStr) Γ "x2" B) e₁ A := by
    refine typed_weakening h₁ (fun y C hy => ?_) (Nat.le_refl n)
    by_cases hxy : "x2" = y
    · subst hxy
      rw [hx2] at hy
      exact absurd hy (by simp)
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy]
      exact hy
  refine .typed_app n Γ _ _ B (product_type A B) ?_ h₂
  refine .typed_lam n Γ "x2" _ B (product_type A B) hB ?_
  refine .typed_app n _ _ _ A (product_type A B) ?_ h₁'
  refine .typed_lam n _ "x1" _ A (product_type A B) hA ?_
  refine .typed_tLam n _ _ _ ?_
  rw [shiftCtx_insert, shiftCtx_insert]
  refine .typed_lam (n + 1) _ "p" _ (.fn (A.rename (· + 1)) (.fn (B.rename (· + 1)) (.tVar 0)))
    (.tVar 0) (.fn_wf hAup (.fn_wf hBup (.tVar_wf (by omega)))) ?_
  refine .typed_app (n + 1) _ _ _ (B.rename (· + 1)) (.tVar 0) ?_ ?_
  · refine .typed_app (n + 1) _ _ _ (A.rename (· + 1))
      (.fn (B.rename (· + 1)) (.tVar 0)) (.typed_var _ _ "p" _ lookup_here) ?_
    exact .typed_var _ _ "x1" _ (lookup_there (by decide) lookup_here)
  · exact .typed_var _ _ "x2" _
      (lookup_there (by decide) (lookup_there (by decide) lookup_here))

/-! ## Church numerals -/

def nat_type : Ty := .all (.fn (.tVar 0) (.fn (.fn (.tVar 0) (.tVar 0)) (.tVar 0)))

def zero_val : Val := .tLamV (.lam (.bNamed "z") (.lam (.bNamed "s") (.var "z")))

/-- `Nat.iter n (App "s") "z"`. -/
def churchIter : Nat → Expr
  | 0 => .var "z"
  | m + 1 => .app (.var "s") (churchIter m)

def num_val (m : Nat) : Val := .tLamV (.lam (.bNamed "z") (.lam (.bNamed "s") (churchIter m)))

def succ_val : Val :=
  .lamV (.bNamed "n") (.tLam (.lam (.bNamed "z") (.lam (.bNamed "s")
    (.app (.var "s") (.app (.app (.tApp (.var "n")) (.var "z")) (.var "s"))))))

def iter_val : Val :=
  .lamV (.bNamed "n") (.lam (.bNamed "z") (.lam (.bNamed "s")
    (.app (.app (.tApp (.var "n")) (.var "z")) (.var "s"))))

theorem nat_type_wf (n : Nat) : TypeWf n nat_type :=
  .all_wf (.fn_wf (.tVar_wf (by omega))
    (.fn_wf (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))) (.tVar_wf (by omega))))

theorem zero_typed (Γ : TypingContext) (n : Nat) : SynTyped n Γ zero_val.toExpr nat_type :=
  .typed_tLam n Γ _ _
    (.typed_lam (n + 1) _ "z" _ (.tVar 0) (.fn (.fn (.tVar 0) (.tVar 0)) (.tVar 0))
      (.tVar_wf (by omega))
      (.typed_lam (n + 1) _ "s" (.var "z") (.fn (.tVar 0) (.tVar 0)) (.tVar 0)
        (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega)))
        (.typed_var _ _ "z" _ (lookup_there (by decide) lookup_here))))

theorem num_typed (Γ : TypingContext) (n m : Nat) : SynTyped n Γ (num_val m).toExpr nat_type := by
  refine .typed_tLam n Γ _ _ ?_
  refine .typed_lam (n + 1) _ "z" _ (.tVar 0) (.fn (.fn (.tVar 0) (.tVar 0)) (.tVar 0))
    (.tVar_wf (by omega)) ?_
  refine .typed_lam (n + 1) _ "s" _ (.fn (.tVar 0) (.tVar 0)) (.tVar 0)
    (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))) ?_
  induction m with
  | zero => exact .typed_var _ _ "z" _ (lookup_there (by decide) lookup_here)
  | succ k ih =>
    exact .typed_app (n + 1) _ _ _ (.tVar 0) (.tVar 0)
      (.typed_var _ _ "s" _ lookup_here) ih

theorem succ_typed (Γ : TypingContext) (n : Nat) :
    SynTyped n Γ succ_val.toExpr (.fn nat_type nat_type) := by
  refine .typed_lam n Γ "n" _ nat_type nat_type (nat_type_wf n) ?_
  refine .typed_tLam n _ _ _ ?_
  rw [shiftCtx_insert, type_wf_closed_rename nat_type (· + 1) (nat_type_wf 0)]
  refine .typed_lam (n + 1) _ "z" _ (.tVar 0) (.fn (.fn (.tVar 0) (.tVar 0)) (.tVar 0))
    (.tVar_wf (by omega)) ?_
  refine .typed_lam (n + 1) _ "s" _ (.fn (.tVar 0) (.tVar 0)) (.tVar 0)
    (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))) ?_
  refine .typed_app (n + 1) _ _ _ (.tVar 0) (.tVar 0) (.typed_var _ _ "s" _ lookup_here) ?_
  refine .typed_app (n + 1) _ _ _ (.fn (.tVar 0) (.tVar 0)) (.tVar 0) ?_
    (.typed_var _ _ "s" _ lookup_here)
  refine .typed_app (n + 1) _ _ _ (.tVar 0)
    (.fn (.fn (.tVar 0) (.tVar 0)) (.tVar 0)) ?_
    (.typed_var _ _ "z" _ (lookup_there (by decide) lookup_here))
  exact .typed_tApp (n + 1) _ _ _ (.tVar 0) (.tVar_wf (by omega))
    (.typed_var _ _ "n" _
      (lookup_there (by decide) (lookup_there (by decide) lookup_here)))

theorem iter_typed (n : Nat) (Γ : TypingContext) (C : Ty) (hC : TypeWf n C) :
    SynTyped n Γ iter_val.toExpr (.fn nat_type (.fn C (.fn (.fn C C) C))) := by
  refine .typed_lam n Γ "n" _ nat_type (.fn C (.fn (.fn C C) C)) (nat_type_wf n) ?_
  refine .typed_lam n _ "z" _ C (.fn (.fn C C) C) hC ?_
  refine .typed_lam n _ "s" _ (.fn C C) C (.fn_wf hC hC) ?_
  refine .typed_app n _ _ _ (.fn C C) C ?_ (.typed_var _ _ "s" _ lookup_here)
  refine .typed_app n _ _ _ C (.fn (.fn C C) C) ?_
    (.typed_var _ _ "z" _ (lookup_there (by decide) lookup_here))
  exact .typed_tApp n _ _ _ C hC
    (.typed_var _ _ "n" _
      (lookup_there (by decide) (lookup_there (by decide) lookup_here)))

end SystemF
