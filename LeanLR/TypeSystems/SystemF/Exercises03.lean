import LeanLR.TypeSystems.SystemF.LogRel
import LeanLR.TypeSystems.SystemF.ChurchEncodings
import LeanLR.TypeSystems.SystemF.ChurchEncodingsFaithful
import LeanLR.TypeSystems.SystemF.Tactics

/-!
# System F, exercise sheet 3

`systemf/exercises03_sol.v`. Polymorphic plumbing functions and their types; a translation of
named types into De Bruijn form; Church encodings of sums and lists; and five free theorems read
off the logical relation.
-/

open Iris.Std

namespace SystemF

/-! ## Exercise 1 (LN 22): universal fun -/

def fun_comp : Val := .tLamV (Λₑ (Λₑ (λ: f g x, ("g" : Expr) (("f" : Expr) "x"))))

def fun_comp_type : Ty :=
  .all (.all (.all (.fn (.fn (.tVar 2) (.tVar 1))
    (.fn (.fn (.tVar 1) (.tVar 0)) (.fn (.tVar 2) (.tVar 0))))))

theorem fun_comp_typed :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) fun_comp.toExpr fun_comp_type := by solve_typing

def swap_args : Val := .tLamV (Λₑ (Λₑ (λ: f x y, (("f" : Expr) "y") "x")))

def swap_args_type : Ty :=
  .all (.all (.all (.fn (.fn (.tVar 2) (.fn (.tVar 1) (.tVar 0)))
    (.fn (.tVar 1) (.fn (.tVar 2) (.tVar 0))))))

theorem swap_args_typed :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) swap_args.toExpr swap_args_type := by solve_typing

def lift_prod : Val :=
  .tLamV (Λₑ (Λₑ (Λₑ (λ: f g p,
    Expr.pair (("f" : Expr) (.fst "p")) (("g" : Expr) (.snd "p"))))))

def lift_prod_type : Ty :=
  .all (.all (.all (.all (.fn (.fn (.tVar 3) (.tVar 1))
    (.fn (.fn (.tVar 2) (.tVar 0)) (.fn (.prod (.tVar 3) (.tVar 2)) (.prod (.tVar 1) (.tVar 0))))))))

theorem lift_prod_typed :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) lift_prod.toExpr lift_prod_type := by solve_typing

def lift_sum : Val :=
  .tLamV (Λₑ (Λₑ (Λₑ (λ: f g s,
    matchE "s" (.bNamed "x") (.injL (("f" : Expr) "x"))
      (.bNamed "x") (.injR (("g" : Expr) "x"))))))

def lift_sum_type : Ty :=
  .all (.all (.all (.all (.fn (.fn (.tVar 3) (.tVar 1))
    (.fn (.fn (.tVar 2) (.tVar 0)) (.fn (.sum (.tVar 3) (.tVar 2)) (.sum (.tVar 1) (.tVar 0))))))))

theorem lift_sum_typed :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) lift_sum.toExpr lift_sum_type := by solve_typing

/-! ## Exercise 3 (LN 18): named types to De Bruijn -/

/-- Types with *named* type variables. -/
inductive PTy where
  | pTVar (x : String)
  | pInt
  | pBool
  | pTForall (x : String) (A : PTy)
  | pTExists (x : String) (A : PTy)
  | pFun (A B : PTy)
  deriving Repr, DecidableEq

/-- Translates a named type into De Bruijn form. `m` maps each type variable in scope to its
index; going under a binder shifts every index up and maps the bound name to `0`. -/
def debruijn (m : MapStr Nat) : PTy → Option Ty
  | .pTVar x => match get? (M := MapStr) m x with
    | none => none
    | some n => some (.tVar n)
  | .pInt => some .int
  | .pBool => some .bool
  | .pFun A B => match debruijn m A, debruijn m B with
    | some A', some B' => some (.fn A' B')
    | _, _ => none
  | .pTForall x A =>
    match debruijn (insert (M := MapStr) (Std.ExtTreeMap.map (fun _ n => n + 1) m) x 0) A with
    | none => none
    | some A' => some (.all A')
  | .pTExists x A =>
    match debruijn (insert (M := MapStr) (Std.ExtTreeMap.map (fun _ n => n + 1) m) x 0) A with
    | none => none
    | some A' => some (.exist A')

section Examples

private def emptyNames : MapStr Nat := PartialMap.empty (M := MapStr) (V := Nat)

example : debruijn emptyNames
    (.pTForall "x" (.pTForall "y" (.pFun (.pTVar "x") (.pTVar "y"))))
    = some (.all (.all (.fn (.tVar 1) (.tVar 0)))) := by rfl

example : debruijn emptyNames
    (.pTForall "x" (.pFun (.pTVar "x") (.pTForall "y" (.pTVar "y"))))
    = some (.all (.fn (.tVar 0) (.all (.tVar 0)))) := by rfl

example : debruijn emptyNames
    (.pTForall "x" (.pFun (.pTVar "x") (.pTForall "y" (.pTVar "x"))))
    = some (.all (.fn (.tVar 0) (.all (.tVar 1)))) := by rfl

end Examples

/-! ## Exercise 4: parallel substitution on types -/

namespace Exercise4

def T : Ty :=
  .all (.fn (.tVar 0) (.fn (.tVar 1) (.fn (.tVar 2)
    (.all (.fn (.tVar 0) (.fn (.tVar 2) (.tVar 1)))))))

def σ : Nat → Ty
  | 0 => .all (.fn (.tVar 0) (.fn .int (.tVar 3)))
  | 1 => .tVar 2
  | n => .tVar n

def subst_result : Ty :=
  .all (.fn (.tVar 0) (.fn (.all (.fn (.tVar 0) (.fn .int (.tVar 4))))
    (.fn (.tVar 3) (.all (.fn (.tVar 0)
      (.fn (.all (.fn (.tVar 0) (.fn .int (.tVar 5)))) (.tVar 1)))))))

example : T.substTy σ = subst_result := by rfl

end Exercise4

/-! ## Type-substitution helpers

The shift a `list_type`/`sum_type` binder introduces cancels against the type application that
eliminates it. -/

theorem Ty.subst1_fn (X Y B : Ty) : (Ty.fn X Y).subst1 B = .fn (X.subst1 B) (Y.subst1 B) := rfl

theorem Ty.subst1_tVar_zero (B : Ty) : (Ty.tVar 0).subst1 B = B := rfl

/-- Shifting twice and then substituting for index `0` leaves a single shift. -/
theorem Ty.rename_two_subst1 (A : Ty) (B : Ty) :
    (A.rename (fun n => n + 2)).subst1 B = A.rename (· + 1) := by
  rw [Ty.subst1, Ty.rename_substTy, Ty.rename_eq_substTy]

/-! ## Exercise 5 (LN 24): Church encoding of sum types -/

def sum_type (A B : Ty) : Ty :=
  .all (.fn (.fn (A.rename (· + 1)) (.tVar 0)) (.fn (.fn (B.rename (· + 1)) (.tVar 0)) (.tVar 0)))

def injl_val (v : Val) : Val := .tLamV (λ: f g, ("f" : Expr) v.toExpr)

def injl_expr (e : Expr) : Expr := let: x := e in Λₑ (λ: f g, ("f" : Expr) "x")

def injr_val (v : Val) : Val := .tLamV (λ: f g, ("g" : Expr) v.toExpr)

def injr_expr (e : Expr) : Expr := let: x := e in Λₑ (λ: f g, ("g" : Expr) "x")

/-- The eliminator. The match arms bind their payload to `x1` and `x2` respectively. -/
def match_sum (e e₁ e₂ : Expr) : Expr :=
  .app (.app (.tApp e) (.lam (.bNamed "x1") e₁)) (.lam (.bNamed "x2") e₂)

/-! ### Reduction behaviour -/

theorem match_sum_red_injl (e e₁ e₂ : Expr) (vl v' : Val) (hvl : closed [] vl.toExpr)
    (he₁ : closed ["x1"] e₁) (h : BigStep e (injl_val vl))
    (h' : BigStep (subst' (.bNamed "x1") vl.toExpr e₁) v') :
    BigStep (match_sum e e₁ e₂) v' := by
  refine .bs_app _ _ (.bNamed "g") (.app (.lam (.bNamed "x1") e₁) vl.toExpr)
    (.lamV (.bNamed "x2") e₂) v' ?_ (.bs_lam _ _) ?_
  · refine .bs_app _ _ (.bNamed "f") (.lam (.bNamed "g") (.app (.var "f") vl.toExpr))
      (.lamV (.bNamed "x1") e₁) _ (.bs_tapp _ _ _ h (.bs_lam _ _)) (.bs_lam _ _) ?_
    simp +decide only [subst', subst, Val.toExpr, subst_closed_nil hvl]
    exact .bs_lam _ _
  · simp +decide only [subst', subst, Val.toExpr, subst_closed_nil hvl,
      subst_closed_notmem (x := "g") he₁ (by simp), reduceIte]
    exact .bs_app _ _ (.bNamed "x1") e₁ vl v' (.bs_lam _ _) (big_step_of_val rfl) h'

theorem match_sum_red_injr (e e₁ e₂ : Expr) (vl v' : Val) (hvl : closed [] vl.toExpr)
    (h : BigStep e (injr_val vl)) (h' : BigStep (subst' (.bNamed "x2") vl.toExpr e₂) v') :
    BigStep (match_sum e e₁ e₂) v' := by
  refine .bs_app _ _ (.bNamed "g") (.app (.var "g") vl.toExpr)
    (.lamV (.bNamed "x2") e₂) v' ?_ (.bs_lam _ _) ?_
  · refine .bs_app _ _ (.bNamed "f") (.lam (.bNamed "g") (.app (.var "g") vl.toExpr))
      (.lamV (.bNamed "x1") e₁) _ (.bs_tapp _ _ _ h (.bs_lam _ _)) (.bs_lam _ _) ?_
    simp +decide only [subst', subst, Val.toExpr, subst_closed_nil hvl]
    exact .bs_lam _ _
  · simp +decide only [subst', subst, Val.toExpr, subst_closed_nil hvl]
    exact .bs_app _ _ (.bNamed "x2") e₂ vl v' (.bs_lam _ _) (big_step_of_val rfl) h'

theorem injl_expr_red (e : Expr) (v : Val) (h : BigStep e v) :
    BigStep (injl_expr e) (injl_val v) := by
  refine .bs_app _ _ (.bNamed "x") _ v _ (.bs_lam _ _) h ?_
  simp +decide only [subst', subst]
  exact .bs_tlam _

theorem injr_expr_red (e : Expr) (v : Val) (h : BigStep e v) :
    BigStep (injr_expr e) (injr_val v) := by
  refine .bs_app _ _ (.bNamed "x") _ v _ (.bs_lam _ _) h ?_
  simp +decide only [subst', subst]
  exact .bs_tlam _

/-! ### Typing rules -/

theorem sum_injl_typed (n : Nat) (Γ : TypingContext) (e : Expr) (A B : Ty)
    (hB : TypeWf n B) (hA : TypeWf n A) (he : SynTyped n Γ e A) :
    SynTyped n Γ (injl_expr e) (sum_type A B) := by solve_typing

theorem sum_injr_typed (n : Nat) (Γ : TypingContext) (e : Expr) (A B : Ty)
    (hB : TypeWf n B) (hA : TypeWf n A) (he : SynTyped n Γ e B) :
    SynTyped n Γ (injr_expr e) (sum_type A B) := by
  refine .typed_app n Γ _ _ B (sum_type A B) ?_ he
  refine .typed_lam n Γ "x" _ B (sum_type A B) hB ?_
  solve_typing

/-- Eliminating a `sum_type` at `C`: the shift the binder introduced cancels. -/
theorem tapp_sum_type (n : Nat) (Δ : TypingContext) (A B C : Ty) (e : Expr) (hC : TypeWf n C)
    (h : SynTyped n Δ e (sum_type A B)) :
    SynTyped n Δ (Expr.tApp e) (.fn (.fn A C) (.fn (.fn B C) C)) := by
  have htapp := SynTyped.typed_tApp n Δ e _ C hC h
  simpa only [sum_type, Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id] using htapp

theorem sum_match_typed (n : Nat) (Γ : TypingContext) (A B C : Ty) (e e₁ e₂ : Expr)
    (hA : TypeWf n A) (hB : TypeWf n B) (hC : TypeWf n C)
    (he : SynTyped n Γ e (sum_type A B))
    (h₁ : SynTyped n (insert (M := TyMapStr) Γ "x1" A) e₁ C)
    (h₂ : SynTyped n (insert (M := TyMapStr) Γ "x2" B) e₂ C) :
    SynTyped n Γ (match_sum e e₁ e₂) C := by
  refine .typed_app n Γ _ _ (.fn B C) C ?_ (.typed_lam n Γ "x2" e₂ B C hB h₂)
  exact .typed_app n Γ _ _ (.fn A C) _ (tapp_sum_type n Γ A B C e hC he)
    (.typed_lam n Γ "x1" e₁ A C hA h₁)

/-! ## Exercise 6 (LN 25): Church encoding of lists -/

def list_type (A : Ty) : Ty :=
  .all (.fn (.tVar 0) (.fn (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))) (.tVar 0)))

theorem list_type_wf (n : Nat) (A : Ty) (hA : TypeWf n A) : TypeWf n (list_type A) :=
  .all_wf (.fn_wf (.tVar_wf (by omega))
    (.fn_wf (.fn_wf (TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA)
      (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega)))) (.tVar_wf (by omega))))

/-- Eliminating a `list_type` at `C`. -/
theorem tapp_list_type (n : Nat) (Δ : TypingContext) (A C : Ty) (e : Expr) (hC : TypeWf n C)
    (h : SynTyped n Δ e (list_type A)) :
    SynTyped n Δ (Expr.tApp e) (.fn C (.fn (.fn A (.fn C C)) C)) := by
  have htapp := SynTyped.typed_tApp n Δ e _ C hC h
  simpa only [list_type, Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id] using htapp

/-- Eliminating a shifted `list_type` at the variable the shift made room for. -/
theorem tapp_list_type_shift (n : Nat) (Δ : TypingContext) (A : Ty) (e : Expr)
    (h : SynTyped (n + 1) Δ e ((list_type A).rename (· + 1))) :
    SynTyped (n + 1) Δ (Expr.tApp e)
      (.fn (.tVar 0) (.fn (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))) (.tVar 0))) := by
  have hrw : (list_type A).rename (· + 1)
      = Ty.all (.fn (.tVar 0)
          (.fn (.fn (A.rename (fun n => n + 2)) (.fn (.tVar 0) (.tVar 0))) (.tVar 0))) := by
    simp only [list_type, Ty.rename, Ty.rename_rename]
  rw [hrw] at h
  have htapp := SynTyped.typed_tApp (n + 1) Δ e _ (.tVar 0) (.tVar_wf (by omega)) h
  simpa only [Ty.subst1_fn, Ty.subst1_tVar_zero, Ty.rename_two_subst1] using htapp

def nil_val : Val := .tLamV (λ: e c, "e")

def cons_val (v₁ v₂ : Val) : Val :=
  .tLamV (λ: e c, Expr.app (Expr.app (.var "c") v₁.toExpr)
    (Expr.app (Expr.app (Expr.tApp v₂.toExpr) (.var "e")) (.var "c")))

def cons_expr (e₁ e₂ : Expr) : Expr :=
  let: p := Expr.pair e₁ e₂ in
    Λₑ (λ: e c, Expr.app (Expr.app (.var "c") (Expr.fst (.var "p")))
      (Expr.app (Expr.app (Expr.tApp (Expr.snd (.var "p"))) (.var "e")) (.var "c")))

theorem nil_typed (n : Nat) (Γ : TypingContext) (A : Ty) (hA : TypeWf n A) :
    SynTyped n Γ nil_val.toExpr (list_type A) := by solve_typing

theorem cons_typed (n : Nat) (Γ : TypingContext) (e₁ e₂ : Expr) (A : Ty) (hA : TypeWf n A)
    (h₂ : SynTyped n Γ e₂ (list_type A)) (h₁ : SynTyped n Γ e₁ A) :
    SynTyped n Γ (cons_expr e₁ e₂) (list_type A) := by
  have hAup : TypeWf (n + 1) (A.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA
  refine .typed_app n Γ _ _ (.prod A (list_type A)) (list_type A) ?_
    (.typed_pair n Γ e₁ e₂ A (list_type A) h₁ h₂)
  refine .typed_lam n Γ "p" _ (.prod A (list_type A)) (list_type A)
    (.prod_wf hA (list_type_wf n A hA)) ?_
  refine .typed_tLam n _ _ _ ?_
  rw [shiftCtx_insert]
  refine .typed_lam (n + 1) _ "e" _ (.tVar 0) _ (.tVar_wf (by omega)) ?_
  refine .typed_lam (n + 1) _ "c" _ (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))) (.tVar 0)
    (.fn_wf hAup (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega)))) ?_
  refine .typed_app (n + 1) _ _ _ (.tVar 0) (.tVar 0) ?_ ?_
  · refine .typed_app (n + 1) _ _ _ (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))
      (.typed_var _ _ "c" _ lookup_here) ?_
    exact .typed_fst (n + 1) _ _ (A.rename (· + 1)) ((list_type A).rename (· + 1))
      (.typed_var _ _ "p" _
        (lookup_there (show "c" ≠ "p" by decide)
          (lookup_there (show "e" ≠ "p" by decide) lookup_here)))
  · refine .typed_app (n + 1) _ _ _ (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))) (.tVar 0)
      ?_ (.typed_var _ _ "c" _ lookup_here)
    refine .typed_app (n + 1) _ _ _ (.tVar 0) _ ?_
      (.typed_var _ _ "e" _ (lookup_there (show "c" ≠ "e" by decide) lookup_here))
    refine tapp_list_type_shift n _ A _ ?_
    exact .typed_snd (n + 1) _ _ (A.rename (· + 1)) ((list_type A).rename (· + 1))
      (.typed_var _ _ "p" _
        (lookup_there (show "c" ≠ "p" by decide)
          (lookup_there (show "e" ≠ "p" by decide) lookup_here)))

/-- `head` returns the first element of a list, or `()` when the list is empty. -/
def head : Val :=
  λᵥ: l, Expr.app (Expr.app (Expr.tApp (.var "l")) (Expr.injR (.lit .litUnit)))
    (Expr.lam (.bNamed "h") (Expr.lam .bAnon (.injL (.var "h"))))

theorem head_typed (n : Nat) (Γ : TypingContext) (A : Ty) (hA : TypeWf n A) :
    SynTyped n Γ head.toExpr (.fn (list_type A) (.sum A .unit)) := by
  refine .typed_lam n Γ "l" _ (list_type A) (.sum A .unit) (list_type_wf n A hA) ?_
  refine .typed_app n _ _ _ (.fn A (.fn (.sum A .unit) (.sum A .unit))) (.sum A .unit) ?_ ?_
  · refine .typed_app n _ _ _ (.sum A .unit) _ ?_
      (.typed_injR n _ _ A .unit hA (.typed_lit_unit n _))
    exact tapp_list_type n _ A (.sum A .unit) _ (.sum_wf hA .unit_wf)
      (.typed_var _ _ "l" _ lookup_here)
  · refine .typed_lam n _ "h" _ A _ hA ?_
    refine .typed_lam_anon n _ _ (.sum A .unit) (.sum A .unit) (.sum_wf hA .unit_wf) ?_
    exact .typed_injL n _ _ A .unit .unit_wf (.typed_var _ _ "h" _ lookup_here)

/-- `split` peels off the head of a list, pairing it with the tail. -/
def split : Val :=
  λᵥ: l, Expr.app
    (Expr.app (Expr.tApp (.var "l"))
      (Expr.pair (Expr.injR (.lit .litUnit)) nil_val.toExpr))
    (Expr.lam (.bNamed "h") (Expr.lam (.bNamed "r")
      (matchE (Expr.fst (.var "r")) (.bNamed "h'")
        (Expr.pair (Expr.injL (.var "h"))
          (let: r' := Expr.snd (.var "r") in cons_expr (.var "h'") (.var "r'")))
        .bAnon (Expr.pair (Expr.injL (.var "h")) (Expr.snd (.var "r"))))))

def tail : Val := λᵥ: l, Expr.snd (Expr.app split.toExpr (.var "l"))

/-! ## Exercises 7–8 (LN 27–28): free theorems

Each of these instantiates the universally quantified type variable with a semantic type chosen
to pin down the result — Rocq's `specialize_sem_type` tactic, written out. -/

/-- The singleton semantic type `{v}`. -/
def sing (v : Val) (h : closed [] v.toExpr) : SemType where
  car w := w = v
  closed_val _ hw := hw ▸ h

/-- Every closed `f : ∀ α β. α → β → α × β` pairs its two arguments. -/
theorem free_thm_1 (f : Val)
    (hty : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) f.toExpr
      (.all (.all (.fn (.tVar 1) (.fn (.tVar 0) (.prod (.tVar 1) (.tVar 0)))))))
    (v₁ v₂ : Val) (hcl₁ : closed [] v₁.toExpr) (hcl₂ : closed [] v₂.toExpr) :
    BigStep (.app (.app (.tApp (.tApp f.toExpr)) v₁.toExpr) v₂.toExpr) (.pairV v₁ v₂) := by
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  obtain rfl := big_step_val hb
  simp only [valRel] at hv
  obtain ⟨e₀, rfl, _, hall₀⟩ := hv
  obtain ⟨w₁, hbw₁, hw₁⟩ := hall₀ (sing v₁ hcl₁)
  obtain ⟨e₁, rfl, _, hall₁⟩ := hw₁
  obtain ⟨w₂, hbw₂, hw₂⟩ := hall₁ (sing v₂ hcl₂)
  obtain ⟨x, e', rfl, _, hbody⟩ := hw₂
  obtain ⟨u, hbu, hu⟩ := hbody v₁ (show v₁ = v₁ from rfl)
  obtain ⟨y, e'', rfl, _, hbody'⟩ := hu
  obtain ⟨r, hbr, hr⟩ := hbody' v₂ (show v₂ = v₂ from rfl)
  obtain ⟨a, b, rfl, ha, hb'⟩ := hr
  rw [show a = v₁ from ha, show b = v₂ from hb'] at hbr
  refine .bs_app _ _ y e'' v₂ _ ?_ (big_step_of_val rfl) hbr
  refine .bs_app _ _ x e' v₁ _ ?_ (big_step_of_val rfl) hbu
  exact .bs_tapp _ _ _ (.bs_tapp _ _ _ (.bs_tlam _) hbw₁) hbw₂

/-- Every closed `f : ∀ α β. α × β → α` is the first projection. -/
theorem free_thm_2 (f : Val)
    (hty : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) f.toExpr
      (.all (.all (.fn (.prod (.tVar 1) (.tVar 0)) (.tVar 1)))))
    (v₁ v₂ : Val) (hcl₁ : closed [] v₁.toExpr) (hcl₂ : closed [] v₂.toExpr) :
    BigStep (.app (.tApp (.tApp f.toExpr)) (.pair v₁.toExpr v₂.toExpr)) v₁ := by
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  obtain rfl := big_step_val hb
  simp only [valRel] at hv
  obtain ⟨e₀, rfl, _, hall₀⟩ := hv
  obtain ⟨w₁, hbw₁, hw₁⟩ := hall₀ (sing v₁ hcl₁)
  obtain ⟨e₁, rfl, _, hall₁⟩ := hw₁
  obtain ⟨w₂, hbw₂, hw₂⟩ := hall₁ (sing v₂ hcl₂)
  obtain ⟨x, e', rfl, _, hbody⟩ := hw₂
  obtain ⟨u, hbu, hu⟩ := hbody (.pairV v₁ v₂) ⟨v₁, v₂, rfl, rfl, rfl⟩
  rw [show u = v₁ from hu] at hbu
  refine .bs_app _ _ x e' (.pairV v₁ v₂) _ ?_ ?_ hbu
  · exact .bs_tapp _ _ _ (.bs_tapp _ _ _ (.bs_tlam _) hbw₁) hbw₂
  · exact .bs_pair _ _ _ _ (big_step_of_val rfl) (big_step_of_val rfl)

/-- There is no closed `f : ∀ α β. α → β`. -/
theorem free_thm_3 (f : Val)
    (hty : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) f.toExpr
      (.all (.all (.fn (.tVar 1) (.tVar 0))))) : False := by
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  obtain rfl := big_step_val hb
  simp only [valRel] at hv
  obtain ⟨e₀, rfl, _, hall₀⟩ := hv
  obtain ⟨w₁, _, hw₁⟩ := hall₀ (sing (.litV (.litInt 0)) rfl)
  obtain ⟨e₁, rfl, _, hall₁⟩ := hw₁
  -- The second type variable is instantiated with the *empty* semantic type.
  obtain ⟨w₂, _, hw₂⟩ := hall₁ ⟨fun _ => False, fun _ h => h.elim⟩
  obtain ⟨x, e', rfl, _, hbody⟩ := hw₂
  obtain ⟨u, _, hu⟩ := hbody (.litV (.litInt 0)) (show _ = _ from rfl)
  exact hu

/-- Every closed `f : ∀ α. α → α → α` returns one of its two arguments. -/
theorem free_theorem_either (f : Val)
    (hty : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) f.toExpr
      (.all (.fn (.tVar 0) (.fn (.tVar 0) (.tVar 0)))))
    (v₁ v₂ : Val) (hcl₁ : closed [] v₁.toExpr) (hcl₂ : closed [] v₂.toExpr) :
    BigStep (.app (.app (.tApp f.toExpr) v₁.toExpr) v₂.toExpr) v₁ ∨
    BigStep (.app (.app (.tApp f.toExpr) v₁.toExpr) v₂.toExpr) v₂ := by
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  obtain rfl := big_step_val hb
  simp only [valRel] at hv
  obtain ⟨e₀, rfl, _, hall₀⟩ := hv
  let τ : SemType := ⟨fun w => w = v₁ ∨ w = v₂, fun w h => by
    rcases h with rfl | rfl
    · exact hcl₁
    · exact hcl₂⟩
  obtain ⟨w, hbw, hw⟩ := hall₀ τ
  obtain ⟨x, e', rfl, _, hbody⟩ := hw
  obtain ⟨u, hbu, hu⟩ := hbody v₁ (show τ.car v₁ from Or.inl rfl)
  obtain ⟨y, e'', rfl, _, hbody'⟩ := hu
  obtain ⟨r, hbr, hr⟩ := hbody' v₂ (show τ.car v₂ from Or.inr rfl)
  have hstep : BigStep (.app (.app (.tApp (Expr.tLam e₀)) v₁.toExpr) v₂.toExpr) r :=
    .bs_app _ _ y e'' v₂ _
      (.bs_app _ _ x e' v₁ _ (.bs_tapp _ _ _ (.bs_tlam _) hbw) (big_step_of_val rfl) hbu)
      (big_step_of_val rfl) hbr
  rcases (hr : r = v₁ ∨ r = v₂) with rfl | rfl
  · exact Or.inl hstep
  · exact Or.inr hstep

/-! ## Exercise 9 (LN 29): free theorems III -/

/-- A closed `f : ∀ α. (A₁ → A₂ → α) → α` can only produce its result by calling its argument. -/
theorem free_theorems_magic (A A₁ A₂ : Ty) (f g : Val)
    (_hwfA : TypeWf 0 A) (hwfA₁ : TypeWf 0 A₁) (hwfA₂ : TypeWf 0 A₂)
    (hclf : closed [] f.toExpr) (hclg : closed [] g.toExpr)
    (htyf : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) f.toExpr
      (.all (.fn (.fn A₁ (.fn A₂ (.tVar 0))) (.tVar 0))))
    (htyg : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) g.toExpr
      (.fn A₁ (.fn A₂ A)))
    (v : Val) (hbv : BigStep (.app (.tApp f.toExpr) g.toExpr) v) :
    ∃ v₁ v₂ : Val, BigStep (.app (.app g.toExpr v₁.toExpr) v₂.toExpr) v := by
  obtain ⟨_, hsemf⟩ := sem_soundness htyf
  obtain ⟨_, hsemg⟩ := sem_soundness htyg
  obtain ⟨vf, hbf, hvf⟩ := hsemf (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  obtain ⟨vg, hbg, hvg⟩ := hsemg (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hbf hbg
  obtain rfl := big_step_val hbf
  obtain rfl := big_step_val hbg
  simp only [valRel] at hvf hvg
  obtain ⟨xg, eg, rfl, hclg₀, hbodyg⟩ := hvg
  obtain ⟨ef, rfl, _, hallf⟩ := hvf
  -- The chosen semantic type: exactly the values `g` can produce.
  let τ : SemType :=
    ⟨fun w => ∃ v₁ v₂ : Val, closed [] v₁.toExpr ∧ closed [] v₂.toExpr ∧
        BigStep (.app (.app (Val.lamV xg eg).toExpr v₁.toExpr) v₂.toExpr) w,
     fun w hw => by
       obtain ⟨v₁, v₂, hc₁, hc₂, hb⟩ := hw
       refine big_step_preserve_closed ?_ hb
       simp only [closed, Expr.isClosed, Bool.and_eq_true]
       exact ⟨⟨hclg, hc₁⟩, hc₂⟩⟩
  obtain ⟨wf, hbwf, hwf⟩ := hallf τ
  obtain ⟨x, ef', rfl, _, hbodyf⟩ := hwf
  obtain ⟨r, hbr, hr⟩ := hbodyf (.lamV xg eg) (by
    refine ⟨xg, eg, rfl, hclg₀, fun v₁ hv₁ => ?_⟩
    have hv₁' : valRel δ_any A₁ v₁ := by
      rw [sem_val_rel_cons A₁ δ_any v₁ τ, type_wf_closed_rename A₁ _ hwfA₁]
      exact hv₁
    obtain ⟨u, hbu, hu⟩ := hbodyg v₁ hv₁'
    obtain ⟨xg', eg', rfl, hclg₁, hbodyg'⟩ := hu
    refine ⟨_, hbu, xg', eg', rfl, hclg₁, fun v₂ hv₂ => ?_⟩
    have hv₂' : valRel δ_any A₂ v₂ := by
      rw [sem_val_rel_cons A₂ δ_any v₂ τ, type_wf_closed_rename A₂ _ hwfA₂]
      exact hv₂
    obtain ⟨w, hbw, _⟩ := hbodyg' v₂ hv₂'
    refine ⟨w, hbw, v₁, v₂, val_rel_closed v₁ δ_any A₁ hv₁',
      val_rel_closed v₂ δ_any A₂ hv₂', ?_⟩
    exact .bs_app _ _ xg' eg' v₂ w
      (.bs_app _ _ xg eg v₁ _ (.bs_lam _ _) (big_step_of_val rfl) hbu)
      (big_step_of_val rfl) hbw)
  obtain ⟨v₁, v₂, _, _, hgcall⟩ := hr
  refine ⟨v₁, v₂, ?_⟩
  have hrv : r = v :=
    SystemF.Binary.big_step_det (.bs_app _ _ x ef' (.lamV xg eg) r
      (.bs_tapp _ _ _ (.bs_tlam _) hbwf) (big_step_of_val rfl) hbr) hbv
  exact hrv ▸ hgcall

end SystemF
