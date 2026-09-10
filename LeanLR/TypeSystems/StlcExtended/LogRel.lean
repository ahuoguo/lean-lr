import LeanLR.TypeSystems.StlcExtended.Lang
import LeanLR.TypeSystems.StlcExtended.Maps
import LeanLR.TypeSystems.StlcExtended.BigStep
import LeanLR.TypeSystems.StlcExtended.ParallelSubst
import LeanLR.TypeSystems.StlcExtended.Types

/-!
# Extended STLC: unary logical relation

A unary logical relation for the extended STLC, proving that every well-typed closed term
terminates. There is no step index: the relation recurses on the *type*.

Rocq defines `𝒱` and `ℰ` by mutual well-founded recursion on `mut_measure`. Here the expression
relation is inlined into the one place `valRel` uses it (the function case) and re-exposed
afterwards as `exprRel`, which makes `valRel` an ordinary structural recursion on the type.
`valRel_fn` recovers the mutual-looking equation.
-/

open Iris.Std

namespace StlcExtended

/-! ## The relation -/

/-- `valRel A v` says the value `v` belongs to type `A`. -/
def valRel : Ty → Val → Prop
  | .int, .litIntV _ => True
  | .int, _ => False
  | .fn A B, .lamV x e =>
      closed (x :b: []) e ∧
      ∀ v', valRel A v' → ∃ w, (subst' x v'.toExpr e ⇓ w) ∧ valRel B w
  | .fn _ _, _ => False
  | .prod A B, .pairV v₁ v₂ => valRel A v₁ ∧ valRel B v₂
  | .prod _ _, _ => False
  | .sum A _, .injLV v' => valRel A v'
  | .sum _ B, .injRV v' => valRel B v'
  | .sum _ _, _ => False

/-- `exprRel A e` says `e` evaluates to a value of type `A`. -/
def exprRel (A : Ty) (e : Expr) : Prop := ∃ v, (e ⇓ v) ∧ valRel A v

@[inherit_doc] notation:50 "𝒱⟦" A "⟧" v:50 => valRel A v
@[inherit_doc] notation:50 "ℰ⟦" A "⟧" e:50 => exprRel A e

/-- The function case of `valRel`, written with `exprRel`: this is the equation Rocq's mutual
`type_interp` states directly. -/
theorem valRel_fn {A B : Ty} {x : Binder} {e : Expr} :
    𝒱⟦A ⇒ B⟧ (.lamV x e) ↔
      (closed (x :b: []) e ∧ ∀ v', 𝒱⟦A⟧ v' → ℰ⟦B⟧ (subst' x v'.toExpr e)) := Iff.rfl

/-! ## Semantic typing of contexts -/

/-- `𝒢⟦Γ⟧θ` says `θ` substitutes, for every variable `Γ` types, a closed value in the relation at
that type. -/
inductive semCtxRel : TypingContext → SubstMap → Prop where
  | empty : semCtxRel TypingContext.empty (PartialMap.empty (M := MapStr) (V := Expr))
  | insert (Γ : TypingContext) (θ : SubstMap) (v : Val) (x : String) (A : Ty) :
      valRel A v →
      semCtxRel Γ θ →
      semCtxRel (Iris.Std.insert (M := MapStr) Γ x A)
        (Iris.Std.insert (M := MapStr) θ x v.toExpr)

@[inherit_doc] notation:50 "𝒢⟦" Γ "⟧" θ:50 => semCtxRel Γ θ

/-- Semantic typing: `e` is closed by `Γ` and lands in the expression relation under every
substitution satisfying `Γ`. -/
def semTyped (Γ : TypingContext) (e : Expr) (A : Ty) : Prop :=
  closed Γ.domList e ∧ ∀ θ : SubstMap, 𝒢⟦Γ⟧ θ → ℰ⟦A⟧ (substMap θ e)

@[inherit_doc] notation:75 Γ:75 " ⊨ " e:74 " : " A:74 => semTyped Γ e A

/-! ## Basic properties -/

theorem sem_expr_rel_of_val {A : Ty} {v : Val} (h : ℰ⟦A⟧ v.toExpr) : 𝒱⟦A⟧ v := by
  obtain ⟨v', hbs, hv⟩ := h
  rwa [big_step_val hbs] at hv

theorem val_inclusion {A : Ty} {v : Val} (h : 𝒱⟦A⟧ v) : ℰ⟦A⟧ v.toExpr :=
  ⟨v, big_step_of_val v, h⟩

theorem val_rel_closed {A : Ty} {v : Val} (h : 𝒱⟦A⟧ v) : closed [] v.toExpr := by
  induction A generalizing v with
  | int => cases v <;> first | rfl | simp only [valRel] at h
  | fn A B _ _ =>
    cases v <;> simp only [valRel] at h
    simpa [closed, Val.toExpr, Expr.isClosed] using h.1
  | prod A B ihA ihB =>
    cases v <;> simp only [valRel] at h
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ihA h.1, ihB h.2⟩
  | sum A B ihA ihB =>
    cases v <;> simp only [valRel] at h
    · have hcl := ihA h
      simpa [closed, Val.toExpr, Expr.isClosed] using hcl
    · have hcl := ihB h
      simpa [closed, Val.toExpr, Expr.isClosed] using hcl

/-! ## Properties of the context relation -/

theorem semCtxRel_closed {Γ : TypingContext} {θ : SubstMap} (h : 𝒢⟦Γ⟧ θ) :
    substIsClosed [] θ := by
  induction h with
  | empty =>
    intro x e hx
    have hemp : get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) x = none :=
      LawfulPartialMap.get?_empty (M := MapStr) x
    rw [hemp] at hx
    exact absurd hx (by simp)
  | insert Γ' θ' v x A hv _ ih =>
    intro y e hy
    rw [get?_insert] at hy
    by_cases hxy : x = y
    · rw [if_pos hxy] at hy
      cases hy
      exact val_rel_closed hv
    · rw [if_neg hxy] at hy
      exact ih y e hy

/-- Inversion for `semCtxRel`: every variable the context types is substituted by a related
value. -/
theorem semCtxRel_vals {Γ : TypingContext} {θ : SubstMap} {x : String} {A : Ty}
    (hctx : 𝒢⟦Γ⟧ θ) (hlook : get? (M := MapStr) Γ x = some A) :
    ∃ v, get? (M := MapStr) θ x = some v.toExpr ∧ 𝒱⟦A⟧ v := by
  induction hctx with
  | empty => rw [TypingContext.get?_empty] at hlook; exact absurd hlook (by simp)
  | insert Γ' θ' v y B hv _ ih =>
    rw [get?_insert] at hlook
    by_cases hxy : y = x
    · rw [if_pos hxy] at hlook
      cases hlook
      exact ⟨v, by rw [get?_insert, if_pos hxy], hv⟩
    · rw [if_neg hxy] at hlook
      obtain ⟨w, hw, hvw⟩ := ih hlook
      exact ⟨w, by rw [get?_insert, if_neg hxy]; exact hw, hvw⟩

/-- The substitution covers everything the context types. -/
theorem semCtxRel_domList {Γ : TypingContext} {θ : SubstMap} {x : String}
    (hctx : 𝒢⟦Γ⟧ θ) (hx : x ∈ Γ.domList) : x ∈ θ.domList := by
  obtain ⟨A, hA⟩ := mem_domList_iff_lookup.mp hx
  obtain ⟨v, hv, _⟩ := semCtxRel_vals hctx hA
  exact mem_domList_iff_lookup.mpr ⟨_, hv⟩

/-! ## Compatibility lemmas -/

theorem compat_int (Γ : TypingContext) (z : Int) : Γ ⊨ .litInt z : .int :=
  ⟨rfl, fun _ _ => ⟨.litIntV z, .bs_lit z, trivial⟩⟩

theorem compat_var (Γ : TypingContext) (x : String) (A : Ty)
    (hlook : get? (M := MapStr) Γ x = some A) : Γ ⊨ .var x : A := by
  refine ⟨?_, fun θ hctx => ?_⟩
  · simpa [closed, Expr.isClosed] using mem_domList_iff_lookup.mpr ⟨A, hlook⟩
  · obtain ⟨v, hθ, hv⟩ := semCtxRel_vals hctx hlook
    rw [substMap, hθ]
    exact val_inclusion hv

theorem compat_app (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : Γ ⊨ e₁ : (A ⇒ B)) (h₂ : Γ ⊨ e₂ : A) : Γ ⊨ .app e₁ e₂ : B := by
  obtain ⟨hcl₁, hsem₁⟩ := h₁
  obtain ⟨hcl₂, hsem₂⟩ := h₂
  refine ⟨by simp [closed, Expr.isClosed, hcl₁, hcl₂], fun θ hctx => ?_⟩
  obtain ⟨v₁, hbs₁, hv₁⟩ := hsem₁ θ hctx
  cases v₁ <;> simp only [valRel] at hv₁
  obtain ⟨hcl, hbody⟩ := hv₁
  obtain ⟨v₂, hbs₂, hv₂⟩ := hsem₂ θ hctx
  obtain ⟨v, hbs, hv⟩ := hbody v₂ hv₂
  exact ⟨v, .bs_app hbs₁ hbs₂ hbs, hv⟩

/-- Technical helper for `compat_lam`: closing off the body really does yield a closed λ. -/
theorem lam_closed (Γ : TypingContext) (θ : SubstMap) (x : String) (A : Ty) (e : Expr)
    (hcl : closed (Iris.Std.insert (M := MapStr) Γ x A).domList e) (hctx : 𝒢⟦Γ⟧ θ) :
    closed [] (Expr.lam (.bNamed x) (substMap (delete (M := MapStr) θ x) e)) := by
  simp only [closed, Expr.isClosed, Binder.cons]
  refine substMap_closed (X := [x]) ?_ (substIsClosed_delete_weaken (semCtxRel_closed hctx))
  refine closed_weaken hcl fun y hy => ?_
  rcases mem_domList_insert.mp hy with rfl | hy
  · exact List.mem_append.mpr (Or.inl (.head _))
  · by_cases hyx : y = x
    · exact List.mem_append.mpr (Or.inl (by simp [hyx]))
    · refine List.mem_append.mpr (Or.inr ?_)
      obtain ⟨e', he'⟩ := mem_domList_iff_lookup.mp (semCtxRel_domList hctx hy)
      exact mem_domList_iff_lookup.mpr
        ⟨e', by rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) (fun h => hyx h.symm)]⟩

theorem compat_lam (Γ : TypingContext) (x : String) (e : Expr) (A B : Ty)
    (h : Iris.Std.insert (M := MapStr) Γ x A ⊨ e : B) : Γ ⊨ .lam (.bNamed x) e : (A ⇒ B) := by
  obtain ⟨hbodycl, hbody⟩ := h
  refine ⟨?_, fun θ hctx => ?_⟩
  · simp only [closed, Expr.isClosed, Binder.cons]
    refine closed_weaken hbodycl fun y hy => ?_
    rcases mem_domList_insert.mp hy with rfl | hy
    · exact .head _
    · exact .tail _ hy
  · rw [substMap]
    refine ⟨.lamV (.bNamed x) (substMap (binderDelete (.bNamed x) θ) e), .bs_lam _ _, ?_⟩
    rw [valRel_fn]
    refine ⟨lam_closed Γ θ x A e hbodycl hctx, fun v' hv' => ?_⟩
    rw [subst'_substMap (.bNamed x) v'.toExpr θ e (semCtxRel_closed hctx)]
    exact hbody _ (.insert Γ θ v' x A hv' hctx)

theorem compat_lam_anon (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : Γ ⊨ e : B) : Γ ⊨ .lam .bAnon e : (A ⇒ B) := by
  obtain ⟨hbodycl, hbody⟩ := h
  refine ⟨hbodycl, fun θ hctx => ?_⟩
  rw [substMap]
  refine ⟨.lamV .bAnon (substMap (binderDelete .bAnon θ) e), .bs_lam _ _, ?_⟩
  rw [valRel_fn]
  refine ⟨?_, fun v' hv' => ?_⟩
  · simp only [closed, Binder.cons, binderDelete]
    refine substMap_closed (X := []) ?_ (semCtxRel_closed hctx)
    refine closed_weaken hbodycl fun y hy => ?_
    exact List.mem_append.mpr (Or.inr (semCtxRel_domList hctx hy))
  · rw [subst'_substMap .bAnon v'.toExpr θ e (semCtxRel_closed hctx)]
    exact hbody θ hctx

theorem compat_add (Γ : TypingContext) (e₁ e₂ : Expr)
    (h₁ : Γ ⊨ e₁ : .int) (h₂ : Γ ⊨ e₂ : .int) : Γ ⊨ .plus e₁ e₂ : .int := by
  obtain ⟨hcl₁, hsem₁⟩ := h₁
  obtain ⟨hcl₂, hsem₂⟩ := h₂
  refine ⟨by simp [closed, Expr.isClosed, hcl₁, hcl₂], fun θ hctx => ?_⟩
  obtain ⟨v₁, hbs₁, hv₁⟩ := hsem₁ θ hctx
  obtain ⟨v₂, hbs₂, hv₂⟩ := hsem₂ θ hctx
  cases v₁ <;> simp only [valRel] at hv₁
  cases v₂ <;> simp only [valRel] at hv₂
  exact ⟨.litIntV _, .bs_add hbs₁ hbs₂, trivial⟩

theorem compat_pair (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : Γ ⊨ e₁ : A) (h₂ : Γ ⊨ e₂ : B) : Γ ⊨ .pair e₁ e₂ : (A ×ₜ B) := by
  obtain ⟨hcl₁, hsem₁⟩ := h₁
  obtain ⟨hcl₂, hsem₂⟩ := h₂
  refine ⟨by simp [closed, Expr.isClosed, hcl₁, hcl₂], fun θ hctx => ?_⟩
  obtain ⟨v₁, hbs₁, hv₁⟩ := hsem₁ θ hctx
  obtain ⟨v₂, hbs₂, hv₂⟩ := hsem₂ θ hctx
  exact ⟨.pairV v₁ v₂, .bs_pair hbs₁ hbs₂, ⟨hv₁, hv₂⟩⟩

theorem compat_fst (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : Γ ⊨ e : (A ×ₜ B)) : Γ ⊨ .fst e : A := by
  obtain ⟨hcl, hsem⟩ := h
  refine ⟨hcl, fun θ hctx => ?_⟩
  obtain ⟨v, hbs, hv⟩ := hsem θ hctx
  cases v <;> simp only [valRel] at hv
  exact ⟨_, .bs_fst hbs, hv.1⟩

theorem compat_snd (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : Γ ⊨ e : (A ×ₜ B)) : Γ ⊨ .snd e : B := by
  obtain ⟨hcl, hsem⟩ := h
  refine ⟨hcl, fun θ hctx => ?_⟩
  obtain ⟨v, hbs, hv⟩ := hsem θ hctx
  cases v <;> simp only [valRel] at hv
  exact ⟨_, .bs_snd hbs, hv.2⟩

theorem compat_injl (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : Γ ⊨ e : A) : Γ ⊨ .injL e : (A +ₜ B) := by
  obtain ⟨hcl, hsem⟩ := h
  refine ⟨hcl, fun θ hctx => ?_⟩
  obtain ⟨v, hbs, hv⟩ := hsem θ hctx
  exact ⟨.injLV v, .bs_injl hbs, hv⟩

theorem compat_injr (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : Γ ⊨ e : B) : Γ ⊨ .injR e : (A +ₜ B) := by
  obtain ⟨hcl, hsem⟩ := h
  refine ⟨hcl, fun θ hctx => ?_⟩
  obtain ⟨v, hbs, hv⟩ := hsem θ hctx
  exact ⟨.injRV v, .bs_injr hbs, hv⟩

theorem compat_case (Γ : TypingContext) (e e₁ e₂ : Expr) (A B C : Ty)
    (h : Γ ⊨ e : (B +ₜ C)) (h₁ : Γ ⊨ e₁ : (B ⇒ A)) (h₂ : Γ ⊨ e₂ : (C ⇒ A)) :
    Γ ⊨ .case e e₁ e₂ : A := by
  obtain ⟨hcl, hsem⟩ := h
  obtain ⟨hcl₁, hsem₁⟩ := h₁
  obtain ⟨hcl₂, hsem₂⟩ := h₂
  refine ⟨by simp [closed, Expr.isClosed, hcl, hcl₁, hcl₂], fun θ hctx => ?_⟩
  obtain ⟨v, hbs, hv⟩ := hsem θ hctx
  cases v <;> simp only [valRel] at hv
  · obtain ⟨w, hbsw, hw⟩ := hsem₁ θ hctx
    cases w <;> simp only [valRel] at hw
    obtain ⟨u, hbsu, hu⟩ := hw.2 _ hv
    exact ⟨u, .bs_casel hbs (.bs_app hbsw (big_step_of_val _) hbsu), hu⟩
  · obtain ⟨w, hbsw, hw⟩ := hsem₂ θ hctx
    cases w <;> simp only [valRel] at hw
    obtain ⟨u, hbsu, hu⟩ := hw.2 _ hv
    exact ⟨u, .bs_caser hbs (.bs_app hbsw (big_step_of_val _) hbsu), hu⟩

/-! ## Soundness -/

/-- The fundamental theorem: every syntactically typed term is semantically typed. -/
theorem sem_soundness {Γ : TypingContext} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) : Γ ⊨ e : A := by
  induction h with
  | typed_var x hlook => exact compat_var _ x _ hlook
  | typed_lam x _ ih => exact compat_lam _ x _ _ _ ih
  | typed_lam_anon _ ih => exact compat_lam_anon _ _ _ _ ih
  | typed_int z => exact compat_int _ z
  | typed_app _ _ ih₁ ih₂ => exact compat_app _ _ _ _ _ ih₁ ih₂
  | typed_add _ _ ih₁ ih₂ => exact compat_add _ _ _ ih₁ ih₂
  | typed_pair _ _ ih₁ ih₂ => exact compat_pair _ _ _ _ _ ih₁ ih₂
  | typed_fst _ ih => exact compat_fst _ _ _ _ ih
  | typed_snd _ ih => exact compat_snd _ _ _ _ ih
  | typed_injl _ ih => exact compat_injl _ _ _ _ ih
  | typed_injr _ ih => exact compat_injr _ _ _ _ ih
  | typed_case _ _ _ ih₀ ih₁ ih₂ => exact compat_case _ _ _ _ _ _ _ ih₀ ih₁ ih₂

/-- Every closed well-typed term terminates. -/
theorem termination {e : Expr} {A : Ty} (h : TypingContext.empty ⊢ e : A) : terminates e := by
  obtain ⟨_, hsem⟩ := sem_soundness h
  have hres := hsem (PartialMap.empty (M := MapStr) (V := Expr)) .empty
  rw [substMap_empty] at hres
  obtain ⟨v, hbs, _⟩ := hres
  exact ⟨v, hbs⟩

end StlcExtended
