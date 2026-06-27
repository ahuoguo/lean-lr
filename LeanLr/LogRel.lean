import LeanLr.Lang
import LeanLr.Types
import LeanLr.Operational
import LeanLr.Notation
import LeanLr.ParallelSubst

import Iris.Std.PartialMap
import Iris.Std.GenSets
import Iris.Std.GenSetsInstances
import Iris.Std.HeapInstances

open Iris.Std

namespace STLC

-- Value relation: 𝒱⟦τ⟧
-- Expression relation: ℰ⟦τ⟧
mutual
  def valRel (τ : Ty) (v : Val) : Prop :=
    match τ, v with
    | Ty.int, Val.litIntV _ => True
    | Ty.int, _ => False
    | Ty.fun A B, Val.lamV x e =>
        Expr.closed (x :b: []) e ∧
        ∀ v', valRel A v' → exprRel B (subst' x v'.toExpr e)
    | Ty.fun _ _, _ => False

  def exprRel (τ : Ty) (e : Expr) : Prop :=
    ∃ (w : Val), (e ⇓ w) ∧ (valRel τ w)
end

notation:50 "𝒱⟦" τ "⟧" v:50 => valRel τ v
notation:50 "ℰ⟦" τ "⟧" e:50 => exprRel τ e

inductive semContextRel : Context → Subst → Prop where
  | semContextRel_empty :
      semContextRel Context.empty Subst.empty
  | semContextRel_insert Γ σ v x A :
      𝒱⟦A⟧ v →
      semContextRel Γ σ →
      semContextRel (Γ.insert x A) (σ.insert x v.toExpr)

notation:50 "𝒢⟦" Γ "⟧" σ:50 => semContextRel Γ σ

def semTyped (Γ : Context) (e : Expr) (τ : Ty) : Prop :=
  Expr.closed Γ.domList e ∧
  ∀ σ: Subst, 𝒢⟦Γ⟧ σ → ℰ⟦τ⟧ (substMap σ e)

notation:75 Γ:75 " ⊨ " e:74 " : " τ:74 => semTyped Γ e τ

-- Value inclusion
theorem val_inclusion {τ : Ty} {v : Val} :
    𝒱⟦τ⟧ v → ℰ⟦τ⟧ v.toExpr := by
  intro hv
  unfold exprRel
  exact ⟨v, val_evals_to_self v, hv⟩

-- Values in the value relation are closed
theorem val_rel_closed {A : Ty} {v : Val} :
    𝒱⟦A⟧ v → (v.toExpr).closed [] := by
  cases A with
  | int =>
    unfold valRel
    cases v with
    | litIntV _ => simp [Val.toExpr, Expr.closed]
    | lamV _ _ => intro h; exact h.elim
  | «fun» A B =>
    unfold valRel
    cases v with
    | litIntV _ => intro h; exact h.elim
    | lamV x e =>
      intro ⟨hcl, _⟩
      simp [Val.toExpr, Expr.closed]
      exact hcl

-- Semantic contexts are closed
theorem semContextRel_closed {Γ : Context} {θ : Subst} :
    𝒢⟦Γ⟧ θ → θ.closed [] := by
  intro hctx
  induction hctx with
  | semContextRel_empty =>
    intro x e hlookup
    simp only [Subst.empty, Subst.lookup] at hlookup
    change (none = some _) at hlookup
    contradiction
  | semContextRel_insert Γ σ v x A hv _ ih =>
    intro y e hlookup
    simp only [Subst.insert, Subst.lookup] at hlookup
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hlookup
      injection hlookup with heq
      rw [← heq]
      exact val_rel_closed hv
    · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hlookup
      exact ih y e hlookup

-- Extract value from semantic context relation
theorem semCtxRelVal {Γ : Context} {σ : Subst} {x : String} {A : Ty} :
    𝒢⟦Γ⟧ σ → Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v.toExpr ∧ 𝒱⟦A⟧ v := by
  intro hctx hlookup
  induction hctx with
  | semContextRel_empty =>
    simp only [Context.empty, Context.lookup] at hlookup
    change (none = some _) at hlookup
    contradiction
  | semContextRel_insert Γ' σ' v' y B hv' _ ih =>
    simp only [Context.insert, Context.lookup] at hlookup
    by_cases hxy : y = x
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hlookup
      injection hlookup with heq
      exact ⟨v', by
        simp only [Subst.insert, Subst.lookup]
        rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
        exact ⟨rfl, heq ▸ hv'⟩⟩
    · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy,
           LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at hlookup
      have ⟨v, hσ, hvr⟩ := ih hlookup
      exact ⟨v, by
        simp only [Subst.insert, Subst.lookup]
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
        simp only [Subst.lookup] at hσ
        exact ⟨hσ, hvr⟩⟩

theorem semContextRel_dom {Γ : Context} {σ : Subst} :
    𝒢⟦Γ⟧ σ → Γ.dom = σ.dom := by
  intro hctx
  induction hctx with
  | semContextRel_empty => rfl
  | semContextRel_insert Γ' σ' v x A _ _ ih =>
    simp only [Context.dom, Subst.dom, Context.insert, Subst.insert]
    apply LawfulSet.ext
    intro k
    simp only [LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]
    by_cases hxk : x = k
    · subst hxk
      simp [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
    · constructor <;> intro h
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
             LawfulPartialMap.get?_delete_ne (M := MapStr) hxk] at h
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk]
        have hmem : k ∈ Context.dom Γ' := by
          rw [Context.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]; exact h
        rw [ih] at hmem
        rw [Subst.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)] at hmem
        exact hmem
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk] at h
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
            LawfulPartialMap.get?_delete_ne (M := MapStr) hxk]
        have hmem : k ∈ Subst.dom σ' := by
          rw [Subst.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)]; exact h
        rw [← ih] at hmem
        rw [Context.dom, LawfulFiniteMap.mem_dom_set (M := MapStr) (S := StringSet)] at hmem
        exact hmem

-- Helper: membership in domList iff lookup succeeds (for Context)
theorem mem_domList_iff_lookup_ctx {Γ : Context} {x : String} :
    x ∈ Γ.domList ↔ ∃ e, Γ.lookup x = some e := by
  simp only [Context.domList, Context.lookup]
  rw [List.mem_map]
  constructor
  · intro ⟨⟨k, v⟩, hmem', heq⟩
    simp at heq; subst heq
    exact ⟨v, (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mp hmem'⟩
  · intro ⟨e, he⟩
    exact ⟨(x, e), (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr he, rfl⟩

theorem lookup_mem_domList {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A → x ∈ Γ.domList := by
  intro h; rw [mem_domList_iff_lookup_ctx]; exact ⟨A, h⟩

-- domList of insert
theorem mem_domList_insert {Γ : Context} {x y : String} {A : Ty} :
    y ∈ (Γ.insert x A).domList ↔ y = x ∨ (y ∈ Γ.domList ∧ y ≠ x) := by
  constructor
  · intro hmem
    rw [mem_domList_iff_lookup_ctx] at hmem
    obtain ⟨e, he⟩ := hmem
    simp only [Context.insert, Context.lookup] at he
    by_cases hxy : x = y
    · left; exact hxy.symm
    · right
      rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy,
          LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at he
      exact ⟨(mem_domList_iff_lookup_ctx).mpr ⟨e, he⟩, fun h => hxy h.symm⟩
  · intro h
    rw [show (Γ.insert x A).domList = (FiniteMap.toList (M := MapStr)
        (Iris.Std.insert (M := MapStr) (Iris.Std.delete (M := MapStr) Γ x) x A)).map Prod.fst from rfl]
    rw [List.mem_map]
    cases h with
    | inl heq =>
      subst heq
      refine ⟨(y, A), ?_, rfl⟩
      apply (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr
      exact LawfulPartialMap.get?_insert_eq (M := MapStr) rfl
    | inr h =>
      obtain ⟨hmem, hne⟩ := h
      rw [mem_domList_iff_lookup_ctx] at hmem
      obtain ⟨B, hB⟩ := hmem
      have hne' : x ≠ y := Ne.symm hne
      have hget : Iris.Std.get? (Iris.Std.insert (Iris.Std.delete Γ x) x A) y = some B := by
        rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hne',
            LawfulPartialMap.get?_delete_ne (M := MapStr) hne']
        exact hB
      exact ⟨(y, B), (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr hget, rfl⟩

-- Compatibility for integer literals
theorem compat_int {Γ : Context} {n : Int} :
    Γ ⊨ Expr.litInt n : Ty.int := by
  constructor
  · simp [Expr.closed]
  · intro σ _
    unfold exprRel
    refine ⟨Val.litIntV n, by simp [substMap]; exact BigStep.litInt, ?_⟩
    unfold valRel; trivial

-- Compatibility for variables
theorem compat_var {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A → Γ ⊨ Expr.var x : A := by
  intro hlookup
  constructor
  · simp [Expr.closed]; exact lookup_mem_domList hlookup
  · intro σ hctx
    have ⟨v, hσ, hv⟩ := semCtxRelVal hctx hlookup
    show ℰ⟦A⟧ (substMap σ (Expr.var x))
    unfold substMap; simp only [hσ]
    exact val_inclusion hv

-- Compatibility for application
theorem compatApp {Γ : Context} {e₁ e₂ : Expr} {A B : Ty} :
    Γ ⊨ e₁ : (A ⇒ B) → Γ ⊨ e₂ : A → Γ ⊨ e₁ e₂ : B := by
  intro ⟨hcl₁, hsem₁⟩ ⟨hcl₂, hsem₂⟩
  constructor
  · simp [Expr.closed, hcl₁, hcl₂]
  · intro σ hctx
    have h1 := hsem₁ σ hctx
    unfold exprRel at h1
    obtain ⟨v₁, heval₁, hv₁⟩ := h1
    unfold valRel at hv₁
    cases v₁ with
    | litIntV n => exact absurd hv₁ id
    | lamV y e =>
      obtain ⟨hclosed, hbody⟩ := hv₁
      have h2 := hsem₂ σ hctx
      unfold exprRel at h2
      obtain ⟨v₂, heval₂, hv₂⟩ := h2
      have h3 := hbody v₂ hv₂
      unfold exprRel at h3
      obtain ⟨v, heval, hv⟩ := h3
      unfold exprRel
      exact ⟨v, by simp [substMap]; exact BigStep.app heval₁ heval₂ heval, hv⟩

-- Lambda closedness helper
theorem lamClosed (Γ : Context) (θ : Subst) (x: String) (A : Ty) (e : Expr) :
    e.closed ((Γ.insert x A).domList) →
    𝒢⟦Γ⟧ θ →
    (Expr.lam (Binder.named x) (substMap (Subst.delete x θ) e)).closed [] := by
  intro Hcl Hctxt
  simp [Expr.closed, Binder.cons]
  have hσcl : (Subst.delete x θ).closed [x] := Subst.closed_delete_weaken (semContextRel_closed Hctxt)
  apply substMapClosed (σ := Subst.delete x θ) (X := [x])
  · apply closed_weaken Hcl
    intro y hy
    rw [mem_domList_insert] at hy
    cases hy with
    | inl heq =>
      subst heq; exact List.mem_append.mpr (Or.inl (List.Mem.head _))
    | inr h =>
      obtain ⟨hmem, hne⟩ := h
      by_cases hyx : y = x
      · subst hyx; exact List.mem_append.mpr (Or.inl (List.Mem.head _))
      · apply List.mem_append.mpr; right
        rw [mem_domList_iff_lookup_ctx] at hmem
        obtain ⟨B, hB⟩ := hmem
        obtain ⟨v, hσ, _⟩ := semCtxRelVal Hctxt hB
        rw [mem_domList_iff_lookup]
        exact ⟨v.toExpr, by rw [lookup_delete_ne hyx]; exact hσ⟩
  · exact hσcl

-- Compatibility for lambda abstractions
theorem compatLamNamed {Γ : Context} {x : String} {e : Expr} {A B : Ty} :
    (Γ.insert x A) ⊨ e : B →
    Γ ⊨ Expr.lam (Binder.named x) e : (A ⇒ B) := by
  intro ⟨hbodycl, hbody⟩
  constructor
  · simp [Expr.closed, Binder.cons]
    apply closed_weaken hbodycl
    intro y hy
    rw [mem_domList_insert] at hy
    cases hy with
    | inl heq => subst heq; exact List.Mem.head _
    | inr h => exact List.Mem.tail _ h.1
  · intro θ Hctxt
    simp [substMap]
    unfold exprRel
    refine ⟨Val.lamV (Binder.named x) (substMap (Subst.delete x θ) e), BigStep.lam, ?_⟩
    show valRel (A ⇒ B) (Val.lamV (Binder.named x) (substMap (Subst.delete x θ) e))
    unfold valRel
    refine ⟨lamClosed Γ θ x A e hbodycl Hctxt, ?_⟩
    intro v' hv'
    simp [subst']
    rw [subst_substMap_compose (semContextRel_closed Hctxt)]
    exact hbody _ (semContextRel.semContextRel_insert Γ θ v' x A hv' Hctxt)

theorem compatPlus {Γ : Context} {e₁ e₂ : Expr} :
    Γ ⊨ e₁ : Ty.int → Γ ⊨ e₂ : Ty.int → Γ ⊨ Expr.plus e₁ e₂ : Ty.int := by
  intro ⟨hcl₁, hsem₁⟩ ⟨hcl₂, hsem₂⟩
  constructor
  · simp [Expr.closed, hcl₁, hcl₂]
  · intro σ hctx
    have h1 := hsem₁ σ hctx; unfold exprRel at h1
    obtain ⟨v₁, heval₁, hv₁⟩ := h1
    unfold valRel at hv₁
    cases v₁ with
    | litIntV n₁ =>
      have h2 := hsem₂ σ hctx; unfold exprRel at h2
      obtain ⟨v₂, heval₂, hv₂⟩ := h2
      unfold valRel at hv₂
      cases v₂ with
      | litIntV n₂ =>
        unfold exprRel
        refine ⟨Val.litIntV (n₁ + n₂),
          by simp [substMap]; exact BigStep.plus heval₁ heval₂, ?_⟩
        unfold valRel; trivial
      | lamV _ _ => exact absurd hv₂ id
    | lamV _ _ => exact absurd hv₁ id

theorem fundamental {Γ : Context} {e : Expr} {A : Ty} :
    (Γ ⊢ e : A) → (Γ ⊨ e : A) := by
  intro h
  induction h with
  | var hlookup => exact compat_var hlookup
  | lam_named _ ih => exact compatLamNamed ih
  | app _ _ ih₁ ih₂ => exact compatApp ih₁ ih₂
  | litInt => exact compat_int
  | plus _ _ ih₁ ih₂ => exact compatPlus ih₁ ih₂

theorem type_safety {e : Expr} {A : Ty} :
    (Context.empty ⊢ e : A) → terminates e := by
  intro htype
  have ⟨_, hsem⟩ := fundamental htype
  have h := hsem Subst.empty semContextRel.semContextRel_empty
  rw [substMap_empty] at h
  unfold exprRel at h
  obtain ⟨v, heval, _⟩ := h
  exact ⟨v, heval⟩

end STLC
