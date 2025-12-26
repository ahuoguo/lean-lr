import LeanLr.Lang
import LeanLr.Operational

namespace STLC

-- TODO: maybe switch to ExtTreeMap?
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/stdpp/near/563551375
-- Finite map substitution (like gmap in Coq)
abbrev Subst := List (String × Expr)

def Subst.empty : Subst := []

def Subst.delete (x : String) (σ : Subst) : Subst :=
  σ.filter (fun p => p.1 ≠ x)

def Subst.insert (x : String) (e : Expr) (σ : Subst) : Subst :=
  (x, e) :: σ.delete x

def Subst.lookup (σ : Subst) (x : String) : Option Expr :=
  List.lookup x σ

def Subst.dom (σ : Subst) : List String :=
  σ.map (·.1)

def Subst.closed (X: List String) (σ: Subst) :=
  ∀ x e, σ.lookup x = some e → e.closed X

def Subst.isSubSubstOf (σ: Subst) (σ': Subst) :=
  ∀ x, x ∈ σ → x ∈ σ'

-- TODO:
notation :70 A "⊆" B => Subst.isSubSubstOf A B

-- Apply finite map substitution to expression
-- TODO: maybe we can define a substmap as `Expr.substMap`?
def substMap (σ : Subst) : Expr → Expr
  | Expr.var x => match List.lookup x σ with
    | some e => e
    | none => Expr.var x
  | Expr.lam (Binder.named x) e =>
      Expr.lam (Binder.named x) (substMap (σ.delete x) e)
  | Expr.lam Binder.anon e => Expr.lam Binder.anon (substMap σ e)
  | Expr.app e₁ e₂ => Expr.app (substMap σ e₁) (substMap σ e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ => Expr.plus (substMap σ e₁) (substMap σ e₂)

-- Lemma subst_closed_weaken X Y map1 map2 :
--   Y ⊆ X → map1 ⊆ map2 → subst_closed Y map2 → subst_closed X map1.
-- Proof.
--   intros Hsub1 Hsub2 Hclosed2 x e Hl.
--   eapply closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
-- Qed.


-- Helper: applying empty substitution is identity
theorem substMap_empty (e : Expr) : substMap Subst.empty e = e := by
  sorry

-- Lemma subst_map_closed'_2 X Θ e:
--   closed (X ++ (elements (dom Θ))) e ->
--   subst_closed X Θ ->
--   closed X (subst_map Θ e).
-- Proof.
theorem substMapClosed {X : List String} {σ : Subst} {e : Expr} :
    e.closed (X ++ σ.dom) →
    σ.closed X →
    (substMap σ e).closed X := by
  sorry

-- Lemma about the interaction with "normal" substitution.
-- Lemma subst_subst_map x es map e :
--   subst_closed [] map →
--   subst x es (subst_map (delete x map) e) =
--   subst_map (<[x:=es]> map) e.
theorem subst_substMap_compose {x : String} {es : Expr} {θ : Subst} {e : Expr} :
    θ.closed [] →
    subst x es (substMap (θ.delete x) e) = substMap (Subst.insert x es θ) e := by
  sorry

-- Helper: weakening for closed expressions
theorem closed_weaken {X Y : List String} {e : Expr} :
    e.closed X → (∀ x, x ∈ X → x ∈ Y) → e.closed Y := by
  intro hclosed hsub
  induction e generalizing X Y with
  | var x =>
    simp [Expr.closed] at hclosed ⊢
    exact hsub x hclosed
  | lam b e ih =>
    simp [Expr.closed] at hclosed ⊢
    apply ih hclosed
    intro z hz
    cases b with
    | anon => exact hsub z hz
    | named y =>
      simp [Binder.cons] at hz ⊢
      cases hz with
      | inl heq => left; exact heq
      | inr hmem => right; exact hsub z hmem
  | app e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩
  | litInt n =>
    simp [Expr.closed]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩



-- Lemma subst_closed_weaken X Y map1 map2 :
--   Y ⊆ X → map1 ⊆ map2 → subst_closed Y map2 → subst_closed X map1.
-- Proof.
--   intros Hsub1 Hsub2 Hclosed2 x e Hl.
--   eapply closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
-- Qed.
theorem substClosedWeaken {X Y: List String} {σ1 σ2 : Subst} :
  -- TODO: `σ1 ⊆ σ2` doesn't quite work
  (Y ⊆ X) → (σ1.isSubSubstOf σ2) → σ2.closed Y → σ1.closed X
  := sorry

end STLC
