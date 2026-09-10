import LeanLR.TypeSystems.SystemF.LogRel

/-!
# System F: free theorems

`systemf/free_theorems.v`. Two consequences of parametricity, read off the logical relation by
instantiating a universally quantified type variable with a *chosen* semantic type: there is no
closed term of type `∀ α. α`, and every closed term of type `∀ α. α → α` is the identity.
-/

open Iris.Std

namespace SystemF

theorem not_every_type_inhabited :
    ¬ ∃ e : Expr, SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e (.all (.tVar 0)) := by
  rintro ⟨e, hty⟩
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  simp only [valRel] at hv
  obtain ⟨e', rfl, hcl, hall⟩ := hv
  -- Instantiate the type variable with the empty semantic type.
  let τ : SemType := ⟨fun _ => False, fun _ h => h.elim⟩
  obtain ⟨w, _, hw⟩ := hall τ
  exact hw

theorem all_identity (e : Expr)
    (hty : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e
      (.all (.fn (.tVar 0) (.tVar 0))))
    (v₀ : Val) (hcl₀ : closed [] v₀.toExpr) :
    BigStep (.app (.tApp e) v₀.toExpr) v₀ := by
  obtain ⟨_, hsem⟩ := sem_soundness hty
  obtain ⟨v, hb, hv⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  simp only [valRel] at hv
  obtain ⟨e', rfl, hcl, hall⟩ := hv
  -- Instantiate the type variable with the singleton semantic type `{v₀}`.
  let τ : SemType := ⟨fun w => w = v₀, fun w h => by subst h; exact hcl₀⟩
  obtain ⟨w, hbw, hw⟩ := hall τ
  obtain ⟨x, e'', rfl, _, hbody⟩ := hw
  obtain ⟨u, hbu, hu⟩ := hbody v₀ (show τ.car v₀ from rfl)
  have : u = v₀ := hu
  subst this
  exact .bs_app _ _ x e'' _ _ (.bs_tapp _ _ _ hb hbw) (big_step_of_val rfl) hbu

end SystemF
