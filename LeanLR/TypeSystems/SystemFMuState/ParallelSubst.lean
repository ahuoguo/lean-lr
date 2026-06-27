/-
  System F with recursive types and mutable state - Parallel Substitution
  Ported from semantics-2025/theories/type_systems/systemf_mu_state/parallel_subst.v
-/

import LeanLR.TypeSystems.SystemFMuState.Lang

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

open Iris.Std

namespace SystemFMuState

abbrev MapStr (V : Type) := Std.ExtTreeMap String V compare
abbrev SubstMap := MapStr Expr

def binderDelete (b : Binder) (m : SubstMap) : SubstMap :=
  match b with
  | .bAnon => m
  | .bNamed x => Iris.Std.delete (M := MapStr) m x

-- Parallel substitution
def substMap (xs : SubstMap) : Expr → Expr
  | .lit l => .lit l
  | .var y => match Iris.Std.get? (M := MapStr) xs y with | some es => es | none => .var y
  | .lam x e => .lam x (substMap (binderDelete x xs) e)
  | .app e₁ e₂ => .app (substMap xs e₁) (substMap xs e₂)
  | .unOp op e => .unOp op (substMap xs e)
  | .binOp op e₁ e₂ => .binOp op (substMap xs e₁) (substMap xs e₂)
  | .ite e₀ e₁ e₂ => .ite (substMap xs e₀) (substMap xs e₁) (substMap xs e₂)
  | .tApp e => .tApp (substMap xs e)
  | .tLam e => .tLam (substMap xs e)
  | .pack e => .pack (substMap xs e)
  | .unpack x e₁ e₂ => .unpack x (substMap xs e₁) (substMap (binderDelete x xs) e₂)
  | .pair e₁ e₂ => .pair (substMap xs e₁) (substMap xs e₂)
  | .fst e => .fst (substMap xs e)
  | .snd e => .snd (substMap xs e)
  | .injL e => .injL (substMap xs e)
  | .injR e => .injR (substMap xs e)
  | .case e₀ e₁ e₂ => .case (substMap xs e₀) (substMap xs e₁) (substMap xs e₂)
  | .roll e => .roll (substMap xs e)
  | .unroll e => .unroll (substMap xs e)
  | .load e => .load (substMap xs e)
  | .store e₁ e₂ => .store (substMap xs e₁) (substMap xs e₂)
  | .new e => .new (substMap xs e)

private theorem binderDelete_empty (b : Binder) :
    binderDelete b (PartialMap.empty (M := MapStr) (V := Expr)) =
    PartialMap.empty (M := MapStr) (V := Expr) := by
  cases b with
  | bAnon => rfl
  | bNamed x =>
    simp only [binderDelete]
    exact ExtensionalPartialMap.equiv_iff_eq.mp
      (LawfulPartialMap.delete_empty (M := MapStr))

theorem substMap_empty (e : Expr) :
    substMap (PartialMap.empty (M := MapStr) (V := Expr)) e = e := by
  induction e with
  | lit _ => rfl
  | var y =>
    simp only [substMap]
    have h : Iris.Std.get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) y = none :=
      LawfulPartialMap.get?_empty (M := MapStr) y
    simp [h]
  | lam b e' ih => simp only [substMap]; rw [binderDelete_empty, ih]
  | app e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | unOp op e' ih => simp [substMap, ih]
  | binOp op e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp [substMap, ih₀, ih₁, ih₂]
  | tApp e' ih => simp [substMap, ih]
  | tLam e' ih => simp [substMap, ih]
  | pack e' ih => simp [substMap, ih]
  | unpack b e₁ e₂ ih₁ ih₂ => simp only [substMap]; rw [binderDelete_empty, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | fst e' ih => simp [substMap, ih]
  | snd e' ih => simp [substMap, ih]
  | injL e' ih => simp [substMap, ih]
  | injR e' ih => simp [substMap, ih]
  | case e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp [substMap, ih₀, ih₁, ih₂]
  | roll e' ih => simp [substMap, ih]
  | unroll e' ih => simp [substMap, ih]
  | load e' ih => simp [substMap, ih]
  | store e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | new e' ih => simp [substMap, ih]

def substIsClosed (X : List String) (m : SubstMap) : Prop :=
  ∀ x e, Iris.Std.get? (M := MapStr) m x = some e → closed X e

private theorem subst_closed_notmem {x : String} {es : Expr} {e : Expr} {X : List String}
    (hclosed : closed X e) (hnotmem : x ∉ X) : subst x es e = e := by
  induction e generalizing X with
  | lit _ => rfl
  | var y =>
    simp [closed, Expr.isClosed] at hclosed
    simp only [subst]
    have hne : x ≠ y := by intro heq; subst heq; exact hnotmem hclosed
    simp [hne]
  | lam b e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst
    cases b with
    | bAnon =>
      congr 1
      exact ih hclosed hnotmem
    | bNamed y =>
      congr 1
      simp only [Binder.cons] at hclosed
      by_cases hxy : Binder.bNamed x = Binder.bNamed y
      · simp [hxy]
      · simp [hxy]
        have hxy' : x ≠ y := by intro h; exact hxy (congrArg Binder.bNamed h)
        exact ih hclosed (fun hmem => by
          cases hmem with
          | head => exact hxy' rfl
          | tail _ hmem' => exact hnotmem hmem')
  | app e₁ e₂ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | unOp op e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | binOp op e₁ e₂ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₀ hclosed.1.1 hnotmem
    · exact ih₁ hclosed.1.2 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | tApp e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | tLam e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | pack e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst
    cases b with
    | bAnon =>
      congr 1
      · exact ih₁ hclosed.1 hnotmem
      · exact ih₂ hclosed.2 hnotmem
    | bNamed y =>
      simp only [Binder.cons] at hclosed
      congr 1
      · exact ih₁ hclosed.1 hnotmem
      · by_cases hxy : Binder.bNamed x = Binder.bNamed y
        · simp [hxy]
        · simp [hxy]
          have hxy' : x ≠ y := by intro h; exact hxy (congrArg Binder.bNamed h)
          exact ih₂ hclosed.2 (fun hmem => by
            cases hmem with
            | head => exact hxy' rfl
            | tail _ hmem' => exact hnotmem hmem')
  | pair e₁ e₂ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | fst e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | snd e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | injL e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | injR e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | case e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₀ hclosed.1.1 hnotmem
    · exact ih₁ hclosed.1.2 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | roll e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | unroll e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | load e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem
  | store e₁ e₂ ih₁ ih₂ =>
    simp [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst; congr 1
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | new e' ih =>
    simp [closed, Expr.isClosed] at hclosed
    unfold subst; congr 1; exact ih hclosed hnotmem

private theorem subst_closed_nil {x : String} {es : Expr} {e : Expr}
    (hclosed : closed [] e) : subst x es e = e :=
  subst_closed_notmem hclosed (by simp)

private theorem map_ext {m₁ m₂ : SubstMap}
    (h : ∀ k, Iris.Std.get? (M := MapStr) m₁ k = Iris.Std.get? (M := MapStr) m₂ k) :
    m₁ = m₂ :=
  ExtensionalPartialMap.equiv_iff_eq.mp h

theorem subst_substMap (x : String) (es : Expr) (m : SubstMap) (e : Expr) :
    substIsClosed [] m →
    subst x es (substMap (Iris.Std.delete (M := MapStr) m x) e) =
    substMap (Iris.Std.insert (M := MapStr) m x es) e := by
  intro hclosed
  induction e generalizing m with
  | lit _ => simp [substMap, subst]
  | var y =>
    simp only [substMap]
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
      simp [subst]
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]
      rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      cases hget : Iris.Std.get? (M := MapStr) m y with
      | none => simp [subst, hxy]
      | some e' =>
        have hcl : closed [] e' := hclosed y e' hget
        exact subst_closed_nil hcl
  | lam b e' ih =>
    cases b with
    | bAnon =>
      simp only [substMap, binderDelete, subst]
      congr 1; exact ih m hclosed
    | bNamed y =>
      simp only [substMap, binderDelete]
      unfold subst
      congr 1
      by_cases hxy : Binder.bNamed x = Binder.bNamed y
      · -- x = y case (binder shadows)
        simp [hxy]
        have hxy' : x = y := by cases hxy; rfl
        subst hxy'
        congr 1
        apply map_ext; intro k
        by_cases hkx : x = k
        · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hkx,
               LawfulPartialMap.get?_delete_eq (M := MapStr) hkx]
        · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
               LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
               LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
               LawfulPartialMap.get?_insert_ne (M := MapStr) hkx]
      · -- x ≠ y case
        simp [hxy]
        have hxy' : x ≠ y := by intro heq'; apply hxy; rw [heq']
        have hcomm : Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) m x) y =
                     Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) m y) x := by
          apply map_ext; intro k
          by_cases hyk : y = k <;> by_cases hxk : x = k
          · subst hyk; subst hxk; exact absurd rfl hxy'
          · subst hyk
            rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
          · subst hxk
            rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
          · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hyk]
        have hcomm2 : Iris.Std.delete (M := MapStr) (Iris.Std.insert (M := MapStr) m x es) y =
                      Iris.Std.insert (M := MapStr) (Iris.Std.delete (M := MapStr) m y) x es := by
          apply map_ext; intro k
          by_cases hyk : y = k
          · subst hyk
            rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                LawfulPartialMap.get?_insert_ne (M := MapStr) hxy',
                LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
          · by_cases hxk : x = k
            · subst hxk
              rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                  LawfulPartialMap.get?_insert_eq (M := MapStr) rfl,
                  LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
            · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                   LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
                   LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
                   LawfulPartialMap.get?_delete_ne (M := MapStr) hyk]
        rw [hcomm, hcomm2]
        have hclosed' : substIsClosed [] (Iris.Std.delete (M := MapStr) m y) := by
          intro z ez hlz
          have hne' : y ≠ z := by
            intro heq'; subst heq'
            rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hlz
            contradiction
          rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hne'] at hlz
          exact hclosed z ez hlz
        exact ih _ hclosed'
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | unOp op e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | binOp op e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₀ m hclosed
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | tApp e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | tLam e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | pack e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | unpack b e₁ e₂ ih₁ ih₂ =>
    cases b with
    | bAnon =>
      simp only [substMap, binderDelete, subst]
      congr 1
      · exact ih₁ m hclosed
      · exact ih₂ m hclosed
    | bNamed y =>
      simp only [substMap, binderDelete]
      unfold subst
      congr 1
      · exact ih₁ m hclosed
      · by_cases hxy : Binder.bNamed x = Binder.bNamed y
        · -- x = y case
          simp [hxy]
          have hxy' : x = y := by cases hxy; rfl
          subst hxy'
          congr 1
          apply map_ext; intro k
          by_cases hkx : x = k
          · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_eq (M := MapStr) hkx]
          · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_insert_ne (M := MapStr) hkx]
        · -- x ≠ y case
          simp [hxy]
          have hxy' : x ≠ y := by intro heq'; apply hxy; rw [heq']
          have hcomm : Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) m x) y =
                       Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) m y) x := by
            apply map_ext; intro k
            by_cases hyk : y = k <;> by_cases hxk : x = k
            · subst hyk; subst hxk; exact absurd rfl hxy'
            · subst hyk
              rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                  LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                  LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
            · subst hxk
              rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                  LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                  LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
            · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                   LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                   LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
                   LawfulPartialMap.get?_delete_ne (M := MapStr) hyk]
          have hcomm2 : Iris.Std.delete (M := MapStr) (Iris.Std.insert (M := MapStr) m x es) y =
                        Iris.Std.insert (M := MapStr) (Iris.Std.delete (M := MapStr) m y) x es := by
            apply map_ext; intro k
            by_cases hyk : y = k
            · subst hyk
              rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                  LawfulPartialMap.get?_insert_ne (M := MapStr) hxy',
                  LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
            · by_cases hxk : x = k
              · subst hxk
                rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                    LawfulPartialMap.get?_insert_eq (M := MapStr) rfl,
                    LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
              · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hyk,
                     LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
                     LawfulPartialMap.get?_insert_ne (M := MapStr) hxk,
                     LawfulPartialMap.get?_delete_ne (M := MapStr) hyk]
          rw [hcomm, hcomm2]
          have hclosed' : substIsClosed [] (Iris.Std.delete (M := MapStr) m y) := by
            intro z ez hlz
            have hne' : y ≠ z := by
              intro heq'; subst heq'
              rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hlz
              contradiction
            rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hne'] at hlz
            exact hclosed z ez hlz
          exact ih₂ _ hclosed'
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | fst e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | snd e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | injL e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | injR e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | case e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₀ m hclosed
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | roll e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | unroll e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | load e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed
  | store e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, subst]; congr 1
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | new e' ih =>
    simp only [substMap, subst]; congr 1; exact ih m hclosed

theorem subst'_substMap (b : Binder) (es : Expr) (m : SubstMap) (e : Expr) :
    substIsClosed [] m →
    subst' b es (substMap (binderDelete b m) e) =
    substMap (match b with | .bAnon => m | .bNamed x => Iris.Std.insert (M := MapStr) m x es) e := by
  intro hclosed
  cases b with
  | bAnon => simp [subst', binderDelete]
  | bNamed x => exact subst_substMap x es m e hclosed

end SystemFMuState
