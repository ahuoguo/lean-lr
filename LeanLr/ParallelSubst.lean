import LeanLr.Lang
import LeanLr.Operational
import LeanLr.Types

import Iris.Std.PartialMap
import Iris.Std.GenSets
import Iris.Std.GenSetsInstances
import Iris.Std.HeapInstances

open Iris.Std

namespace STLC

-- Parallel substitution map (like gmap string expr in Coq)
abbrev Subst := MapStr Expr

def Subst.empty : Subst := PartialMap.empty (M := MapStr) (V := Expr)

def Subst.delete (x : String) (σ : Subst) : Subst :=
  Iris.Std.delete (M := MapStr) σ x

nonrec def Subst.insert (x : String) (e : Expr) (σ : Subst) : Subst :=
  Iris.Std.insert (M := MapStr) σ x e

def Subst.lookup (σ : Subst) (x : String) : Option Expr :=
  Iris.Std.get? (M := MapStr) σ x

def Subst.domList (σ : Subst) : List String :=
  (FiniteMap.toList (M := MapStr) σ).map Prod.fst

def Subst.dom (σ : Subst) : StringSet :=
  FiniteMap.dom_set (M := MapStr) σ

def Subst.closed (X: List String) (σ: Subst) :=
  ∀ x e, σ.lookup x = some e → e.closed X

def Subst.mem (σ : Subst) (x : String) : Bool :=
  (Subst.lookup σ x).isSome

notation:90 σ " <[ " x " := " e " ]> " => Subst.insert x e σ

-- Apply parallel substitution to expression
def substMap (σ : Subst) : Expr → Expr
  | Expr.var x => match Subst.lookup σ x with
    | some e => e
    | none => Expr.var x
  | Expr.lam (Binder.named x) e =>
      Expr.lam (Binder.named x) (substMap (Subst.delete x σ) e)
  | Expr.lam Binder.anon e => Expr.lam Binder.anon (substMap σ e)
  | Expr.app e₁ e₂ => Expr.app (substMap σ e₁) (substMap σ e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ => Expr.plus (substMap σ e₁) (substMap σ e₂)

-- Helper: two subst maps with same get? are equal
private theorem subst_ext {σ₁ σ₂ : Subst}
    (h : ∀ k, Iris.Std.get? (M := MapStr) σ₁ k = Iris.Std.get? (M := MapStr) σ₂ k) :
    σ₁ = σ₂ :=
  ExtensionalPartialMap.equiv_iff_eq.mp h

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
    constructor
    · exact ih₁ hclosed.1 hsub
    · exact ih₂ hclosed.2 hsub
  | litInt n =>
    simp [Expr.closed]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hsub
    · exact ih₂ hclosed.2 hsub

-- Helper: deleting from empty gives empty
theorem delete_empty (x : String) : Subst.delete x Subst.empty = Subst.empty := by
  simp only [Subst.delete, Subst.empty]
  apply subst_ext
  intro k
  have hempty : Iris.Std.get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) k = none :=
    LawfulPartialMap.get?_empty (M := MapStr) k
  by_cases heq : x = k
  · simp [LawfulPartialMap.get?_delete_eq (M := MapStr) heq, hempty]
  · simp [LawfulPartialMap.get?_delete_ne (M := MapStr) heq, hempty]

-- Helper: applying empty substitution is identity
theorem substMap_empty (e : Expr) : substMap Subst.empty e = e := by
  induction e with
  | var x =>
    simp only [substMap, Subst.empty, Subst.lookup]
    have h : Iris.Std.get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) x = none :=
      LawfulPartialMap.get?_empty (M := MapStr) x
    simp [h]
  | lam b e ih =>
    cases b with
    | anon => simp [substMap, ih]
    | named x =>
      simp only [substMap]
      rw [delete_empty x]
      rw [ih]
  | app e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]
  | litInt n => rfl
  | plus e₁ e₂ ih₁ ih₂ => simp [substMap, ih₁, ih₂]

-- Helper lemma for lookup in delete
theorem lookup_delete_ne {σ : Subst} {x y : String} :
    x ≠ y → (Subst.delete y σ).lookup x = σ.lookup x := by
  intro hne
  simp only [Subst.delete, Subst.lookup]
  exact LawfulPartialMap.get?_delete_ne (M := MapStr) hne.symm

theorem lookup_delete_eq {σ : Subst} {x : String} :
    (Subst.delete x σ).lookup x = none := by
  simp only [Subst.delete, Subst.lookup]
  exact LawfulPartialMap.get?_delete_eq (M := MapStr) rfl

-- Helper: closed is preserved by weakening the context
theorem Subst.closed_weaken {X Y : List String} {σ : Subst} :
    (∀ x, x ∈ X → x ∈ Y) → σ.closed X → σ.closed Y := by
  intro hsub hclosed x e hlookup
  have hcl := hclosed x e hlookup
  exact STLC.closed_weaken hcl hsub

-- Helper: deleting preserves closedness with weaker context
theorem Subst.closed_delete_weaken {X : List String} {σ : Subst} {x : String} :
    σ.closed X → (σ.delete x).closed (x :: X) := by
  intro hclosed y e hlookup
  unfold Subst.closed at *
  have hne : y ≠ x := by
    intro heq
    subst heq
    rw [lookup_delete_eq] at hlookup
    contradiction
  have : σ.lookup y = some e := by
    rw [← lookup_delete_ne hne]
    exact hlookup
  have hcl := hclosed y e this
  exact STLC.closed_weaken hcl (fun z hz => List.Mem.tail x hz)

-- Helper: membership in domList corresponds to successful lookup
theorem mem_domList_iff_lookup {σ : Subst} {x : String} :
    x ∈ Subst.domList σ ↔ ∃ e, Subst.lookup σ x = some e := by
  simp only [Subst.domList, Subst.lookup]
  rw [List.mem_map]
  constructor
  · intro ⟨⟨k, v⟩, hmem', heq⟩
    simp at heq
    subst heq
    have h := (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mp hmem'
    exact ⟨v, h⟩
  · intro ⟨e, he⟩
    have hmem : (x, e) ∈ (FiniteMap.toList (M := MapStr) σ) :=
      (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr he
    exact ⟨(x, e), hmem, rfl⟩

-- Helper: if y is in σ.domList and y ≠ x, then y is in (σ.delete x).domList
theorem mem_domList_delete {σ : Subst} {x y : String} :
    y ∈ Subst.domList σ → y ≠ x → y ∈ Subst.domList (Subst.delete x σ) := by
  intro hmem hne
  rw [mem_domList_iff_lookup] at hmem ⊢
  obtain ⟨e, he⟩ := hmem
  exists e
  rw [lookup_delete_ne hne]
  exact he

theorem lookup_insert_eq {σ : Subst} {x : String} {e : Expr} :
    (Subst.insert x e σ).lookup x = some e := by
  simp only [Subst.insert, Subst.lookup]
  exact LawfulPartialMap.get?_insert_eq (M := MapStr) rfl

theorem lookup_insert_ne {σ : Subst} {x y : String} {e : Expr} (h : x ≠ y) :
    (Subst.insert y e σ).lookup x = σ.lookup x := by
  simp only [Subst.insert, Subst.lookup]
  exact LawfulPartialMap.get?_insert_ne (M := MapStr) h.symm

-- Helper: if x is not in the closed set, substitution doesn't change the expression
theorem subst_closed_notmem {x : String} {es : Expr} {e : Expr} {X : List String} :
    e.closed X = true → x ∉ X → subst x es e = e := by
  intro hclosed hnotmem
  induction e generalizing X with
  | var y =>
    simp [Expr.closed] at hclosed
    simp [subst]
    intro heq
    subst heq
    exact (hnotmem hclosed).elim
  | lam b e' ih =>
    cases b with
    | anon =>
      simp [subst, Expr.closed] at hclosed ⊢
      exact ih hclosed hnotmem
    | named y =>
      simp [subst, Expr.closed, Binder.cons] at hclosed ⊢
      intro hne
      apply ih hclosed
      intro hmem
      cases hmem with
      | head => exact hne rfl
      | tail _ hmem' => exact hnotmem hmem'
  | app e₁ e₂ ih₁ ih₂ =>
    simp [subst, Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | litInt n => rfl
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [subst, Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem

theorem subst_closed_nil {x : String} {es : Expr} {e : Expr} :
    e.closed [] = true → subst x es e = e := by
  intro hclosed
  apply subst_closed_notmem hclosed
  simp

-- Key lemma: substMap preserves closedness
theorem substMapClosed {X : List String} {σ : Subst} {e : Expr} :
    e.closed (X ++ σ.domList) →
    σ.closed X →
    (substMap σ e).closed X := by
  intro hclosed hσclosed
  induction e generalizing X σ with
  | var x =>
    simp [substMap]
    split
    · next he => exact hσclosed x _ he
    · simp [Expr.closed] at hclosed ⊢
      cases hclosed with
      | inl h => exact h
      | inr h =>
        have : x ∈ σ.domList := h
        rw [mem_domList_iff_lookup] at this
        obtain ⟨e', he'⟩ := this
        simp_all [Subst.lookup]
  | lam b e' ih =>
    cases b with
    | anon =>
      simp [substMap, Expr.closed] at hclosed ⊢
      exact ih hclosed hσclosed
    | named y =>
      simp [substMap, Expr.closed, Binder.cons] at hclosed ⊢
      apply ih
      · apply closed_weaken hclosed
        intro z hz
        cases hz with
        | head =>
          rw [List.mem_append]
          left
          apply List.Mem.head
        | tail _ hrest =>
          have : z ∈ X ∨ z ∈ σ.domList := List.mem_append.mp hrest
          rw [List.mem_append]
          cases this with
          | inl hx =>
            left
            apply List.Mem.tail
            exact hx
          | inr hdom =>
            by_cases heq : z = y
            · subst heq
              left
              apply List.Mem.head
            · right
              exact mem_domList_delete hdom heq
      · exact Subst.closed_delete_weaken hσclosed
  | app e₁ e₂ ih₁ ih₂ =>
    simp [substMap, Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hσclosed
    · exact ih₂ hclosed.2 hσclosed
  | litInt n => simp [substMap, Expr.closed]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [substMap, Expr.closed, Bool.and_eq_true] at hclosed ⊢
    constructor
    · exact ih₁ hclosed.1 hσclosed
    · exact ih₂ hclosed.2 hσclosed

-- Key lemma: interaction between normal substitution and parallel substitution
-- Corresponds to Coq's subst_subst_map
theorem subst_substMap_compose {x : String} {es : Expr} {θ : Subst} {e : Expr} :
    θ.closed [] →
    subst x es (substMap (θ.delete x) e) = substMap (Subst.insert x es θ) e := by
  intro hclosed
  induction e generalizing θ with
  | var y =>
    simp only [substMap, Subst.lookup, Subst.delete, Subst.insert]
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
      simp [subst]
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]
      rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      cases hget : Iris.Std.get? (M := MapStr) θ y with
      | none => simp [subst, hxy]
      | some e' =>
        have hcl : e'.closed [] := hclosed y e' hget
        exact subst_closed_nil hcl
  | lam b e' ih =>
    cases b with
    | anon =>
      simp [substMap, subst]
      exact ih hclosed
    | named y =>
      simp only [substMap, subst]
      split
      · next heq =>
        have hxy : x = y := by
          cases heq; rfl
        subst hxy
        congr 1
        have : Subst.delete x (Subst.delete x θ) = Subst.delete x (Subst.insert x es θ) := by
          apply subst_ext
          intro k
          show Iris.Std.get? (M := MapStr)
            (Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) θ x) x) k =
            Iris.Std.get? (M := MapStr)
            (Iris.Std.delete (M := MapStr) (Iris.Std.insert (M := MapStr) θ x es) x) k
          by_cases hkx : x = k
          · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_eq (M := MapStr) hkx]
          · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
                 LawfulPartialMap.get?_insert_ne (M := MapStr) hkx]
        rw [this]
      · next hne =>
        have hxy : x ≠ y := by
          intro heq'
          apply hne
          rw [heq']
        congr 1
        have hcomm : Subst.delete y (Subst.delete x θ) = Subst.delete x (Subst.delete y θ) := by
          apply subst_ext; intro k
          show Iris.Std.get? (M := MapStr)
            (Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) θ x) y) k =
            Iris.Std.get? (M := MapStr)
            (Iris.Std.delete (M := MapStr) (Iris.Std.delete (M := MapStr) θ y) x) k
          by_cases hyk : y = k <;> by_cases hxk : x = k
          · subst hyk; subst hxk; exact absurd rfl hxy
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
        have hcomm2 : Subst.delete y (Subst.insert x es θ) = Subst.insert x es (Subst.delete y θ) := by
          apply subst_ext; intro k
          show Iris.Std.get? (M := MapStr)
            (Iris.Std.delete (M := MapStr) (Iris.Std.insert (M := MapStr) θ x es) y) k =
            Iris.Std.get? (M := MapStr)
            (Iris.Std.insert (M := MapStr) (Iris.Std.delete (M := MapStr) θ y) x es) k
          by_cases hyk : y = k
          · subst hyk
            rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
                LawfulPartialMap.get?_insert_ne (M := MapStr) hxy,
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
        have hclosed' : (Subst.delete y θ).closed [] := by
          intro z ez hlz
          have hne' : z ≠ y := by
            intro heq'
            subst heq'
            rw [lookup_delete_eq] at hlz
            contradiction
          rw [lookup_delete_ne hne'] at hlz
          exact hclosed z ez hlz
        exact ih hclosed'
  | app e₁ e₂ ih₁ ih₂ =>
    simp [substMap, subst, ih₁ hclosed, ih₂ hclosed]
  | litInt n =>
    simp [substMap, subst]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [substMap, subst, ih₁ hclosed, ih₂ hclosed]

end STLC
