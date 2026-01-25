import LeanLr.Lang
import LeanLr.Operational
import LeanLr.Types
import Std.Data.ExtTreeMap

import Iris.Std.FiniteMap
import Iris.Std.FiniteMapInst
import Iris.Std.FiniteSet
import Iris.Std.FiniteSetInst

open Iris.Std

namespace STLC

-- Finite map substitution using FiniteMap interface (like gmap in Coq)
-- The underlying implementation is ExtTreeMap, but we use the abstract interface
abbrev Subst := Std.ExtTreeMap String Expr compare

-- Type alias for the FiniteMap instance type
abbrev SubstMap := Std.ExtTreeMap String

def Subst.empty : Subst :=
  (FiniteMap.empty : SubstMap Expr)

def Subst.delete (x : String) (σ : Subst) : Subst :=
  (FiniteMap.delete σ x : SubstMap Expr)

nonrec def Subst.insert (x : String) (e : Expr) (σ : Subst) : Subst :=
  (FiniteMap.insert σ x e : SubstMap Expr)

def Subst.lookup (σ : Subst) (x : String) : Option Expr :=
  FiniteMap.get? (M := SubstMap) σ x

-- Return domain as a List (for compatibility with proofs using List operations)
def Subst.domList (σ : Subst) : List String :=
  (FiniteMap.toList (M := SubstMap) σ).map Prod.fst

-- Return domain as a FiniteSet (default) using FiniteMapDom
def Subst.dom (σ : Subst) : StringSet :=
  domSet (M := SubstMap) (S := StringSet) σ

def Subst.closed (X: List String) (σ: Subst) :=
  ∀ x e, σ.lookup x = some e → e.closed X

-- Check if key is in substitution using FiniteMap membership
def Subst.mem (σ : Subst) (x : String) : Bool :=
  (Subst.lookup σ x).isSome

def Subst.isSubSubstOf (σ: Subst) (σ': Subst) :=
  ∀ x, σ.mem x → σ'.mem x

-- TODO:
notation :70 A "⊆" B => Subst.isSubSubstOf A B
notation:90 σ " <[ " x " := " e " ]> " => Subst.insert x e σ

-- Apply finite map substitution to expression
-- Using FiniteMap operations
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
  exact FiniteMapLaws.delete_empty' (M := SubstMap) (K := String) (V := Expr) x

-- Helper: applying empty substitution is identity
theorem substMap_empty (e : Expr) : substMap Subst.empty e = e := by
  induction e with
  | var x =>
    simp only [substMap, Subst.empty, Subst.lookup]
    have h : FiniteMap.get? (M := SubstMap) (FiniteMap.empty : SubstMap Expr) x = none :=
      FiniteMapLaws.lookup_empty (M := SubstMap) (K := String) (V := Expr) x
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

-- Helper lemma for lookup in delete - using FiniteMapLaws
theorem lookup_delete_ne {σ : Subst} {x y : String} :
    x ≠ y → (Subst.delete y σ).lookup x = σ.lookup x := by
  intro hne
  simp only [Subst.delete, Subst.lookup]
  exact FiniteMapLaws.lookup_delete_ne (M := SubstMap) (K := String) (V := Expr) σ y x hne.symm

theorem lookup_delete_eq {σ : Subst} {x : String} :
    (Subst.delete x σ).lookup x = none := by
  simp only [Subst.delete, Subst.lookup]
  exact FiniteMapLaws.lookup_delete_eq (M := SubstMap) (K := String) (V := Expr) σ x

-- Helper: closed is preserved by weakening the context
theorem Subst.closed_weaken {X Y : List String} {σ : Subst} :
    (∀ x, x ∈ X → x ∈ Y) → σ.closed X → σ.closed Y := by
  intro hsub hclosed x e hlookup
  have hcl := hclosed x e hlookup
  have : e.closed Y := STLC.closed_weaken hcl hsub
  exact this

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
  have : e.closed (x :: X) := STLC.closed_weaken hcl (fun z hz => List.Mem.tail x hz)
  exact this

-- Helper: membership in domList corresponds to successful lookup
-- This relates the list-based domList to the map's lookup function
theorem mem_domList_iff_lookup {σ : Subst} {x : String} :
    x ∈ Subst.domList σ ↔ ∃ e, Subst.lookup σ x = some e := by
  simp only [Subst.domList, Subst.lookup]
  rw [List.mem_map]
  constructor
  · intro ⟨⟨k, v⟩, hmem', heq⟩
    simp at heq
    subst heq
    have h := (FiniteMapLaws.elem_of_map_to_list (M := SubstMap) (K := String) (V := Expr) σ k v).mp hmem'
    exact ⟨v, h⟩
  · intro ⟨e, he⟩
    have hmem : (x, e) ∈ (FiniteMap.toList (M := SubstMap) σ) :=
      (FiniteMapLaws.elem_of_map_to_list (M := SubstMap) (K := String) (V := Expr) σ x e).mpr he
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

-- Helper: delete operations commute when deleting different keys
theorem delete_delete_comm {σ : Subst} {x y : String} :
    x ≠ y → Subst.delete x (Subst.delete y σ) = Subst.delete y (Subst.delete x σ) := by
  intro _
  simp only [Subst.delete]
  exact FiniteMapLaws.delete_delete (M := SubstMap) (K := String) (V := Expr) σ y x

theorem lookup_insert_eq {σ : Subst} {x : String} {e : Expr} :
    (Subst.insert x e σ).lookup x = some e := by
  simp only [Subst.insert, Subst.lookup]
  exact FiniteMapLaws.lookup_insert_eq (M := SubstMap) (K := String) (V := Expr) σ x e

theorem lookup_insert_ne {σ : Subst} {x y : String} {e : Expr} (h : x ≠ y) :
    (Subst.insert y e σ).lookup x = σ.lookup x := by
  simp only [Subst.insert, Subst.lookup]
  exact FiniteMapLaws.lookup_insert_ne (M := SubstMap) (K := String) (V := Expr) σ y x e h.symm

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

-- TODO: Complete this proof
-- Corresponds to Coq's subst_closed_nil
-- Issue: Lean's `subst` definition differs from Coq's in how it handles binders
-- Strategy: May need to restructure the proof or adjust the definition
-- See parallel_subst.v (this lemma is used but not shown in the file)
theorem subst_closed_nil {x : String} {es : Expr} {e : Expr} :
    e.closed [] = true → subst x es e = e := by
  intro hclosed
  apply subst_closed_notmem hclosed
  simp

-- TODO: Complete this proof
-- Corresponds to Coq's subst_map_closed'_2
-- Strategy: Induction on e, for variables show either lookup succeeds (giving closed expr)
--           or lookup fails (so x must be in X). For lambdas, use IH with extended context.
-- See parallel_subst.v lines 178-189
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
      · -- Show e'.closed ((y :: X) ++ (σ.delete y).domList)
        apply closed_weaken hclosed
        intro z hz
        cases hz with
        | head =>
          -- z = y
          rw [List.mem_append]
          left
          apply List.Mem.head
        | tail _ hrest =>
          -- z ∈ X ++ σ.domList
          have : z ∈ X ∨ z ∈ σ.domList := List.mem_append.mp hrest
          rw [List.mem_append]
          cases this with
          | inl hx =>
            -- z ∈ X
            left
            apply List.Mem.tail
            exact hx
          | inr hdom =>
            -- z ∈ σ.domList
            by_cases heq : z = y
            · subst heq
              left
              apply List.Mem.head
            · right
              exact mem_domList_delete hdom heq
      · -- Show (σ.delete y).closed (y :: X)
        exact Subst.closed_delete_weaken hσclosed
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

-- TODO: Complete this proof
-- Corresponds to Coq's subst_subst_map
-- Key lemma showing interaction between normal substitution and parallel substitution
-- Strategy: Induction on e. For vars, use delete/insert properties and subst_closed_nil.
--           For lambdas, need to show delete/insert commute appropriately.
-- Requires: subst_closed_nil to be completed first
-- See parallel_subst.v lines 90-111
theorem subst_substMap_compose {x : String} {es : Expr} {θ : Subst} {e : Expr} :
    θ.closed [] →
    subst x es (substMap (θ.delete x) e) = substMap (Subst.insert x es θ) e := by
  intro hclosed
  induction e with
  | var y =>
    -- Variable case: need to consider whether y = x and whether y is in θ
    sorry
  | lam b e' ih =>
    cases b with
    | anon =>
      simp [substMap, subst]
      exact ih
    | named y =>
      simp [substMap, subst]
      split
      · next heq =>
        -- x = y case
        subst heq
        simp [Subst.delete, Subst.insert]
        congr 1
        -- Need to show: (θ.erase x).erase x = (θ.insert x es).erase x
        sorry
      · next hne =>
        -- ¬(x = y) case, need commutativity of erase/insert operations
        sorry
  | app e₁ e₂ ih₁ ih₂ =>
    simp [substMap, subst, ih₁, ih₂]
  | litInt n =>
    simp [substMap, subst]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [substMap, subst, ih₁, ih₂]

-- Helper: isSubSubstOf implies same values for common keys
-- This is a semantic property of substitution maps
-- NOTE: This requires isSubSubstOf to guarantee value equality, not just key membership
-- The current definition of isSubSubstOf may need to be strengthened
theorem lookup_of_isSubSubstOf {σ1 σ2 : Subst} {x : String} :
    σ1.isSubSubstOf σ2 → σ1.mem x →
    ∃ e, σ1.lookup x = some e ∧ σ2.lookup x = some e := by
  intro _ _
  -- We have σ1.get? x = some e
  -- We need to show σ2.get? x = some e
  -- But isSubSubstOf only guarantees x ∈ σ2, not that σ2[x] = σ1[x]
  -- This likely requires the definition of isSubSubstOf to be strengthened
  sorry

-- TODO: Complete this proof
-- Corresponds to Coq's subst_closed_weaken
-- Weakening lemma for closed substitutions
-- Strategy: Use closed_weaken and properties of isSubSubstOf
-- See parallel_subst.v lines 82-87
theorem substClosedWeaken {X Y: List String} {σ1 σ2 : Subst} :
    (∀ x, x ∈ Y → x ∈ X) →
    (σ1.isSubSubstOf σ2) →
    σ2.closed Y →
    σ1.closed X := by
  intro hsub hsub12 hclosed2
  unfold Subst.closed at *
  intro x e he1
  have hmem : σ1.mem x := by
    simp only [Subst.mem, Subst.lookup] at he1 ⊢
    simp [he1]
  have ⟨e', ⟨he1', he2'⟩⟩ := lookup_of_isSubSubstOf hsub12 hmem
  rw [he1'] at he1
  cases he1
  have := hclosed2 x e he2'
  exact STLC.closed_weaken this hsub

end STLC
