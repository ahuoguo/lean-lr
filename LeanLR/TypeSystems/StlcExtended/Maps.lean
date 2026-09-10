import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# Extended STLC: finite maps keyed by term variables

Typing contexts and simultaneous substitutions are both `Std.ExtTreeMap String _ compare`. Unlike
stdpp, which discharges map side conditions with `simplify_map_eq`, Lean needs these equations
stated; they are proved pointwise through `map_ext`.
-/

open Iris.Std

namespace StlcExtended

/-- Finite maps keyed by term variables. -/
abbrev MapStr (V : Type) := Std.ExtTreeMap String V compare

/-- The names a finite map binds. -/
def MapStr.domList {V : Type} (m : MapStr V) : List String :=
  (FiniteMap.toList (M := MapStr) m).map Prod.fst

/-- Substitutions agreeing at every key are equal. -/
theorem map_ext {V : Type} {m₁ m₂ : MapStr V}
    (h : ∀ k, get? (M := MapStr) m₁ k = get? (M := MapStr) m₂ k) : m₁ = m₂ :=
  LawfulPartialMap.equiv_iff_eq.mp h

theorem mem_domList_iff_lookup {V : Type} {m : MapStr V} {x : String} :
    x ∈ m.domList ↔ ∃ e, get? (M := MapStr) m x = some e := by
  simp only [MapStr.domList, List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, hmem, rfl⟩
    exact ⟨v, (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mp hmem⟩
  · rintro ⟨e, he⟩
    exact ⟨(x, e), (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr he, rfl⟩

theorem mem_domList_delete {V : Type} {m : MapStr V} {x y : String}
    (h : y ∈ (delete (M := MapStr) m x).domList) : y ∈ m.domList := by
  rw [mem_domList_iff_lookup] at h ⊢
  obtain ⟨e, he⟩ := h
  by_cases hxy : x = y
  · subst hxy
    rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at he
    exact absurd he (by simp)
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at he
    exact ⟨e, he⟩

theorem not_mem_domList_delete {V : Type} {m : MapStr V} {x : String} :
    x ∉ (delete (M := MapStr) m x).domList := by
  rw [mem_domList_iff_lookup]
  rintro ⟨e, he⟩
  rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at he
  exact absurd he (by simp)

/-- An insertion is invisible behind a deletion of the same key. -/
theorem delete_delete_insert {V : Type} (m : MapStr V) (x : String) (es : V) :
    delete (M := MapStr) (delete (M := MapStr) m x) x =
    delete (M := MapStr) (insert (M := MapStr) m x es) x := by
  refine map_ext fun k => ?_
  by_cases hkx : x = k
  · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hkx,
      LawfulPartialMap.get?_delete_eq (M := MapStr) hkx]
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
      LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
      LawfulPartialMap.get?_delete_ne (M := MapStr) hkx,
      LawfulPartialMap.get?_insert_ne (M := MapStr) hkx]

/-- Deletions at distinct keys commute. -/
theorem delete_delete_comm {V : Type} (m : MapStr V) {x y : String} (hxy : x ≠ y) :
    delete (M := MapStr) (delete (M := MapStr) m x) y =
    delete (M := MapStr) (delete (M := MapStr) m y) x := by
  refine map_ext fun k => ?_
  by_cases hyk : y = k <;> by_cases hxk : x = k
  · exact absurd (hxk.trans hyk.symm) hxy
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

/-- A deletion and an insertion at distinct keys commute. -/
theorem delete_insert_comm {V : Type} (m : MapStr V) (es : V) {x y : String} (hxy : x ≠ y) :
    delete (M := MapStr) (insert (M := MapStr) m x es) y =
    insert (M := MapStr) (delete (M := MapStr) m y) x es := by
  refine map_ext fun k => ?_
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

/-- Looking up an insertion. -/
theorem get?_insert {V : Type} (m : MapStr V) (x : String) (v : V) (k : String) :
    get? (M := MapStr) (insert (M := MapStr) m x v) k = if x = k then some v else
      get? (M := MapStr) m k := by
  by_cases h : x = k
  · subst h
    rw [if_pos rfl]
    exact LawfulPartialMap.get?_insert_eq (M := MapStr) rfl
  · rw [if_neg h]
    exact LawfulPartialMap.get?_insert_ne (M := MapStr) h

theorem mem_domList_insert {V : Type} {m : MapStr V} {x y : String} {v : V} :
    y ∈ (insert (M := MapStr) m x v).domList ↔ y = x ∨ y ∈ m.domList := by
  rw [mem_domList_iff_lookup]
  constructor
  · rintro ⟨e, he⟩
    rw [get?_insert] at he
    by_cases hxy : x = y
    · exact Or.inl hxy.symm
    · rw [if_neg hxy] at he
      exact Or.inr (mem_domList_iff_lookup.mpr ⟨e, he⟩)
  · rintro (rfl | h)
    · exact ⟨v, by rw [get?_insert, if_pos rfl]⟩
    · obtain ⟨e, he⟩ := mem_domList_iff_lookup.mp h
      by_cases hxy : x = y
      · exact ⟨v, by rw [get?_insert, if_pos hxy]⟩
      · exact ⟨e, by rw [get?_insert, if_neg hxy]; exact he⟩

/-- Deleting a key discards an insertion at that key. -/
theorem delete_insert_eq {V : Type} (m : MapStr V) (x : String) (v : V) :
    delete (M := MapStr) (insert (M := MapStr) m x v) x = delete (M := MapStr) m x := by
  refine map_ext fun k => ?_
  by_cases hxk : x = k
  · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hxk,
      LawfulPartialMap.get?_delete_eq (M := MapStr) hxk]
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
      LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
      LawfulPartialMap.get?_insert_ne (M := MapStr) hxk]

end StlcExtended
