import LeanLR.TypeSystems.SystemFMuState.Lang

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# System F with recursive types and mutable state: parallel substitution

`substMap` substitutes a whole finite map of expressions at once. The main results relate it to the
single-variable `subst` of `Lang.lean` and characterise when its result is closed.
-/

open Iris.Std

namespace SystemFMuState

/-! ## Parallel substitution -/

/-- Finite maps keyed by term variables. -/
abbrev MapStr (V : Type) := Std.ExtTreeMap String V compare

/-- A simultaneous substitution: what to put in place of each term variable. -/
abbrev SubstMap := MapStr Expr

/-- Removes a binder's variable from a substitution, so that the binder shadows it. The anonymous
binder shadows nothing. -/
def binderDelete (b : Binder) (m : SubstMap) : SubstMap :=
  match b with
  | .bAnon => m
  | .bNamed x => delete (M := MapStr) m x

/-- `substMap xs e` replaces every free term variable of `e` that `xs` maps, all at once. -/
def substMap (xs : SubstMap) : Expr → Expr
  | .lit l => .lit l
  | .var y => match get? (M := MapStr) xs y with | some es => es | none => .var y
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

/-- Deleting from the empty substitution changes nothing. -/
private theorem binderDelete_empty (b : Binder) :
    binderDelete b (PartialMap.empty (M := MapStr) (V := Expr)) =
    PartialMap.empty (M := MapStr) (V := Expr) := by
  cases b with
  | bAnon => rfl
  | bNamed x =>
    exact ExtensionalPartialMap.equiv_iff_eq.mp (LawfulPartialMap.delete_empty (M := MapStr))

/-- The empty substitution acts as the identity. -/
theorem substMap_empty (e : Expr) :
    substMap (PartialMap.empty (M := MapStr) (V := Expr)) e = e := by
  have hget : ∀ y, get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) y = none :=
    LawfulPartialMap.get?_empty (M := MapStr)
  induction e <;> simp_all [substMap, binderDelete_empty]

/-! ## Closedness -/

/-- `substIsClosed X m` says every expression in the range of `m` is `X`-closed. -/
def substIsClosed (X : List String) (m : SubstMap) : Prop :=
  ∀ x e, get? (M := MapStr) m x = some e → closed X e

/-- Extending the variable list preserves closedness under a binder. -/
private theorem cons_subset {b : Binder} {X Y : List String}
    (hsub : ∀ x, x ∈ X → x ∈ Y) : ∀ x, x ∈ (b :b: X) → x ∈ (b :b: Y) := by
  cases b with
  | bAnon => exact hsub
  | bNamed y =>
    intro z hz
    cases hz with
    | head => exact .head _
    | tail _ hz' => exact .tail _ (hsub z hz')

/-- Closedness is monotone in the list of permitted variables. -/
theorem closed_weaken {X Y : List String} {e : Expr}
    (hclosed : closed X e) (hsub : ∀ x, x ∈ X → x ∈ Y) : closed Y e := by
  induction e generalizing X Y with
  | lit _ => rfl
  | var x =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at hclosed ⊢
    exact hsub x hclosed
  | lam _ _ ih => exact ih hclosed (cons_subset hsub)
  | unpack _ _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 (cons_subset hsub)⟩
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih | roll _ ih | unroll _ ih | load _ ih | new _ ih =>
    exact ih hclosed hsub
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨⟨ih₀ hclosed.1.1 hsub, ih₁ hclosed.1.2 hsub⟩, ih₂ hclosed.2 hsub⟩

/-- Substituting a variable the expression does not have free is a no-op. -/
private theorem subst_closed_notmem {x : String} {es e : Expr} {X : List String}
    (hclosed : closed X e) (hnotmem : x ∉ X) : subst x es e = e := by
  induction e generalizing X with
  | lit _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at hclosed
    have hne : x ≠ y := fun heq => hnotmem (heq ▸ hclosed)
    simp [subst, hne]
  | lam b e' ih =>
    simp only [closed, Expr.isClosed] at hclosed
    refine congrArg (Expr.lam b) ?_
    cases b with
    | bAnon => exact ih hclosed hnotmem
    | bNamed y =>
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [Binder.cons] at hclosed
        rw [if_neg fun h => hxy (by cases h; rfl)]
        exact ih hclosed fun hmem => by
          cases hmem with
          | head => exact hxy rfl
          | tail _ hmem' => exact hnotmem hmem'
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst
    congr 1
    · exact ih₁ hclosed.1 hnotmem
    · cases b with
      | bAnon => exact ih₂ hclosed.2 hnotmem
      | bNamed y =>
        by_cases hxy : x = y
        · simp [hxy]
        · simp only [Binder.cons] at hclosed
          rw [if_neg fun h => hxy (by cases h; rfl)]
          exact ih₂ hclosed.2 fun hmem => by
            cases hmem with
            | head => exact hxy rfl
            | tail _ hmem' => exact hnotmem hmem'
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih | roll _ ih | unroll _ ih | load _ ih | new _ ih =>
    simp only [closed, Expr.isClosed] at hclosed
    unfold subst
    congr 1
    exact ih hclosed hnotmem
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst
    congr 1
    · exact ih₁ hclosed.1 hnotmem
    · exact ih₂ hclosed.2 hnotmem
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed
    unfold subst
    congr 1
    · exact ih₀ hclosed.1.1 hnotmem
    · exact ih₁ hclosed.1.2 hnotmem
    · exact ih₂ hclosed.2 hnotmem

/-- Substitution into a closed expression is a no-op. -/
private theorem subst_closed_nil {x : String} {es e : Expr} (hclosed : closed [] e) :
    subst x es e = e :=
  subst_closed_notmem hclosed (by simp)

/-! ## Map algebra

The equations `subst_substMap` needs to move a deletion past the insertion it competes with. Each
is proved pointwise through `map_ext`. -/

/-- Substitutions agreeing at every key are equal. -/
private theorem map_ext {m₁ m₂ : SubstMap}
    (h : ∀ k, get? (M := MapStr) m₁ k = get? (M := MapStr) m₂ k) : m₁ = m₂ :=
  ExtensionalPartialMap.equiv_iff_eq.mp h

/-- An insertion is invisible behind a deletion of the same key. -/
private theorem delete_delete_insert (m : SubstMap) (x : String) (es : Expr) :
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
private theorem delete_delete_comm (m : SubstMap) {x y : String} (hxy : x ≠ y) :
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
private theorem delete_insert_comm (m : SubstMap) (es : Expr) {x y : String} (hxy : x ≠ y) :
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

/-- Deleting a key preserves closedness of the range. -/
private theorem substIsClosed_delete {X : List String} {m : SubstMap} (y : String)
    (hm : substIsClosed X m) : substIsClosed X (delete (M := MapStr) m y) := by
  intro z ez hlz
  refine hm z ez ?_
  by_cases hyz : y = z
  · subst hyz
    rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hlz
    exact absurd hlz (by simp)
  · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hyz] at hlz

/-! ## Relating `substMap` to `subst` -/

/-- Substituting `x` after the map, or inserting `x` into the map, agree — provided the map's range
is closed, so that the outer `subst x` cannot reach into a substituted expression.

Both binder cases split on whether the binder shadows `x`. If it does, the insertion is discarded
(`delete_delete_insert`); otherwise the deletion of the binder commutes past both the deletion and
the insertion of `x` (`delete_delete_comm`, `delete_insert_comm`) and the induction hypothesis
applies at the smaller map. -/
theorem subst_substMap (x : String) (es : Expr) (m : SubstMap) (e : Expr)
    (hclosed : substIsClosed [] m) :
    subst x es (substMap (delete (M := MapStr) m x) e) =
    substMap (insert (M := MapStr) m x es) e := by
  induction e generalizing m with
  | lit _ => rfl
  | var y =>
    simp only [substMap]
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl,
        LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
      simp [subst]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy,
        LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      cases hget : get? (M := MapStr) m y with
      | none => simp [subst, hxy]
      | some e' => exact subst_closed_nil (hclosed y e' hget)
  | lam b e' ih =>
    cases b with
    | bAnon =>
      simp only [substMap, binderDelete, subst]
      exact congrArg _ (ih m hclosed)
    | bNamed y =>
      simp only [substMap, binderDelete, subst]
      refine congrArg (Expr.lam (.bNamed y)) ?_
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, delete_delete_insert]
      · rw [if_neg fun h => hxy (by cases h; rfl), delete_delete_comm m hxy,
          delete_insert_comm m es hxy]
        exact ih _ (substIsClosed_delete y hclosed)
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, subst]
    congr 1
    · exact ih₁ m hclosed
    · cases b with
      | bAnon => exact ih₂ m hclosed
      | bNamed y =>
        simp only [binderDelete]
        by_cases hxy : x = y
        · subst hxy
          rw [if_pos rfl, delete_delete_insert]
        · rw [if_neg fun h => hxy (by cases h; rfl), delete_delete_comm m hxy,
            delete_insert_comm m es hxy]
          exact ih₂ _ (substIsClosed_delete y hclosed)
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih | roll _ ih | unroll _ ih | load _ ih | new _ ih =>
    simp only [substMap, subst]
    congr 1
    exact ih m hclosed
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ =>
    simp only [substMap, subst]
    congr 1
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, subst]
    congr 1
    · exact ih₀ m hclosed
    · exact ih₁ m hclosed
    · exact ih₂ m hclosed

/-- `subst_substMap` for an arbitrary binder; the anonymous binder substitutes nothing. -/
theorem subst'_substMap (b : Binder) (es : Expr) (m : SubstMap) (e : Expr)
    (hclosed : substIsClosed [] m) :
    subst' b es (substMap (binderDelete b m) e) =
    substMap (match b with | .bAnon => m | .bNamed x => insert (M := MapStr) m x es) e := by
  cases b with
  | bAnon => simp [subst', binderDelete]
  | bNamed x => exact subst_substMap x es m e hclosed

/-! ## Closedness of the result -/

/-- `closedModulo θ Y e` says every free variable of `e` is either in `Y` or substituted by `θ`.
This is `Expr.isClosed` relaxed to also permit variables that `θ` covers. -/
def closedModulo (θ : SubstMap) (Y : List String) : Expr → Prop
  | .lit _ => True
  | .var y => y ∈ Y ∨ get? (M := MapStr) θ y ≠ none
  | .lam b e => closedModulo (binderDelete b θ) (b :b: Y) e
  | .app e₁ e₂ => closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .unOp _ e => closedModulo θ Y e
  | .binOp _ e₁ e₂ => closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .ite e₀ e₁ e₂ => closedModulo θ Y e₀ ∧ closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .tApp e => closedModulo θ Y e
  | .tLam e => closedModulo θ Y e
  | .pack e => closedModulo θ Y e
  | .unpack b e₁ e₂ => closedModulo θ Y e₁ ∧ closedModulo (binderDelete b θ) (b :b: Y) e₂
  | .pair e₁ e₂ => closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .fst e => closedModulo θ Y e
  | .snd e => closedModulo θ Y e
  | .injL e => closedModulo θ Y e
  | .injR e => closedModulo θ Y e
  | .case e₀ e₁ e₂ => closedModulo θ Y e₀ ∧ closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .roll e => closedModulo θ Y e
  | .unroll e => closedModulo θ Y e
  | .load e => closedModulo θ Y e
  | .store e₁ e₂ => closedModulo θ Y e₁ ∧ closedModulo θ Y e₂
  | .new e => closedModulo θ Y e

/-- Descending under a binder preserves closedness of the substitution's range. -/
theorem substIsClosed_binderDelete (b : Binder) (θ : SubstMap) (Y : List String) :
    substIsClosed Y θ → substIsClosed (b :b: Y) (binderDelete b θ) := by
  intro hθ x e hget
  cases b with
  | bAnon => exact hθ x e hget
  | bNamed name =>
    exact closed_weaken (substIsClosed_delete name hθ x e hget) fun y hy => .tail _ hy

/-- `substMap θ e` is `Y`-closed as soon as `θ`'s range is `Y`-closed and `θ` covers every free
variable of `e` outside `Y`. -/
theorem substMap_closed_of_closedModulo (θ : SubstMap) (Y : List String) (e : Expr)
    (hθ : substIsClosed Y θ) (hcov : closedModulo θ Y e) : closed Y (substMap θ e) := by
  induction e generalizing θ Y with
  | lit _ => rfl
  | var y =>
    simp only [substMap]
    cases hget : get? (M := MapStr) θ y with
    | some v => exact hθ y v hget
    | none =>
      simp only [closedModulo, hget, ne_eq, not_true_eq_false, or_false] at hcov
      simpa [closed, Expr.isClosed] using hcov
  | lam b _ ih => exact ih _ _ (substIsClosed_binderDelete b θ Y hθ) hcov
  | unpack b _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ θ Y hθ hcov.1, ih₂ _ _ (substIsClosed_binderDelete b θ Y hθ) hcov.2⟩
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih | roll _ ih | unroll _ ih | load _ ih | new _ ih =>
    exact ih θ Y hθ hcov
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ih₁ θ Y hθ hcov.1, ih₂ θ Y hθ hcov.2⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨⟨ih₀ θ Y hθ hcov.1, ih₁ θ Y hθ hcov.2.1⟩, ih₂ θ Y hθ hcov.2.2⟩

/-- Descending under a binder preserves coverage of the variables outside `Y`. -/
private theorem coverage_binderDelete {b : Binder} {θ : SubstMap} {Y : List String}
    (hcov : ∀ y, y ∉ Y → get? (M := MapStr) θ y ≠ none) :
    ∀ y, y ∉ (b :b: Y) → get? (M := MapStr) (binderDelete b θ) y ≠ none := by
  cases b with
  | bAnon => exact hcov
  | bNamed name =>
    intro y hnotmem
    simp only [Binder.cons, List.mem_cons, not_or] at hnotmem
    rw [binderDelete, LawfulPartialMap.get?_delete_ne (M := MapStr) fun h => hnotmem.1 h.symm]
    exact hcov y hnotmem.2

/-- A substitution covering every variable outside `Y` makes every expression `closedModulo`. -/
theorem closedModulo_of_coverage (θ : SubstMap) (Y : List String) (e : Expr)
    (hcov : ∀ y, y ∉ Y → get? (M := MapStr) θ y ≠ none) : closedModulo θ Y e := by
  induction e generalizing θ Y with
  | lit _ => exact trivial
  | var y =>
    by_cases hy : y ∈ Y
    · exact .inl hy
    · exact .inr (hcov y hy)
  | lam _ _ ih => exact ih _ _ (coverage_binderDelete hcov)
  | unpack _ _ _ ih₁ ih₂ => exact ⟨ih₁ θ Y hcov, ih₂ _ _ (coverage_binderDelete hcov)⟩
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih | roll _ ih | unroll _ ih | load _ ih | new _ ih =>
    exact ih θ Y hcov
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ =>
    exact ⟨ih₁ θ Y hcov, ih₂ θ Y hcov⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    exact ⟨ih₀ θ Y hcov, ih₁ θ Y hcov, ih₂ θ Y hcov⟩

end SystemFMuState
