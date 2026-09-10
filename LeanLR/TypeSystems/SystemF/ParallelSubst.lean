import LeanLR.TypeSystems.SystemF.Lang

import Iris.Std.PartialMap
import Iris.Std.HeapInstances

/-!
# System F: parallel substitution

`substMap` substitutes a whole finite map of expressions at once. The main results relate it to the
single-variable `subst` of `Lang.lean` and characterise when its result is closed.
-/

open Iris.Std

namespace SystemF

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

/-- Deleting from the empty substitution changes nothing. -/
private theorem binderDelete_empty (b : Binder) :
    binderDelete b (PartialMap.empty (M := MapStr) (V := Expr)) =
    PartialMap.empty (M := MapStr) (V := Expr) := by
  cases b with
  | bAnon => rfl
  | bNamed x =>
    exact LawfulPartialMap.delete_empty (M := MapStr)

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
  | injL _ ih | injR _ ih =>
    exact ih hclosed hsub
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨⟨ih₀ hclosed.1.1 hsub, ih₁ hclosed.1.2 hsub⟩, ih₂ hclosed.2 hsub⟩

/-- Substituting a variable the expression does not have free is a no-op. -/
theorem subst_closed_notmem {x : String} {es e : Expr} {X : List String}
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
  | injL _ ih | injR _ ih =>
    simp only [closed, Expr.isClosed] at hclosed
    unfold subst
    congr 1
    exact ih hclosed hnotmem
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
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
theorem subst_closed_nil {x : String} {es e : Expr} (hclosed : closed [] e) :
    subst x es e = e :=
  subst_closed_notmem hclosed (by simp)

/-! ## Closedness of the result of a substitution

`lang.v`'s `is_closed_subst` group. These are about closedness of the *result* of a substitution,
unlike `subst_closed_notmem` above, which says the substitution is a no-op. -/

theorem closed_weaken_nil {X : List String} {e : Expr} (h : closed [] e) : closed X e :=
  closed_weaken h (by simp)

/-- In Lean `closed` is *defined* as the `Bool` being `true`, so the
two forms are the same statement. -/
theorem closed_is_closed {X : List String} {e : Expr} : e.isClosed X = true ↔ closed X e :=
  Iff.rfl

/-- A binder can be moved past the variable being substituted for. -/
private theorem closed_swap_binder {b : Binder} {x : String} {X : List String} {e : Expr}
    (he : closed (b :b: (x :: X)) e) : closed (x :: (b :b: X)) e := by
  cases b with
  | bAnon => exact he
  | bNamed y =>
    refine closed_weaken he fun z hz => ?_
    simp only [Binder.cons, List.mem_cons] at hz ⊢
    rcases hz with hz | hz | hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inl hz
    · exact Or.inr (Or.inr hz)

/-- A binder that shadows the variable being substituted for absorbs it. -/
private theorem closed_shadow_binder {x : String} {X : List String} {e : Expr}
    (he : closed (Binder.bNamed x :b: (x :: X)) e) : closed (Binder.bNamed x :b: X) e := by
  refine closed_weaken he fun z hz => ?_
  simp only [Binder.cons, List.mem_cons] at hz ⊢
  rcases hz with hz | hz | hz
  · exact Or.inl hz
  · exact Or.inl hz
  · exact Or.inr hz

/-- Substituting a closed expression for `x` in an `x :: X`-closed expression gives an `X`-closed
expression. -/
theorem closed_subst {X : List String} {e es : Expr} {x : String}
    (hes : closed [] es) (he : closed (x :: X) e) : closed X (subst x es e) := by
  induction e generalizing X with
  | lit _ => rfl
  | var y =>
    simp only [subst]
    split
    · exact closed_weaken hes (by simp)
    · rename_i hne
      simp only [closed, Expr.isClosed, decide_eq_true_eq, List.mem_cons] at he ⊢
      exact he.resolve_left fun h => hne h.symm
  | lam b e ih =>
    simp only [subst, closed, Expr.isClosed] at he ⊢
    split
    · rename_i heq
      subst heq
      exact closed_shadow_binder he
    · exact ih (closed_swap_binder he)
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [subst, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    refine ⟨ih₁ he.1, ?_⟩
    split
    · rename_i heq
      subst heq
      exact closed_shadow_binder he.2
    · exact ih₂ (closed_swap_binder he.2)
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [subst, closed, Expr.isClosed] at he ⊢
    exact ih he
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [subst, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1, ih₂ he.2⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [subst, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ he.1.1, ih₁ he.1.2⟩, ih₂ he.2⟩

/-- The binder-lifted form of `closed_subst`. -/
theorem closed_do_subst' {X : List String} {e es : Expr} {b : Binder}
    (hes : closed [] es) (he : closed (b :b: X) e) : closed X (subst' b es e) := by
  cases b with
  | bAnon => exact he
  | bNamed x => exact closed_subst hes he

/-- The binder-lifted form of `subst_closed_nil`. -/
theorem subst'_closed_nil {b : Binder} {es e : Expr} (hclosed : closed [] e) :
    subst' b es e = e := by
  cases b with
  | bAnon => rfl
  | bNamed x => exact subst_closed_nil hclosed

/-! ## Map algebra

The equations `subst_substMap` needs to move a deletion past the insertion it competes with. Each
is proved pointwise through `map_ext`. -/

/-- Substitutions agreeing at every key are equal. -/
private theorem map_ext {m₁ m₂ : SubstMap}
    (h : ∀ k, get? (M := MapStr) m₁ k = get? (M := MapStr) m₂ k) : m₁ = m₂ :=
  LawfulPartialMap.equiv_iff_eq.mp h

/-- An insertion is invisible behind a deletion of the same key. -/
theorem delete_delete_insert (m : SubstMap) (x : String) (es : Expr) :
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

/-- Deleting a key discards an insertion at that key. -/
theorem delete_insert_eq (m : SubstMap) (x : String) (es : Expr) :
    delete (M := MapStr) (insert (M := MapStr) m x es) x = delete (M := MapStr) m x := by
  refine map_ext fun k => ?_
  by_cases hxk : x = k
  · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hxk,
      LawfulPartialMap.get?_delete_eq (M := MapStr) hxk]
  · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
      LawfulPartialMap.get?_delete_ne (M := MapStr) hxk,
      LawfulPartialMap.get?_insert_ne (M := MapStr) hxk]

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
theorem delete_insert_comm (m : SubstMap) (es : Expr) {x y : String} (hxy : x ≠ y) :
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
  | injL _ ih | injR _ ih =>
    simp only [substMap, subst]
    congr 1
    exact ih m hclosed
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
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
  | injL _ ih | injR _ ih =>
    exact ih θ Y hθ hcov
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
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
  | injL _ ih | injR _ ih =>
    exact ih θ Y hcov
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    exact ⟨ih₁ θ Y hcov, ih₂ θ Y hcov⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    exact ⟨ih₀ θ Y hcov, ih₁ θ Y hcov, ih₂ θ Y hcov⟩

/-! ## The `parallel_subst.v` remainder

The lemmas relating a parallel substitution to closedness and to a single substitution that the
rest of the chapter does not itself need, but which `parallel_subst.v` states. -/

theorem substIsClosed_weaken {X Y : List String} {θ : SubstMap} (hθ : substIsClosed X θ)
    (hsub : ∀ x, x ∈ X → x ∈ Y) : substIsClosed Y θ :=
  fun x e he => closed_weaken (hθ x e he) hsub

theorem substIsClosed_weaken_nil {X : List String} {θ : SubstMap} (hθ : substIsClosed [] θ) :
    substIsClosed X θ :=
  substIsClosed_weaken hθ (by simp)

/-- With `gmap` inclusion spelled out pointwise. -/
theorem substIsClosed_subseteq {X : List String} {θ₁ θ₂ : SubstMap}
    (hsub : ∀ x e, get? (M := MapStr) θ₁ x = some e → get? (M := MapStr) θ₂ x = some e)
    (hθ₂ : substIsClosed X θ₂) : substIsClosed X θ₁ :=
  fun x e he => hθ₂ x e (hsub x e he)

theorem substIsClosed_insert {X : List String} {θ : SubstMap} {f : String} {e : Expr}
    (he : closed X e) (hθ : substIsClosed X (delete (M := MapStr) θ f)) :
    substIsClosed X (insert (M := MapStr) θ f e) := by
  intro x e' hx
  by_cases hfx : f = x
  · rw [LawfulPartialMap.get?_insert_eq (M := MapStr) hfx] at hx
    injection hx with hx
    exact hx ▸ he
  · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hfx] at hx
    exact hθ x e' (by rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hfx])

/-- Descending under a binder keeps the substitution's domain away from the permitted variables. -/
private theorem binderDelete_avoids {X : List String} {θ : SubstMap} (b : Binder)
    (hdom : ∀ x, get? (M := MapStr) θ x ≠ none → x ∉ X) :
    ∀ x, get? (M := MapStr) (binderDelete b θ) x ≠ none → x ∉ (b :b: X) := by
  cases b with
  | bAnon => exact hdom
  | bNamed y =>
    intro x hx hmem
    simp only [Binder.cons, List.mem_cons] at hmem
    by_cases hyx : y = x
    · rw [binderDelete, LawfulPartialMap.get?_delete_eq (M := MapStr) hyx] at hx
      exact hx rfl
    · rw [binderDelete, LawfulPartialMap.get?_delete_ne (M := MapStr) hyx] at hx
      exact hdom x hx (hmem.resolve_left fun h => hyx h.symm)

/-- A substitution whose domain avoids the free variables of `e`
does nothing. -/
theorem substMap_is_closed {X : List String} {θ : SubstMap} {e : Expr} (he : closed X e)
    (hdom : ∀ x, get? (M := MapStr) θ x ≠ none → x ∉ X) : substMap θ e = e := by
  induction e generalizing X θ with
  | lit _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    simp only [substMap]
    cases hget : get? (M := MapStr) θ y with
    | none => rfl
    | some e' => exact absurd he (hdom y (by rw [hget]; simp))
  | lam b e ih =>
    simp only [closed, Expr.isClosed] at he
    simp only [substMap]
    rw [ih he (binderDelete_avoids b hdom)]
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at he
    simp only [substMap]
    rw [ih₁ he.1 hdom, ih₂ he.2 (binderDelete_avoids b hdom)]
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih =>
    simp only [closed, Expr.isClosed] at he
    simp only [substMap]
    rw [ih he hdom]
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at he
    simp only [substMap]
    rw [ih₁ he.1 hdom, ih₂ he.2 hdom]
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at he
    simp only [substMap]
    rw [ih₀ he.1.1 hdom, ih₁ he.1.2 hdom, ih₂ he.2 hdom]

/-- A single substitution in front of a parallel one is an insertion. -/
theorem substMap_subst {θ : SubstMap} {x : String} {e es : Expr} (hes : closed [] es) :
    substMap θ (subst x es e) = substMap (insert (M := MapStr) θ x es) e := by
  induction e generalizing θ with
  | lit _ => rfl
  | var y =>
    simp only [subst, substMap]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
      exact substMap_is_closed hes (fun _ _ => by simp)
    · rw [if_neg hxy]
      simp only [substMap]
      rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
  | lam b e ih =>
    cases b with
    | bAnon =>
      simp only [subst]
      rw [if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))]
      simp only [substMap, binderDelete]
      rw [ih]
    | bNamed y =>
      by_cases hxy : x = y
      · subst hxy
        simp only [subst, if_true]
        simp only [substMap, binderDelete]
        rw [delete_insert_eq θ x es]
      · simp only [subst]
        rw [if_neg (fun h => hxy (by cases h; rfl))]
        simp only [substMap, binderDelete]
        rw [ih, delete_insert_comm θ es hxy]
  | unpack b e₁ e₂ ih₁ ih₂ =>
    cases b with
    | bAnon =>
      simp only [subst]
      rw [if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))]
      simp only [substMap, binderDelete]
      rw [ih₁, ih₂]
    | bNamed y =>
      by_cases hxy : x = y
      · subst hxy
        simp only [subst, if_true]
        simp only [substMap, binderDelete]
        rw [ih₁, delete_insert_eq θ x es]
      · simp only [subst]
        rw [if_neg (fun h => hxy (by cases h; rfl))]
        simp only [substMap, binderDelete]
        rw [ih₁, ih₂, delete_insert_comm θ es hxy]
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih =>
    simp only [subst, substMap]
    rw [ih]
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [subst, substMap]
    rw [ih₁, ih₂]
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [subst, substMap]
    rw [ih₀, ih₁, ih₂]

/-- Descending under a binder preserves closedness of the range at the empty variable list. -/
private theorem substIsClosed_binderDelete_nil (b : Binder) (θ : SubstMap)
    (hθ : substIsClosed [] θ) : substIsClosed [] (binderDelete b θ) := by
  cases b with
  | bAnon => exact hθ
  | bNamed z => exact substIsClosed_delete z hθ

/-- The coverage side condition of `closed_subst_weaken` descends under a binder. -/
private theorem binderDelete_sub {X Y : List String} {θ : SubstMap} (b : Binder)
    (hsub : ∀ x, x ∈ X → get? (M := MapStr) θ x = none → x ∈ Y) :
    ∀ x, x ∈ (b :b: X) → get? (M := MapStr) (binderDelete b θ) x = none → x ∈ (b :b: Y) := by
  cases b with
  | bAnon => exact hsub
  | bNamed z =>
    intro x hx hget
    simp only [Binder.cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · by_cases hzx : z = x
      · exact Or.inl hzx.symm
      · rw [binderDelete, LawfulPartialMap.get?_delete_ne (M := MapStr) hzx] at hget
        exact Or.inr (hsub x hx hget)

/-- Substituting a closed map turns `X`-closedness into
`Y`-closedness, provided every `X`-variable the map does not cover is already in `Y`. -/
theorem closed_subst_weaken {X Y : List String} {θ : SubstMap} {e : Expr}
    (hθ : substIsClosed [] θ)
    (hsub : ∀ x, x ∈ X → get? (M := MapStr) θ x = none → x ∈ Y)
    (he : closed X e) : closed Y (substMap θ e) := by
  induction e generalizing X Y θ with
  | lit _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    simp only [substMap]
    cases hget : get? (M := MapStr) θ y with
    | none =>
      simp only [closed, Expr.isClosed, decide_eq_true_eq]
      exact hsub y he hget
    | some e' => exact closed_weaken_nil (hθ y e' hget)
  | lam b e ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih (substIsClosed_binderDelete_nil b θ hθ) (binderDelete_sub b hsub) he
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ hθ hsub he.1,
      ih₂ (substIsClosed_binderDelete_nil b θ hθ) (binderDelete_sub b hsub) he.2⟩
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih hθ hsub he
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ hθ hsub he.1, ih₂ hθ hsub he.2⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ hθ hsub he.1.1, ih₁ hθ hsub he.1.2⟩, ih₂ hθ hsub he.2⟩

/-- The names the substitution binds. -/
def SubstMap.domList (θ : SubstMap) : List String :=
  (FiniteMap.toList (M := MapStr) θ).map Prod.fst

theorem mem_domList_iff_lookup {θ : SubstMap} {x : String} :
    x ∈ θ.domList ↔ ∃ e, get? (M := MapStr) θ x = some e := by
  simp only [SubstMap.domList, List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, hmem, rfl⟩
    exact ⟨v, (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mp hmem⟩
  · rintro ⟨e, he⟩
    exact ⟨(x, e), (LawfulFiniteMap.toList_get (M := MapStr) (K := String)).mpr he, rfl⟩

/-- The coverage criterion of `substMap_closed'` descends under a binder. -/
private theorem binderDelete_cov {X Y : List String} {θ : SubstMap} (b : Binder)
    (hcov : ∀ x, x ∈ Y → match get? (M := MapStr) θ x with
      | some e' => closed X e'
      | none => x ∈ X) :
    ∀ x, x ∈ (b :b: Y) → match get? (M := MapStr) (binderDelete b θ) x with
      | some e' => closed (b :b: X) e'
      | none => x ∈ (b :b: X) := by
  cases b with
  | bAnon => exact hcov
  | bNamed z =>
    intro x hx
    simp only [Binder.cons, List.mem_cons] at hx
    by_cases hzx : z = x
    · subst hzx
      rw [binderDelete, LawfulPartialMap.get?_delete_eq (M := MapStr) rfl]
      exact List.Mem.head _
    · rw [binderDelete, LawfulPartialMap.get?_delete_ne (M := MapStr) hzx]
      have hy := hcov x (hx.resolve_left fun h => hzx h.symm)
      cases hget : get? (M := MapStr) θ x with
      | none =>
        rw [hget] at hy
        exact List.Mem.tail _ hy
      | some e' =>
        rw [hget] at hy
        exact closed_weaken hy fun w hw => List.Mem.tail _ hw

/-- Every free variable of `e` is either substituted by an `X`-closed
expression or already in `X`. -/
theorem substMap_closed' {X Y : List String} {θ : SubstMap} {e : Expr} (he : closed Y e)
    (hcov : ∀ x, x ∈ Y → match get? (M := MapStr) θ x with
      | some e' => closed X e'
      | none => x ∈ X) : closed X (substMap θ e) := by
  induction e generalizing X Y θ with
  | lit _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    have hy := hcov y he
    simp only [substMap]
    cases hget : get? (M := MapStr) θ y with
    | none =>
      rw [hget] at hy
      simpa [closed, Expr.isClosed] using hy
    | some e' =>
      rw [hget] at hy
      exact hy
  | lam b e ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih he (binderDelete_cov b hcov)
  | unpack b e₁ e₂ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1 hcov, ih₂ he.2 (binderDelete_cov b hcov)⟩
  | unOp _ _ ih | tApp _ ih | tLam _ ih | pack _ ih | fst _ ih | snd _ ih
  | injL _ ih | injR _ ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih he hcov
  | app _ _ ih₁ ih₂ | binOp _ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1 hcov, ih₂ he.2 hcov⟩
  | ite _ _ _ ih₀ ih₁ ih₂ | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ he.1.1 hcov, ih₁ he.1.2 hcov⟩, ih₂ he.2 hcov⟩

/-- Rocq's `subst_map_closed` (`subst_map_closed'_2` in the STLC chapters): the corollary of
`substMap_closed'` in which the extra variables are exactly the substitution's domain. -/
theorem substMap_closed {X : List String} {θ : SubstMap} {e : Expr}
    (he : closed (X ++ θ.domList) e) (hθ : substIsClosed X θ) : closed X (substMap θ e) := by
  refine substMap_closed' he fun x hx => ?_
  cases hget : get? (M := MapStr) θ x with
  | none =>
    rcases List.mem_append.mp hx with h | h
    · exact h
    · obtain ⟨e', he'⟩ := mem_domList_iff_lookup.mp h
      rw [hget] at he'
      exact absurd he' (by simp)
  | some e' => exact hθ x e' hget

end SystemF
