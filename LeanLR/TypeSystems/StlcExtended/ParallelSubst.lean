import LeanLR.TypeSystems.StlcExtended.Lang
import LeanLR.TypeSystems.StlcExtended.Maps

/-!
# Extended STLC: parallel substitution

`substMap` substitutes a whole finite map of expressions at once. The main results relate it to the
single-variable `subst` of `Lang.lean` and characterise when its result is closed.
-/

open Iris.Std

namespace StlcExtended

/-! ## Parallel substitution -/

/-- A simultaneous substitution: what to put in place of each term variable. -/
abbrev SubstMap := MapStr Expr

/-- Removes a binder's variable from a substitution, so that the binder shadows it. The anonymous
binder shadows nothing. -/
def binderDelete (b : Binder) (m : SubstMap) : SubstMap :=
  match b with
  | .bAnon => m
  | .bNamed x => delete (M := MapStr) m x

/-- Applies a simultaneous substitution. -/
def substMap (xs : SubstMap) : Expr → Expr
  | .litInt n => .litInt n
  | .var y => match get? (M := MapStr) xs y with | some es => es | none => .var y
  | .lam x e => .lam x (substMap (binderDelete x xs) e)
  | .app e₁ e₂ => .app (substMap xs e₁) (substMap xs e₂)
  | .plus e₁ e₂ => .plus (substMap xs e₁) (substMap xs e₂)
  | .pair e₁ e₂ => .pair (substMap xs e₁) (substMap xs e₂)
  | .fst e => .fst (substMap xs e)
  | .snd e => .snd (substMap xs e)
  | .injL e => .injL (substMap xs e)
  | .injR e => .injR (substMap xs e)
  | .case e₀ e₁ e₂ => .case (substMap xs e₀) (substMap xs e₁) (substMap xs e₂)

/-! ## Closedness of substitutions -/

/-- `substIsClosed X m` says every expression in the range of `m` is `X`-closed. -/
def substIsClosed (X : List String) (m : SubstMap) : Prop :=
  ∀ x e, get? (M := MapStr) m x = some e → closed X e

/-- Deleting a key preserves closedness of the range. -/
theorem substIsClosed_delete {X : List String} {m : SubstMap} (y : String)
    (hm : substIsClosed X m) : substIsClosed X (delete (M := MapStr) m y) := by
  intro z ez hlz
  refine hm z ez ?_
  by_cases hyz : y = z
  · subst hyz
    rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hlz
    exact absurd hlz (by simp)
  · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hyz] at hlz

theorem substIsClosed_binderDelete {X : List String} {m : SubstMap} (b : Binder)
    (hm : substIsClosed X m) : substIsClosed X (binderDelete b m) := by
  cases b with
  | bAnon => exact hm
  | bNamed y => exact substIsClosed_delete y hm

/-- Weakening the range's variable list. -/
theorem substIsClosed_weaken {X Y : List String} {m : SubstMap} (hm : substIsClosed X m)
    (hsub : ∀ x, x ∈ X → x ∈ Y) : substIsClosed Y m :=
  fun x e he => closed_weaken (hm x e he) hsub

theorem substIsClosed_delete_weaken {X : List String} {m : SubstMap} {x : String}
    (hm : substIsClosed X m) : substIsClosed (x :: X) (delete (M := MapStr) m x) :=
  substIsClosed_weaken (substIsClosed_delete x hm) (fun _ h => .tail _ h)

/-! ## Relating `substMap` to `subst` -/

/-- The empty substitution does nothing. -/
theorem substMap_empty (e : Expr) :
    substMap (PartialMap.empty (M := MapStr) (V := Expr)) e = e := by
  have hemp : ∀ k, get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) k = none :=
    fun k => LawfulPartialMap.get?_empty (M := MapStr) k
  have hdel : ∀ x, delete (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) x
      = PartialMap.empty (M := MapStr) (V := Expr) := by
    intro x
    refine map_ext fun k => ?_
    by_cases hxk : x = k
    · rw [LawfulPartialMap.get?_delete_eq (M := MapStr) hxk, hemp k]
    · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxk]
  have hbd : ∀ b, binderDelete b (PartialMap.empty (M := MapStr) (V := Expr))
      = PartialMap.empty (M := MapStr) (V := Expr) := by
    intro b; cases b with
    | bAnon => rfl
    | bNamed x => exact hdel x
  induction e with
  | var x => simp only [substMap, hemp x]
  | lam b e ih => simp only [substMap, hbd b, ih]
  | litInt _ => rfl
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ => simp only [substMap, ih₁, ih₂]
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih => simp only [substMap, ih]
  | case _ _ _ ih₀ ih₁ ih₂ => simp only [substMap, ih₀, ih₁, ih₂]

/-- Substituting `x` after the map, or inserting `x` into the map, agree — provided the map's range
is closed, so that the outer `subst x` cannot reach into a substituted expression. -/
theorem subst_substMap (x : String) (es : Expr) (m : SubstMap) (e : Expr)
    (hclosed : substIsClosed [] m) :
    subst x es (substMap (delete (M := MapStr) m x) e) =
    substMap (insert (M := MapStr) m x es) e := by
  induction e generalizing m with
  | litInt _ => rfl
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
      simp only [substMap, binderDelete, subst,
        if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))]
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
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, subst, ih₁ m hclosed, ih₂ m hclosed]
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [substMap, subst]
    exact congrArg _ (ih m hclosed)
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, subst]
    rw [ih₀ m hclosed, ih₁ m hclosed, ih₂ m hclosed]

/-- `subst_substMap` for an arbitrary binder; the anonymous binder substitutes nothing. -/
theorem subst'_substMap (b : Binder) (es : Expr) (m : SubstMap) (e : Expr)
    (hclosed : substIsClosed [] m) :
    subst' b es (substMap (binderDelete b m) e) =
    substMap (match b with | .bAnon => m | .bNamed x => insert (M := MapStr) m x es) e := by
  cases b with
  | bAnon => simp [subst', binderDelete]
  | bNamed x => exact subst_substMap x es m e hclosed

/-! ## Closedness of the result -/

/-- The counterpart of Rocq's `subst_map_closed'_2`: if `e`'s free variables are covered by `X`
together with the domain of `θ`, and `θ`'s range is `X`-closed, then the result is `X`-closed. -/
theorem substMap_closed {X : List String} {θ : SubstMap} {e : Expr}
    (he : closed (X ++ θ.domList) e) (hθ : substIsClosed X θ) : closed X (substMap θ e) := by
  induction e generalizing X θ with
  | var x =>
    simp only [substMap]
    cases hget : get? (M := MapStr) θ x with
    | some e' => exact hθ x e' hget
    | none =>
      simp only [closed, Expr.isClosed, decide_eq_true_eq] at he ⊢
      rcases List.mem_append.mp he with h | h
      · exact h
      · obtain ⟨e', he'⟩ := mem_domList_iff_lookup.mp h
        rw [hget] at he'
        exact absurd he' (by simp)
  | lam b e ih =>
    cases b with
    | bAnon =>
      simp only [substMap, closed, Expr.isClosed, Binder.cons, binderDelete] at he ⊢
      exact ih he hθ
    | bNamed y =>
      simp only [substMap, closed, Expr.isClosed, Binder.cons, binderDelete] at he ⊢
      refine ih ?_ (substIsClosed_delete_weaken hθ)
      refine closed_weaken he fun z hz => ?_
      simp only [List.mem_cons, List.mem_append] at hz ⊢
      rcases hz with heq | hz | hz
      · exact Or.inl (Or.inl heq)
      · exact Or.inl (Or.inr hz)
      · by_cases hzy : z = y
        · exact Or.inl (Or.inl hzy)
        · refine Or.inr ?_
          rw [mem_domList_iff_lookup] at hz ⊢
          obtain ⟨e', he'⟩ := hz
          exact ⟨e', by
            rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) (fun h => hzy h.symm)]⟩
  | litInt _ => rfl
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1 hθ, ih₂ he.2 hθ⟩
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih => exact ih he hθ
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ he.1.1 hθ, ih₁ he.1.2 hθ⟩, ih₂ he.2 hθ⟩

/-! ## The `parallel_subst.v` remainder -/

theorem substIsClosed_weaken_nil {X : List String} {m : SubstMap} (hm : substIsClosed [] m) :
    substIsClosed X m :=
  substIsClosed_weaken hm (by simp)

/-- With `gmap` inclusion spelled out pointwise. -/
theorem substIsClosed_subseteq {X : List String} {m₁ m₂ : SubstMap}
    (hsub : ∀ x e, get? (M := MapStr) m₁ x = some e → get? (M := MapStr) m₂ x = some e)
    (hm₂ : substIsClosed X m₂) : substIsClosed X m₁ :=
  fun x e he => hm₂ x e (hsub x e he)

theorem substIsClosed_insert {X : List String} {m : SubstMap} {f : String} {e : Expr}
    (he : closed X e) (hm : substIsClosed X (delete (M := MapStr) m f)) :
    substIsClosed X (insert (M := MapStr) m f e) := by
  intro x e' hx
  by_cases hfx : f = x
  · rw [LawfulPartialMap.get?_insert_eq (M := MapStr) hfx] at hx
    injection hx with hx
    exact hx ▸ he
  · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hfx] at hx
    exact hm x e' (by rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hfx])

/-- Descending under a binder keeps the substitution's domain away from the permitted variables. -/
private theorem binderDelete_avoids {X : List String} {m : SubstMap} (b : Binder)
    (hdom : ∀ x, get? (M := MapStr) m x ≠ none → x ∉ X) :
    ∀ x, get? (M := MapStr) (binderDelete b m) x ≠ none → x ∉ (b :b: X) := by
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

/-- A substitution whose domain avoids the free variables of `e` does
nothing. -/
theorem substMap_is_closed {X : List String} {m : SubstMap} {e : Expr} (he : closed X e)
    (hdom : ∀ x, get? (M := MapStr) m x ≠ none → x ∉ X) : substMap m e = e := by
  induction e generalizing X m with
  | litInt _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    simp only [substMap]
    cases hget : get? (M := MapStr) m y with
    | none => rfl
    | some e' => exact absurd he (hdom y (by rw [hget]; simp))
  | lam b e ih =>
    simp only [closed, Expr.isClosed] at he
    simp only [substMap]
    rw [ih he (binderDelete_avoids b hdom)]
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [closed, Expr.isClosed] at he
    simp only [substMap]
    rw [ih he hdom]
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at he
    simp only [substMap]
    rw [ih₁ he.1 hdom, ih₂ he.2 hdom]
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at he
    simp only [substMap]
    rw [ih₀ he.1.1 hdom, ih₁ he.1.2 hdom, ih₂ he.2 hdom]

/-- A single substitution in front of a parallel one is an insertion. -/
theorem substMap_subst {m : SubstMap} {x : String} {e es : Expr} (hes : closed [] es) :
    substMap m (subst x es e) = substMap (insert (M := MapStr) m x es) e := by
  induction e generalizing m with
  | litInt _ => rfl
  | var y =>
    simp only [subst]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      simp only [substMap]
      rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl]
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
        rw [delete_insert_eq m x es]
      · simp only [subst]
        rw [if_neg (fun h => hxy (by cases h; rfl))]
        simp only [substMap, binderDelete]
        rw [ih, delete_insert_comm m es hxy]
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [subst, substMap]
    rw [ih]
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [subst, substMap]
    rw [ih₁, ih₂]
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [subst, substMap]
    rw [ih₀, ih₁, ih₂]

/-- Descending under a binder preserves closedness of the range at the empty variable list. -/
private theorem substIsClosed_binderDelete_nil (b : Binder) (m : SubstMap)
    (hm : substIsClosed [] m) : substIsClosed [] (binderDelete b m) := by
  cases b with
  | bAnon => exact hm
  | bNamed z => exact substIsClosed_delete z hm

/-- The coverage side condition of `closed_subst_weaken` descends under a binder. -/
private theorem binderDelete_sub {X Y : List String} {m : SubstMap} (b : Binder)
    (hsub : ∀ x, x ∈ X → get? (M := MapStr) m x = none → x ∈ Y) :
    ∀ x, x ∈ (b :b: X) → get? (M := MapStr) (binderDelete b m) x = none → x ∈ (b :b: Y) := by
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
theorem closed_subst_weaken {X Y : List String} {m : SubstMap} {e : Expr}
    (hm : substIsClosed [] m)
    (hsub : ∀ x, x ∈ X → get? (M := MapStr) m x = none → x ∈ Y)
    (he : closed X e) : closed Y (substMap m e) := by
  induction e generalizing X Y m with
  | litInt _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    simp only [substMap]
    cases hget : get? (M := MapStr) m y with
    | none =>
      simp only [closed, Expr.isClosed, decide_eq_true_eq]
      exact hsub y he hget
    | some e' => exact closed_weaken_nil (hm y e' hget)
  | lam b e ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih (substIsClosed_binderDelete_nil b m hm) (binderDelete_sub b hsub) he
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih hm hsub he
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ hm hsub he.1, ih₂ hm hsub he.2⟩
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ hm hsub he.1.1, ih₁ hm hsub he.1.2⟩, ih₂ hm hsub he.2⟩

/-- The coverage criterion of `substMap_closed'` descends under a binder. -/
private theorem binderDelete_cov {X Y : List String} {m : SubstMap} (b : Binder)
    (hcov : ∀ x, x ∈ Y → match get? (M := MapStr) m x with
      | some e' => closed X e'
      | none => x ∈ X) :
    ∀ x, x ∈ (b :b: Y) → match get? (M := MapStr) (binderDelete b m) x with
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
      cases hget : get? (M := MapStr) m x with
      | none =>
        rw [hget] at hy
        exact List.Mem.tail _ hy
      | some e' =>
        rw [hget] at hy
        exact closed_weaken hy fun w hw => List.Mem.tail _ hw

/-- Every free variable of `e` is either substituted by an `X`-closed
expression or already in `X`. -/
theorem substMap_closed' {X Y : List String} {m : SubstMap} {e : Expr} (he : closed Y e)
    (hcov : ∀ x, x ∈ Y → match get? (M := MapStr) m x with
      | some e' => closed X e'
      | none => x ∈ X) : closed X (substMap m e) := by
  induction e generalizing X Y m with
  | litInt _ => rfl
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at he
    have hy := hcov y he
    simp only [substMap]
    cases hget : get? (M := MapStr) m y with
    | none =>
      rw [hget] at hy
      simpa [closed, Expr.isClosed] using hy
    | some e' =>
      rw [hget] at hy
      exact hy
  | lam b e ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih he (binderDelete_cov b hcov)
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih =>
    simp only [substMap, closed, Expr.isClosed] at he ⊢
    exact ih he hcov
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1 hcov, ih₂ he.2 hcov⟩
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [substMap, closed, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ he.1.1 hcov, ih₁ he.1.2 hcov⟩, ih₂ he.2 hcov⟩

end StlcExtended
