import LeanLR.TypeSystems.SystemF.Lang
import LeanLR.TypeSystems.SystemF.Notation
import LeanLR.TypeSystems.SystemF.Types
import LeanLR.TypeSystems.SystemF.TypeSafety
import LeanLR.TypeSystems.SystemF.BigStep
import LeanLR.TypeSystems.SystemF.ParallelSubst
import LeanLR.TypeSystems.SystemF.LogRel

/-!
# System F: the binary logical relation

`systemf/binary_logrel.v`. `valRel δ A v w` says `v` and `w` are indistinguishable at `A`; the
payoff is contextual equivalence (`soundness_wrt_ctx_equiv`). Everything lives in `SystemF.Binary`
so that the unary names stay reachable; `Ty.size` and the syntax are shared with the unary
development.
-/

open Iris.Std

namespace SystemF.Binary

/-! ## Semantic types -/

/-- A relation on values that only relates closed ones. -/
structure SemType where
  car : Val → Val → Prop
  closed_val : ∀ v w, car v w → closed [] v.toExpr ∧ closed [] w.toExpr

abbrev TyVarInterp := Nat → SemType

/-- Autosubst's `τ .: δ`: extend an interpretation at index `0`. -/
def TyVarInterp.cons (τ : SemType) (δ : TyVarInterp) : TyVarInterp
  | 0 => τ
  | n + 1 => δ n

@[inherit_doc] notation:max τ " .:₂ " δ => TyVarInterp.cons τ δ

@[simp] theorem cons_zero (τ : SemType) (δ : TyVarInterp) : (τ .:₂ δ) 0 = τ := rfl

@[simp] theorem cons_succ (τ : SemType) (δ : TyVarInterp) (n : Nat) :
    (τ .:₂ δ) (n + 1) = δ n := rfl

/-! ## The relation

One structurally recursive function on the type, with the expression relation inlined at the two
places that need it (`fn` and `all`). -/

/-- `valRel δ A v w`: the values `v` and `w` are related at type `A`. -/
def valRel (δ : TyVarInterp) : Ty → Val → Val → Prop
  | .int, v, w => ∃ z : Int, v = .litV (.litInt z) ∧ w = .litV (.litInt z)
  | .bool, v, w => ∃ b : Bool, v = .litV (.litBool b) ∧ w = .litV (.litBool b)
  | .unit, v, w => v = .litV .litUnit ∧ w = .litV .litUnit
  | .tVar α, v, w => (δ α).car v w
  | .prod A B, v, w =>
      ∃ v₁ v₂ w₁ w₂ : Val, v = .pairV v₁ v₂ ∧ w = .pairV w₁ w₂ ∧
        valRel δ A v₁ w₁ ∧ valRel δ B v₂ w₂
  | .sum A B, v, w =>
      (∃ v' w' : Val, v = .injLV v' ∧ w = .injLV w' ∧ valRel δ A v' w') ∨
      (∃ v' w' : Val, v = .injRV v' ∧ w = .injRV w' ∧ valRel δ B v' w')
  | .fn A B, v, w =>
      ∃ (x y : Binder) (e₁ e₂ : Expr), v = .lamV x e₁ ∧ w = .lamV y e₂ ∧
        closed (x :b: []) e₁ ∧ closed (y :b: []) e₂ ∧
        ∀ v' w' : Val, valRel δ A v' w' →
          ∃ u₁ u₂ : Val, BigStep (subst' x v'.toExpr e₁) u₁ ∧
            BigStep (subst' y w'.toExpr e₂) u₂ ∧ valRel δ B u₁ u₂
  | .all A, v, w =>
      ∃ e₁ e₂ : Expr, v = .tLamV e₁ ∧ w = .tLamV e₂ ∧ closed [] e₁ ∧ closed [] e₂ ∧
        ∀ τ : SemType, ∃ u₁ u₂ : Val, BigStep e₁ u₁ ∧ BigStep e₂ u₂ ∧
          valRel (τ .:₂ δ) A u₁ u₂
  | .exist A, v, w =>
      ∃ v' w' : Val, v = .packV v' ∧ w = .packV w' ∧
        ∃ τ : SemType, valRel (τ .:₂ δ) A v' w'
termination_by A _ _ => A.size
decreasing_by all_goals simp_wf <;> simp [Ty.size] <;> omega

/-- `exprRel δ A e₁ e₂`: both expressions evaluate, to related values. -/
def exprRel (δ : TyVarInterp) (A : Ty) (e₁ e₂ : Expr) : Prop :=
  ∃ v₁ v₂ : Val, BigStep e₁ v₁ ∧ BigStep e₂ v₂ ∧ valRel δ A v₁ v₂

/-! ## Basic properties -/

theorem val_rel_is_closed (v w : Val) (δ : TyVarInterp) (A : Ty) (h : valRel δ A v w) :
    closed [] v.toExpr ∧ closed [] w.toExpr := by
  induction A generalizing δ v w with
  | tVar α =>
    simp only [valRel] at h
    exact (δ α).closed_val v w h
  | int =>
    simp only [valRel] at h
    obtain ⟨z, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | bool =>
    simp only [valRel] at h
    obtain ⟨b, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | unit =>
    simp only [valRel] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fn A B _ _ =>
    simp only [valRel] at h
    obtain ⟨x, y, e₁, e₂, rfl, rfl, hcl₁, hcl₂, _⟩ := h
    exact ⟨hcl₁, hcl₂⟩
  | all A _ =>
    simp only [valRel] at h
    obtain ⟨e₁, e₂, rfl, rfl, hcl₁, hcl₂, _⟩ := h
    exact ⟨hcl₁, hcl₂⟩
  | exist A ih =>
    simp only [valRel] at h
    obtain ⟨v', w', rfl, rfl, τ, hv'⟩ := h
    exact ih v' w' _ hv'
  | prod A B ihA ihB =>
    simp only [valRel] at h
    obtain ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩ := h
    obtain ⟨ha₁, hb₁⟩ := ihA v₁ w₁ _ h₁
    obtain ⟨ha₂, hb₂⟩ := ihB v₂ w₂ _ h₂
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true]
    exact ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩
  | sum A B ihA ihB =>
    simp only [valRel] at h
    rcases h with ⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩
    · exact ihA v' w' _ h'
    · exact ihB v' w' _ h'

def interp_type (A : Ty) (δ : TyVarInterp) : SemType where
  car v w := valRel δ A v w
  closed_val v w h := val_rel_is_closed v w δ A h

theorem sem_expr_rel_of_val (A : Ty) (δ : TyVarInterp) (v w : Val)
    (h : exprRel δ A v.toExpr w.toExpr) : valRel δ A v w := by
  obtain ⟨v', w', hb₁, hb₂, hrel⟩ := h
  rw [big_step_val hb₁, big_step_val hb₂] at hrel
  exact hrel

/-- The value relation implies the expression relation. -/
theorem val_inclusion (A : Ty) (δ : TyVarInterp) (v w : Val) (h : valRel δ A v w) :
    exprRel δ A v.toExpr w.toExpr :=
  ⟨v, w, big_step_of_val rfl, big_step_of_val rfl, h⟩

/-! ## The context relation -/

inductive SemCtxRel (δ : TyVarInterp) : TypingContext → SubstMap → SubstMap → Prop where
  | empty :
      SemCtxRel δ (PartialMap.empty (M := TyMapStr) (V := Ty))
        (PartialMap.empty (M := MapStr) (V := Expr))
        (PartialMap.empty (M := MapStr) (V := Expr))
  | insert {Γ : TypingContext} {θ₁ θ₂ : SubstMap} (v w : Val) (x : String) (A : Ty) :
      valRel δ A v w → SemCtxRel δ Γ θ₁ θ₂ →
      SemCtxRel δ (Iris.Std.insert (M := TyMapStr) Γ x A)
        (Iris.Std.insert (M := MapStr) θ₁ x v.toExpr)
        (Iris.Std.insert (M := MapStr) θ₂ x w.toExpr)

theorem sem_context_rel_vals {δ : TyVarInterp} {Γ : TypingContext} {θ₁ θ₂ : SubstMap}
    {x : String} {A : Ty} (h : SemCtxRel δ Γ θ₁ θ₂)
    (hx : get? (M := TyMapStr) Γ x = some A) :
    ∃ (e₁ e₂ : Expr) (v₁ v₂ : Val), get? (M := MapStr) θ₁ x = some e₁ ∧
      get? (M := MapStr) θ₂ x = some e₂ ∧ e₁.toVal? = some v₁ ∧ e₂.toVal? = some v₂ ∧
      valRel δ A v₁ v₂ := by
  induction h with
  | empty =>
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
      LawfulPartialMap.get?_empty (M := TyMapStr) x] at hx
    exact absurd hx (by simp)
  | insert v w y B hv _ ih =>
    by_cases hxy : y = x
    · subst hxy
      rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at hx
      injection hx with hx
      subst hx
      exact ⟨v.toExpr, w.toExpr, v, w, LawfulPartialMap.get?_insert_eq (M := MapStr) rfl,
        LawfulPartialMap.get?_insert_eq (M := MapStr) rfl, toVal?_toExpr v, toVal?_toExpr w, hv⟩
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hx
      obtain ⟨e₁, e₂, u₁, u₂, h₁, h₂, hu₁, hu₂, hrel⟩ := ih hx
      exact ⟨e₁, e₂, u₁, u₂, by rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]; exact h₁,
        by rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]; exact h₂, hu₁, hu₂, hrel⟩

/-- As the pointwise statement the port uses. -/
theorem sem_context_rel_dom {δ : TyVarInterp} {Γ : TypingContext} {θ₁ θ₂ : SubstMap}
    (h : SemCtxRel δ Γ θ₁ θ₂) (x : String) :
    (get? (M := TyMapStr) Γ x ≠ none ↔ get? (M := MapStr) θ₁ x ≠ none) ∧
    (get? (M := TyMapStr) Γ x ≠ none ↔ get? (M := MapStr) θ₂ x ≠ none) := by
  induction h with
  | empty =>
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
        LawfulPartialMap.get?_empty (M := TyMapStr) x,
      show get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) x = none from
        LawfulPartialMap.get?_empty (M := MapStr) x]
    simp
  | insert v w y B hv _ ih =>
    by_cases hxy : y = x
    · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy,
        LawfulPartialMap.get?_insert_eq (M := MapStr) hxy,
        LawfulPartialMap.get?_insert_eq (M := MapStr) hxy]
      simp
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy,
        LawfulPartialMap.get?_insert_ne (M := MapStr) hxy,
        LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      exact ih

theorem sem_context_rel_closed {δ : TyVarInterp} {Γ : TypingContext} {θ₁ θ₂ : SubstMap}
    (h : SemCtxRel δ Γ θ₁ θ₂) : substIsClosed [] θ₁ ∧ substIsClosed [] θ₂ := by
  induction h with
  | empty =>
    constructor <;>
      · intro y e hy
        rw [show get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) y = none from
          LawfulPartialMap.get?_empty (M := MapStr) y] at hy
        exact absurd hy (by simp)
  | insert v w x A hv _ ih =>
    obtain ⟨hcv, hcw⟩ := val_rel_is_closed v w _ _ hv
    constructor
    · intro y e hy
      by_cases hxy : x = y
      · rw [LawfulPartialMap.get?_insert_eq (M := MapStr) hxy] at hy
        injection hy with hy
        exact hy ▸ hcv
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hy
        exact ih.1 y e hy
    · intro y e hy
      by_cases hxy : x = y
      · rw [LawfulPartialMap.get?_insert_eq (M := MapStr) hxy] at hy
        injection hy with hy
        exact hy ▸ hcw
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hy
        exact ih.2 y e hy

/-- As a `domList` statement. -/
theorem sem_context_rel_domList {δ : TyVarInterp} {Γ : TypingContext} {θ₁ θ₂ : SubstMap}
    (h : SemCtxRel δ Γ θ₁ θ₂) (x : String) :
    (x ∈ Γ.domList ↔ x ∈ θ₁.domList) ∧ (x ∈ Γ.domList ↔ x ∈ θ₂.domList) := by
  obtain ⟨hd₁, hd₂⟩ := sem_context_rel_dom h x
  rw [mem_ctx_domList, mem_domList_iff_lookup, mem_domList_iff_lookup]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA⟩
    cases hget : get? (M := MapStr) θ₁ x with
    | none => exact absurd hget (hd₁.mp (by rw [hA]; simp))
    | some e => exact ⟨e, rfl⟩
  · rintro ⟨e, he⟩
    cases hget : get? (M := TyMapStr) Γ x with
    | none => exact absurd hget (hd₁.mpr (by rw [he]; simp))
    | some A => exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    cases hget : get? (M := MapStr) θ₂ x with
    | none => exact absurd hget (hd₂.mp (by rw [hA]; simp))
    | some e => exact ⟨e, rfl⟩
  · rintro ⟨e, he⟩
    cases hget : get? (M := TyMapStr) Γ x with
    | none => exact absurd hget (hd₂.mpr (by rw [he]; simp))
    | some A => exact ⟨A, rfl⟩

def semTyped (Γ : TypingContext) (e₁ e₂ : Expr) (A : Ty) : Prop :=
  closed Γ.domList e₁ ∧ closed Γ.domList e₂ ∧
    ∀ (θ₁ θ₂ : SubstMap) (δ : TyVarInterp), SemCtxRel δ Γ θ₁ θ₂ →
      exprRel δ A (substMap θ₁ e₁) (substMap θ₂ e₂)

/-! ## Moving the interpretation around -/

/-- Extending two pointwise-equal interpretations keeps them pointwise equal. -/
private theorem cons_iff {δ δ' : TyVarInterp} (τ : SemType)
    (hiff : ∀ n v w, (δ n).car v w ↔ (δ' n).car v w) :
    ∀ n v w, ((τ .:₂ δ) n).car v w ↔ ((τ .:₂ δ') n).car v w := by
  intro n v w
  cases n with
  | zero => exact Iff.rfl
  | succ m => exact hiff m v w

theorem sem_val_rel_ext (B : Ty) (δ δ' : TyVarInterp) (v w : Val)
    (hiff : ∀ n v w, (δ n).car v w ↔ (δ' n).car v w) :
    valRel δ B v w ↔ valRel δ' B v w := by
  induction B generalizing δ δ' v w with
  | tVar α => simp only [valRel]; exact hiff α v w
  | int | bool | unit => simp only [valRel]
  | fn A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ δ' v' w' hiff).mpr hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ δ' u₁ u₂ hiff).mp hu⟩
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ δ' v' w' hiff).mp hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ δ' u₁ u₂ hiff).mpr hu⟩
  | all A ih =>
    simp only [valRel]
    constructor
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (ih _ _ u₁ u₂ (cons_iff τ hiff)).mp hu⟩
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (ih _ _ u₁ u₂ (cons_iff τ hiff)).mpr hu⟩
  | exist A ih =>
    simp only [valRel]
    constructor
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (ih _ _ v' w' (cons_iff τ hiff)).mp hv'⟩
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (ih _ _ v' w' (cons_iff τ hiff)).mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA _ _ v₁ w₁ hiff).mp h₁, (ihB _ _ v₂ w₂ hiff).mp h₂⟩
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA _ _ v₁ w₁ hiff).mpr h₁, (ihB _ _ v₂ w₂ hiff).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA _ _ v' w' hiff).mp h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB _ _ v' w' hiff).mp h'⟩
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA _ _ v' w' hiff).mpr h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB _ _ v' w' hiff).mpr h'⟩

theorem sem_val_rel_move_ren (B : Ty) (δ : TyVarInterp) (σ : Nat → Nat) (v w : Val) :
    valRel (fun n => δ (σ n)) B v w ↔ valRel δ (B.rename σ) v w := by
  induction B generalizing δ σ v w with
  | tVar α => simp only [Ty.rename, valRel]
  | int | bool | unit => simp only [Ty.rename, valRel]
  | fn A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ σ v' w').mpr hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ σ u₁ u₂).mp hu⟩
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ σ v' w').mp hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ σ u₁ u₂).mpr hu⟩
  | all A ih =>
    simp only [Ty.rename, valRel]
    have hcons : ∀ (τ : SemType) (u₁ u₂ : Val),
        valRel (τ .:₂ fun n => δ (σ n)) A u₁ u₂ ↔
          valRel (τ .:₂ δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) u₁ u₂ := by
      intro τ u₁ u₂
      refine Iff.trans ?_ (ih (τ .:₂ δ) _ u₁ u₂)
      refine sem_val_rel_ext A _ _ u₁ u₂ fun n a b => ?_
      cases n <;> exact Iff.rfl
    constructor
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (hcons τ u₁ u₂).mp hu⟩
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (hcons τ u₁ u₂).mpr hu⟩
  | exist A ih =>
    simp only [Ty.rename, valRel]
    have hcons : ∀ (τ : SemType) (u₁ u₂ : Val),
        valRel (τ .:₂ fun n => δ (σ n)) A u₁ u₂ ↔
          valRel (τ .:₂ δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) u₁ u₂ := by
      intro τ u₁ u₂
      refine Iff.trans ?_ (ih (τ .:₂ δ) _ u₁ u₂)
      refine sem_val_rel_ext A _ _ u₁ u₂ fun n a b => ?_
      cases n <;> exact Iff.rfl
    constructor
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (hcons τ v' w').mp hv'⟩
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (hcons τ v' w').mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA δ σ v₁ w₁).mp h₁, (ihB δ σ v₂ w₂).mp h₂⟩
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA δ σ v₁ w₁).mpr h₁, (ihB δ σ v₂ w₂).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA δ σ v' w').mp h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB δ σ v' w').mp h'⟩
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA δ σ v' w').mpr h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB δ σ v' w').mpr h'⟩

theorem sem_val_rel_move_subst (B : Ty) (δ : TyVarInterp) (σ : Nat → Ty) (v w : Val) :
    valRel (fun n => interp_type (σ n) δ) B v w ↔ valRel δ (B.substTy σ) v w := by
  induction B generalizing δ σ v w with
  | tVar α => simp only [Ty.substTy, valRel, interp_type]
  | int | bool | unit => simp only [Ty.substTy, valRel]
  | fn A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ σ v' w').mpr hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ σ u₁ u₂).mp hu⟩
    · rintro ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨x, y, e₁, e₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody v' w' ((ihA δ σ v' w').mp hvw)
      exact ⟨u₁, u₂, hb₁, hb₂, (ihB δ σ u₁ u₂).mpr hu⟩
  | all A ih =>
    simp only [Ty.substTy, valRel]
    have hcons : ∀ (τ : SemType) (u₁ u₂ : Val),
        valRel (τ .:₂ fun n => interp_type (σ n) δ) A u₁ u₂ ↔
          valRel (τ .:₂ δ) (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) u₁ u₂ := by
      intro τ u₁ u₂
      refine Iff.trans ?_ (ih (τ .:₂ δ) _ u₁ u₂)
      refine sem_val_rel_ext A _ _ u₁ u₂ fun n a b => ?_
      cases n with
      | zero =>
        show τ.car a b ↔ (interp_type (Ty.tVar 0) (τ .:₂ δ)).car a b
        simp only [interp_type, valRel, cons_zero]
      | succ m =>
        show (interp_type (σ m) δ).car a b ↔
          (interp_type ((σ m).rename (· + 1)) (τ .:₂ δ)).car a b
        exact sem_val_rel_move_ren (σ m) (τ .:₂ δ) (· + 1) a b
    constructor
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (hcons τ u₁ u₂).mp hu⟩
    · rintro ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, hbody⟩
      refine ⟨e₁, e₂, rfl, rfl, hc₁, hc₂, fun τ => ?_⟩
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hbody τ
      exact ⟨u₁, u₂, hb₁, hb₂, (hcons τ u₁ u₂).mpr hu⟩
  | exist A ih =>
    simp only [Ty.substTy, valRel]
    have hcons : ∀ (τ : SemType) (u₁ u₂ : Val),
        valRel (τ .:₂ fun n => interp_type (σ n) δ) A u₁ u₂ ↔
          valRel (τ .:₂ δ) (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) u₁ u₂ := by
      intro τ u₁ u₂
      refine Iff.trans ?_ (ih (τ .:₂ δ) _ u₁ u₂)
      refine sem_val_rel_ext A _ _ u₁ u₂ fun n a b => ?_
      cases n with
      | zero =>
        show τ.car a b ↔ (interp_type (Ty.tVar 0) (τ .:₂ δ)).car a b
        simp only [interp_type, valRel, cons_zero]
      | succ m =>
        show (interp_type (σ m) δ).car a b ↔
          (interp_type ((σ m).rename (· + 1)) (τ .:₂ δ)).car a b
        exact sem_val_rel_move_ren (σ m) (τ .:₂ δ) (· + 1) a b
    constructor
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (hcons τ v' w').mp hv'⟩
    · rintro ⟨v', w', rfl, rfl, τ, hv'⟩
      exact ⟨v', w', rfl, rfl, τ, (hcons τ v' w').mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA δ σ v₁ w₁).mp h₁, (ihB δ σ v₂ w₂).mp h₂⟩
    · rintro ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, (ihA δ σ v₁ w₁).mpr h₁, (ihB δ σ v₂ w₂).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA δ σ v' w').mp h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB δ σ v' w').mp h'⟩
    · rintro (⟨v', w', rfl, rfl, h'⟩ | ⟨v', w', rfl, rfl, h'⟩)
      · exact Or.inl ⟨v', w', rfl, rfl, (ihA δ σ v' w').mpr h'⟩
      · exact Or.inr ⟨v', w', rfl, rfl, (ihB δ σ v' w').mpr h'⟩

theorem sem_val_rel_move_single_subst (A B : Ty) (δ : TyVarInterp) (v w : Val) :
    valRel ((interp_type A δ) .:₂ δ) B v w ↔ valRel δ (B.subst1 A) v w := by
  refine Iff.trans ?_ (sem_val_rel_move_subst B δ _ v w)
  refine sem_val_rel_ext B _ _ v w fun n a b => ?_
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    show (δ m).car a b ↔ (interp_type (Ty.tVar m) δ).car a b
    simp only [interp_type, valRel]

theorem sem_val_rel_cons (A : Ty) (δ : TyVarInterp) (v w : Val) (τ : SemType) :
    valRel δ A v w ↔ valRel (τ .:₂ δ) (A.rename (· + 1)) v w :=
  sem_val_rel_move_ren A (τ .:₂ δ) (· + 1) v w

theorem sem_context_rel_cons {Γ : TypingContext} {δ : TyVarInterp} {θ₁ θ₂ : SubstMap}
    (τ : SemType) (h : SemCtxRel δ Γ θ₁ θ₂) : SemCtxRel (τ .:₂ δ) (shiftCtx Γ) θ₁ θ₂ := by
  induction h with
  | empty =>
    rw [shiftCtx_empty]
    exact .empty
  | insert v w x A hv _ ih =>
    rw [shiftCtx_insert]
    exact .insert v w x _ ((sem_val_rel_cons A _ v w τ).mp hv) ih

/-! ## Closedness helpers -/

/-- Stated against the domain and closedness facts rather than against the
context relation, so that it applies to either side. -/
theorem lam_closed {Γ : TypingContext} {θ : SubstMap} (x : String) (A : Ty) (e : Expr)
    (hcl : closed (TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A)) e)
    (hdom : ∀ y, y ∈ Γ.domList ↔ y ∈ θ.domList) (hθ : substIsClosed [] θ) :
    closed [] (Expr.lam (.bNamed x) (substMap (delete (M := MapStr) θ x) e)) := by
  show closed [x] (substMap (delete (M := MapStr) θ x) e)
  refine substMap_closed ?_ ?_
  · refine closed_weaken hcl fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.mem_append.mpr (Or.inl (List.Mem.head _))
    · by_cases hxy : x = y
      · exact List.mem_append.mpr (Or.inl (hxy ▸ List.Mem.head _))
      · refine List.mem_append.mpr (Or.inr ?_)
        rw [mem_domList_iff_lookup]
        obtain ⟨e', he'⟩ := mem_domList_iff_lookup.mp ((hdom y).mp hy')
        exact ⟨e', by rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]; exact he'⟩
  · intro y e' hy
    refine closed_weaken (hθ y e' ?_) (by simp)
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hy
      exact absurd hy (by simp)
    · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at hy

/-- The anonymous-binder counterpart of `lam_closed`. -/
theorem substMap_ctx_closed {Γ : TypingContext} {θ : SubstMap} {e : Expr}
    (hcl : closed Γ.domList e) (hdom : ∀ y, y ∈ Γ.domList ↔ y ∈ θ.domList)
    (hθ : substIsClosed [] θ) : closed [] (substMap θ e) := by
  refine substMap_closed ?_ hθ
  exact closed_weaken hcl fun y hy => List.mem_append.mpr (Or.inr ((hdom y).mp hy))

/-! ## Compatibility lemmas -/

theorem compat_int (Γ : TypingContext) (z : Int) :
    semTyped Γ (.lit (.litInt z)) (.lit (.litInt z)) .int := by
  refine ⟨rfl, rfl, fun θ₁ θ₂ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV (.litInt z), .litV (.litInt z), .bs_lit _, .bs_lit _, z, rfl, rfl⟩

theorem compat_bool (Γ : TypingContext) (b : Bool) :
    semTyped Γ (.lit (.litBool b)) (.lit (.litBool b)) .bool := by
  refine ⟨rfl, rfl, fun θ₁ θ₂ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV (.litBool b), .litV (.litBool b), .bs_lit _, .bs_lit _, b, rfl, rfl⟩

theorem compat_unit (Γ : TypingContext) :
    semTyped Γ (.lit .litUnit) (.lit .litUnit) .unit := by
  refine ⟨rfl, rfl, fun θ₁ θ₂ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV .litUnit, .litV .litUnit, .bs_lit _, .bs_lit _, rfl, rfl⟩

theorem compat_var (Γ : TypingContext) (x : String) (A : Ty)
    (hx : get? (M := TyMapStr) Γ x = some A) : semTyped Γ (.var x) (.var x) A := by
  refine ⟨?_, ?_, fun θ₁ θ₂ δ hctx => ?_⟩
  · simpa [closed, Expr.isClosed] using mem_ctx_domList.mpr ⟨A, hx⟩
  · simpa [closed, Expr.isClosed] using mem_ctx_domList.mpr ⟨A, hx⟩
  · obtain ⟨e₁, e₂, v₁, v₂, h₁, h₂, hv₁, hv₂, hrel⟩ := sem_context_rel_vals hctx hx
    simp only [substMap, h₁, h₂, exprRel]
    exact ⟨v₁, v₂, big_step_of_val (toVal?_eq hv₁), big_step_of_val (toVal?_eq hv₂), hrel⟩

theorem compat_app (Γ : TypingContext) (e₁ e₁' e₂ e₂' : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ e₁' (.fn A B)) (h₂ : semTyped Γ e₂ e₂' A) :
    semTyped Γ (.app e₁ e₂) (.app e₁' e₂') B := by
  obtain ⟨hc₁, hc₁', hfun⟩ := h₁
  obtain ⟨hc₂, hc₂', harg⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁', hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨f₁, f₂, hbf₁, hbf₂, hf⟩ := hfun θ₁ θ₂ δ hctx
  simp only [valRel] at hf
  obtain ⟨x, y, e, e', rfl, rfl, _, _, hbody⟩ := hf
  obtain ⟨a₁, a₂, hba₁, hba₂, ha⟩ := harg θ₁ θ₂ δ hctx
  obtain ⟨u₁, u₂, hbu₁, hbu₂, hu⟩ := hbody a₁ a₂ ha
  simp only [substMap, exprRel]
  exact ⟨u₁, u₂, .bs_app _ _ x e a₁ u₁ hbf₁ hba₁ hbu₁,
    .bs_app _ _ y e' a₂ u₂ hbf₂ hba₂ hbu₂, hu⟩

theorem compat_lam_named (Γ : TypingContext) (x : String) (e₁ e₂ : Expr) (A B : Ty)
    (h : semTyped (Iris.Std.insert (M := TyMapStr) Γ x A) e₁ e₂ B) :
    semTyped Γ (.lam (.bNamed x) e₁) (.lam (.bNamed x) e₂) (.fn A B) := by
  obtain ⟨hc₁, hc₂, hbody⟩ := h
  have hweak : ∀ e : Expr,
      closed (TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A)) e →
      closed (x :: TypingContext.domList Γ) e := by
    intro e he
    refine closed_weaken he fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ hy'
  refine ⟨hweak e₁ hc₁, hweak e₂ hc₂, fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨hθ₁, hθ₂⟩ := sem_context_rel_closed hctx
  simp only [substMap, binderDelete, exprRel]
  refine ⟨.lamV (.bNamed x) (substMap (delete (M := MapStr) θ₁ x) e₁),
    .lamV (.bNamed x) (substMap (delete (M := MapStr) θ₂ x) e₂), .bs_lam _ _, .bs_lam _ _, ?_⟩
  simp only [valRel]
  refine ⟨.bNamed x, .bNamed x, _, _, rfl, rfl,
    lam_closed x A e₁ hc₁ (fun y => (sem_context_rel_domList hctx y).1) hθ₁,
    lam_closed x A e₂ hc₂ (fun y => (sem_context_rel_domList hctx y).2) hθ₂,
    fun v' w' hvw => ?_⟩
  have hb := hbody (Iris.Std.insert (M := MapStr) θ₁ x v'.toExpr)
    (Iris.Std.insert (M := MapStr) θ₂ x w'.toExpr) δ (.insert v' w' x A hvw hctx)
  rw [← subst_substMap x v'.toExpr θ₁ e₁ hθ₁] at hb
  rw [← subst_substMap x w'.toExpr θ₂ e₂ hθ₂] at hb
  exact hb

theorem compat_lam_anon (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h : semTyped Γ e₁ e₂ B) : semTyped Γ (.lam .bAnon e₁) (.lam .bAnon e₂) (.fn A B) := by
  obtain ⟨hc₁, hc₂, hbody⟩ := h
  refine ⟨hc₁, hc₂, fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨hθ₁, hθ₂⟩ := sem_context_rel_closed hctx
  simp only [substMap, binderDelete, exprRel]
  refine ⟨.lamV .bAnon (substMap θ₁ e₁), .lamV .bAnon (substMap θ₂ e₂),
    .bs_lam _ _, .bs_lam _ _, ?_⟩
  simp only [valRel]
  exact ⟨.bAnon, .bAnon, _, _, rfl, rfl,
    substMap_ctx_closed hc₁ (fun y => (sem_context_rel_domList hctx y).1) hθ₁,
    substMap_ctx_closed hc₂ (fun y => (sem_context_rel_domList hctx y).2) hθ₂,
    fun v' w' _ => hbody θ₁ θ₂ δ hctx⟩

theorem compat_int_binop (Γ : TypingContext) (op : BinOp) (e₁ e₁' e₂ e₂' : Expr)
    (hop : BinOpTyped op .int .int .int) (h₁ : semTyped Γ e₁ e₁' .int)
    (h₂ : semTyped Γ e₂ e₂' .int) : semTyped Γ (.binOp op e₁ e₂) (.binOp op e₁' e₂') .int := by
  obtain ⟨hc₁, hc₁', he₁⟩ := h₁
  obtain ⟨hc₂, hc₂', he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁', hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v₁, w₁, hb₁, hb₁', hv₁⟩ := he₁ θ₁ θ₂ δ hctx
  obtain ⟨v₂, w₂, hb₂, hb₂', hv₂⟩ := he₂ θ₁ θ₂ δ hctx
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl, rfl⟩ := hv₁
  obtain ⟨z₂, rfl, rfl⟩ := hv₂
  simp only [substMap, exprRel, valRel]
  cases hop
  · exact ⟨.litV (.litInt (z₁ + z₂)), .litV (.litInt (z₁ + z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩
  · exact ⟨.litV (.litInt (z₁ - z₂)), .litV (.litInt (z₁ - z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩
  · exact ⟨.litV (.litInt (z₁ * z₂)), .litV (.litInt (z₁ * z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩

theorem compat_int_bool_binop (Γ : TypingContext) (op : BinOp) (e₁ e₁' e₂ e₂' : Expr)
    (hop : BinOpTyped op .int .int .bool) (h₁ : semTyped Γ e₁ e₁' .int)
    (h₂ : semTyped Γ e₂ e₂' .int) : semTyped Γ (.binOp op e₁ e₂) (.binOp op e₁' e₂') .bool := by
  obtain ⟨hc₁, hc₁', he₁⟩ := h₁
  obtain ⟨hc₂, hc₂', he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁', hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v₁, w₁, hb₁, hb₁', hv₁⟩ := he₁ θ₁ θ₂ δ hctx
  obtain ⟨v₂, w₂, hb₂, hb₂', hv₂⟩ := he₂ θ₁ θ₂ δ hctx
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl, rfl⟩ := hv₁
  obtain ⟨z₂, rfl, rfl⟩ := hv₂
  simp only [substMap, exprRel, valRel]
  cases hop
  · exact ⟨.litV (.litBool (z₁ < z₂)), .litV (.litBool (z₁ < z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩
  · exact ⟨.litV (.litBool (z₁ ≤ z₂)), .litV (.litBool (z₁ ≤ z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩
  · exact ⟨.litV (.litBool (z₁ = z₂)), .litV (.litBool (z₁ = z₂)),
      .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, .bs_binop _ _ _ _ _ _ hb₁' hb₂' rfl, _, rfl, rfl⟩

theorem compat_unop (Γ : TypingContext) (op : UnOp) (A B : Ty) (e e' : Expr)
    (hop : UnOpTyped op A B) (h : semTyped Γ e e' A) :
    semTyped Γ (.unOp op e) (.unOp op e') B := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  cases hop
  · simp only [valRel] at hv
    obtain ⟨b, rfl, rfl⟩ := hv
    refine ⟨.litV (.litBool (!b)), .litV (.litBool (!b)),
      .bs_unop _ _ _ _ hb rfl, .bs_unop _ _ _ _ hb' rfl, ?_⟩
    simp only [valRel]
    exact ⟨_, rfl, rfl⟩
  · simp only [valRel] at hv
    obtain ⟨z, rfl, rfl⟩ := hv
    refine ⟨.litV (.litInt (-z)), .litV (.litInt (-z)),
      .bs_unop _ _ _ _ hb rfl, .bs_unop _ _ _ _ hb' rfl, ?_⟩
    simp only [valRel]
    exact ⟨_, rfl, rfl⟩

theorem compat_tlam (Γ : TypingContext) (e₁ e₂ : Expr) (A : Ty)
    (h : semTyped (shiftCtx Γ) e₁ e₂ A) : semTyped Γ (.tLam e₁) (.tLam e₂) (.all A) := by
  obtain ⟨hc₁, hc₂, he⟩ := h
  have hc₁' : closed Γ.domList e₁ := closed_weaken hc₁ fun y hy => mem_shiftCtx_domList.mp hy
  have hc₂' : closed Γ.domList e₂ := closed_weaken hc₂ fun y hy => mem_shiftCtx_domList.mp hy
  refine ⟨hc₁', hc₂', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨hθ₁, hθ₂⟩ := sem_context_rel_closed hctx
  simp only [substMap, exprRel]
  refine ⟨.tLamV (substMap θ₁ e₁), .tLamV (substMap θ₂ e₂), .bs_tlam _, .bs_tlam _, ?_⟩
  simp only [valRel]
  exact ⟨_, _, rfl, rfl,
    substMap_ctx_closed hc₁' (fun y => (sem_context_rel_domList hctx y).1) hθ₁,
    substMap_ctx_closed hc₂' (fun y => (sem_context_rel_domList hctx y).2) hθ₂,
    fun τ => he θ₁ θ₂ (τ .:₂ δ) (sem_context_rel_cons τ hctx)⟩

theorem compat_tapp (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' (.all A)) : semTyped Γ (.tApp e) (.tApp e') (A.subst1 B) := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [valRel] at hv
  obtain ⟨f₁, f₂, rfl, rfl, _, _, hbody⟩ := hv
  obtain ⟨u₁, u₂, hbu₁, hbu₂, hu⟩ := hbody (interp_type B δ)
  simp only [substMap, exprRel]
  exact ⟨u₁, u₂, .bs_tapp _ _ _ hb hbu₁, .bs_tapp _ _ _ hb' hbu₂,
    (sem_val_rel_move_single_subst B A δ u₁ u₂).mp hu⟩

theorem compat_pack (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' (A.subst1 B)) : semTyped Γ (.pack e) (.pack e') (.exist A) := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.packV v, .packV w, .bs_pack _ v hb, .bs_pack _ w hb', ?_⟩
  simp only [valRel]
  exact ⟨v, w, rfl, rfl, interp_type B δ, (sem_val_rel_move_single_subst B A δ v w).mpr hv⟩

theorem compat_unpack (Γ : TypingContext) (A B : Ty) (e₁ e₁' e₂ e₂' : Expr) (x : String)
    (h : semTyped Γ e₁ e₁' (.exist A))
    (h' : semTyped (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ) x A) e₂ e₂'
      (B.rename (· + 1))) :
    semTyped Γ (.unpack (.bNamed x) e₁ e₂) (.unpack (.bNamed x) e₁' e₂') B := by
  obtain ⟨hc₁, hc₁', he⟩ := h
  obtain ⟨hc₂, hc₂', he'⟩ := h'
  have hweak : ∀ e : Expr,
      closed (TypingContext.domList
        (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ) x A)) e →
      closed (x :: TypingContext.domList Γ) e := by
    intro e he
    refine closed_weaken he fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (mem_shiftCtx_domList.mp hy')
  refine ⟨?_, ?_, fun θ₁ θ₂ δ hctx => ?_⟩
  · simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨hc₁, hweak e₂ hc₂⟩
  · simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨hc₁', hweak e₂' hc₂'⟩
  · obtain ⟨hθ₁, hθ₂⟩ := sem_context_rel_closed hctx
    obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
    simp only [valRel] at hv
    obtain ⟨v', w', rfl, rfl, τ, hvw⟩ := hv
    obtain ⟨u₁, u₂, hbu₁, hbu₂, hu⟩ := he' (Iris.Std.insert (M := MapStr) θ₁ x v'.toExpr)
      (Iris.Std.insert (M := MapStr) θ₂ x w'.toExpr) (τ .:₂ δ)
      (.insert v' w' x A hvw (sem_context_rel_cons τ hctx))
    rw [← subst_substMap x v'.toExpr θ₁ e₂ hθ₁] at hbu₁
    rw [← subst_substMap x w'.toExpr θ₂ e₂' hθ₂] at hbu₂
    simp only [substMap, binderDelete, exprRel]
    exact ⟨u₁, u₂, .bs_unpack _ _ v' u₁ (.bNamed x) hb hbu₁,
      .bs_unpack _ _ w' u₂ (.bNamed x) hb' hbu₂, (sem_val_rel_cons B δ u₁ u₂ τ).mpr hu⟩

theorem compat_if (Γ : TypingContext) (e₀ e₀' e₁ e₁' e₂ e₂' : Expr) (A : Ty)
    (h₀ : semTyped Γ e₀ e₀' .bool) (h₁ : semTyped Γ e₁ e₁' A) (h₂ : semTyped Γ e₂ e₂' A) :
    semTyped Γ (.ite e₀ e₁ e₂) (.ite e₀' e₁' e₂') A := by
  obtain ⟨hc₀, hc₀', he₀⟩ := h₀
  obtain ⟨hc₁, hc₁', he₁⟩ := h₁
  obtain ⟨hc₂, hc₂', he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hc₀, hc₁⟩, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hc₀', hc₁'⟩, hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v₀, w₀, hb₀, hb₀', hv₀⟩ := he₀ θ₁ θ₂ δ hctx
  simp only [valRel] at hv₀
  obtain ⟨b, rfl, rfl⟩ := hv₀
  obtain ⟨v₁, w₁, hb₁, hb₁', hv₁⟩ := he₁ θ₁ θ₂ δ hctx
  obtain ⟨v₂, w₂, hb₂, hb₂', hv₂⟩ := he₂ θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  cases b
  · exact ⟨v₂, w₂, .bs_if_false _ _ _ v₂ hb₀ hb₂, .bs_if_false _ _ _ w₂ hb₀' hb₂', hv₂⟩
  · exact ⟨v₁, w₁, .bs_if_true _ _ _ v₁ hb₀ hb₁, .bs_if_true _ _ _ w₁ hb₀' hb₁', hv₁⟩

theorem compat_pair (Γ : TypingContext) (e₁ e₁' e₂ e₂' : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ e₁' A) (h₂ : semTyped Γ e₂ e₂' B) :
    semTyped Γ (.pair e₁ e₂) (.pair e₁' e₂') (.prod A B) := by
  obtain ⟨hc₁, hc₁', he₁⟩ := h₁
  obtain ⟨hc₂, hc₂', he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hc₁', hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v₁, w₁, hb₁, hb₁', hv₁⟩ := he₁ θ₁ θ₂ δ hctx
  obtain ⟨v₂, w₂, hb₂, hb₂', hv₂⟩ := he₂ θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.pairV v₁ v₂, .pairV w₁ w₂, .bs_pair _ _ v₁ v₂ hb₁ hb₂,
    .bs_pair _ _ w₁ w₂ hb₁' hb₂', ?_⟩
  simp only [valRel]
  exact ⟨v₁, v₂, w₁, w₂, rfl, rfl, hv₁, hv₂⟩

theorem compat_fst (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' (.prod A B)) : semTyped Γ (.fst e) (.fst e') A := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩ := hv
  simp only [substMap, exprRel]
  exact ⟨v₁, w₁, .bs_fst _ v₁ v₂ hb, .bs_fst _ w₁ w₂ hb', h₁⟩

theorem compat_snd (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' (.prod A B)) : semTyped Γ (.snd e) (.snd e') B := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, w₁, w₂, rfl, rfl, h₁, h₂⟩ := hv
  simp only [substMap, exprRel]
  exact ⟨v₂, w₂, .bs_snd _ v₁ v₂ hb, .bs_snd _ w₁ w₂ hb', h₂⟩

theorem compat_injl (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' A) : semTyped Γ (.injL e) (.injL e') (.sum A B) := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.injLV v, .injLV w, .bs_injl _ v hb, .bs_injl _ w hb', ?_⟩
  simp only [valRel]
  exact Or.inl ⟨v, w, rfl, rfl, hv⟩

theorem compat_injr (Γ : TypingContext) (e e' : Expr) (A B : Ty)
    (h : semTyped Γ e e' B) : semTyped Γ (.injR e) (.injR e') (.sum A B) := by
  obtain ⟨hc, hc', he⟩ := h
  refine ⟨hc, hc', fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.injRV v, .injRV w, .bs_injr _ v hb, .bs_injr _ w hb', ?_⟩
  simp only [valRel]
  exact Or.inr ⟨v, w, rfl, rfl, hv⟩

theorem compat_case (Γ : TypingContext) (e e' e₁ e₁' e₂ e₂' : Expr) (A B C : Ty)
    (h : semTyped Γ e e' (.sum B C)) (h₁ : semTyped Γ e₁ e₁' (.fn B A))
    (h₂ : semTyped Γ e₂ e₂' (.fn C A)) :
    semTyped Γ (.case e e₁ e₂) (.case e' e₁' e₂') A := by
  obtain ⟨hc, hc', he⟩ := h
  obtain ⟨hc₁, hc₁', he₁⟩ := h₁
  obtain ⟨hc₂, hc₂', he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hc, hc₁⟩, hc₂⟩,
    by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hc', hc₁'⟩, hc₂'⟩,
    fun θ₁ θ₂ δ hctx => ?_⟩
  obtain ⟨v, w, hb, hb', hv⟩ := he θ₁ θ₂ δ hctx
  simp only [valRel] at hv
  simp only [substMap, exprRel]
  rcases hv with ⟨v', w', rfl, rfl, hvw⟩ | ⟨v', w', rfl, rfl, hvw⟩
  · obtain ⟨f₁, f₂, hbf₁, hbf₂, hf⟩ := he₁ θ₁ θ₂ δ hctx
    simp only [valRel] at hf
    obtain ⟨x, y, g₁, g₂, rfl, rfl, _, _, hbody⟩ := hf
    obtain ⟨u₁, u₂, hbu₁, hbu₂, hu⟩ := hbody v' w' hvw
    exact ⟨u₁, u₂,
      .bs_casel _ _ _ v' u₁ hb (.bs_app _ _ x g₁ v' u₁ hbf₁ (big_step_of_val rfl) hbu₁),
      .bs_casel _ _ _ w' u₂ hb' (.bs_app _ _ y g₂ w' u₂ hbf₂ (big_step_of_val rfl) hbu₂), hu⟩
  · obtain ⟨f₁, f₂, hbf₁, hbf₂, hf⟩ := he₂ θ₁ θ₂ δ hctx
    simp only [valRel] at hf
    obtain ⟨x, y, g₁, g₂, rfl, rfl, _, _, hbody⟩ := hf
    obtain ⟨u₁, u₂, hbu₁, hbu₂, hu⟩ := hbody v' w' hvw
    exact ⟨u₁, u₂,
      .bs_caser _ _ _ v' u₁ hb (.bs_app _ _ x g₁ v' u₁ hbf₁ (big_step_of_val rfl) hbu₁),
      .bs_caser _ _ _ w' u₂ hb' (.bs_app _ _ y g₂ w' u₂ hbf₂ (big_step_of_val rfl) hbu₂), hu⟩

/-! ## The fundamental theorem -/

/-- Every syntactically typed term is related to itself. -/
theorem sem_soundness {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (h : SynTyped n Γ e A) : semTyped Γ e e A := by
  induction h with
  | typed_lit_int _ Γ z => exact compat_int Γ z
  | typed_lit_bool _ Γ b => exact compat_bool Γ b
  | typed_lit_unit _ Γ => exact compat_unit Γ
  | typed_var _ Γ x A hx => exact compat_var Γ x A hx
  | typed_lam _ Γ x e A B _ _ ih => exact compat_lam_named Γ x e e A B ih
  | typed_lam_anon _ Γ e A B _ _ ih => exact compat_lam_anon Γ e e A B ih
  | typed_app _ Γ e₁ e₂ A B _ _ ih₁ ih₂ => exact compat_app Γ e₁ e₁ e₂ e₂ A B ih₁ ih₂
  | typed_tLam _ Γ e A _ ih => exact compat_tlam Γ e e A ih
  | typed_tApp _ Γ e A B _ _ ih => exact compat_tapp Γ e e A B ih
  | typed_pack _ Γ e A B _ _ _ ih => exact compat_pack Γ e e A B ih
  | typed_unpack _ Γ x e₁ e₂ A B _ _ _ ih₁ ih₂ =>
    exact compat_unpack Γ A B e₁ e₁ e₂ e₂ x ih₁ ih₂
  | typed_pair _ Γ e₁ e₂ A B _ _ ih₁ ih₂ => exact compat_pair Γ e₁ e₁ e₂ e₂ A B ih₁ ih₂
  | typed_fst _ Γ e A B _ ih => exact compat_fst Γ e e A B ih
  | typed_snd _ Γ e A B _ ih => exact compat_snd Γ e e A B ih
  | typed_injL _ Γ e A B _ _ ih => exact compat_injl Γ e e A B ih
  | typed_injR _ Γ e A B _ _ ih => exact compat_injr Γ e e A B ih
  | typed_case _ Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂ =>
    exact compat_case Γ e e e₁ e₁ e₂ e₂ C A B ih ih₁ ih₂
  | typed_unOp _ Γ op e A B hop _ ih => exact compat_unop Γ op A B e e hop ih
  | typed_binOp _ Γ op e₁ e₂ A B C hop _ _ ih₁ ih₂ =>
    cases hop <;>
      first
        | exact compat_int_binop Γ _ e₁ e₁ e₂ e₂ (by constructor) ih₁ ih₂
        | exact compat_int_bool_binop Γ _ e₁ e₁ e₂ e₂ (by constructor) ih₁ ih₂
  | typed_if _ Γ e₀ e₁ e₂ A _ _ _ ih₀ ih₁ ih₂ => exact compat_if Γ e₀ e₀ e₁ e₁ e₂ e₂ A ih₀ ih₁ ih₂

/-- The dummy interpretation: any two closed values. -/
def any_type : SemType where
  car v w := closed [] v.toExpr ∧ closed [] w.toExpr
  closed_val _ _ h := h

def δ_any : TyVarInterp := fun _ => any_type

/-! ## Program contexts and contextual equivalence -/

/-- An expression with a single hole, in an arbitrary (not necessarily evaluation)
position. -/
inductive Pctx where
  | holePCtx
  | appLPCtx (C : Pctx) (e₂ : Expr)
  | appRPCtx (e₁ : Expr) (C : Pctx)
  | tAppPCtx (C : Pctx)
  | packPCtx (C : Pctx)
  | unpackLPCtx (x : Binder) (C : Pctx) (e₂ : Expr)
  | unpackRPCtx (x : Binder) (e₁ : Expr) (C : Pctx)
  | unOpPCtx (op : UnOp) (C : Pctx)
  | binOpLPCtx (op : BinOp) (C : Pctx) (e₂ : Expr)
  | binOpRPCtx (op : BinOp) (e₁ : Expr) (C : Pctx)
  | ifPCtx (C : Pctx) (e₁ e₂ : Expr)
  | ifTPCtx (e : Expr) (C : Pctx) (e₂ : Expr)
  | ifEPCtx (e e₁ : Expr) (C : Pctx)
  | pairLPCtx (C : Pctx) (e₂ : Expr)
  | pairRPCtx (e₁ : Expr) (C : Pctx)
  | fstPCtx (C : Pctx)
  | sndPCtx (C : Pctx)
  | injLPCtx (C : Pctx)
  | injRPCtx (C : Pctx)
  | casePCtx (C : Pctx) (e₁ e₂ : Expr)
  | caseTPCtx (e : Expr) (C : Pctx) (e₂ : Expr)
  | caseEPCtx (e e₁ : Expr) (C : Pctx)
  | lamPCtx (x : Binder) (C : Pctx)
  | tLamPCtx (C : Pctx)

def pfill : Pctx → Expr → Expr
  | .holePCtx, e => e
  | .appLPCtx K e₂, e => .app (pfill K e) e₂
  | .appRPCtx e₁ K, e => .app e₁ (pfill K e)
  | .tAppPCtx K, e => .tApp (pfill K e)
  | .packPCtx K, e => .pack (pfill K e)
  | .unpackLPCtx x K e₂, e => .unpack x (pfill K e) e₂
  | .unpackRPCtx x e₁ K, e => .unpack x e₁ (pfill K e)
  | .unOpPCtx op K, e => .unOp op (pfill K e)
  | .binOpLPCtx op K e₂, e => .binOp op (pfill K e) e₂
  | .binOpRPCtx op e₁ K, e => .binOp op e₁ (pfill K e)
  | .ifPCtx K e₁ e₂, e => .ite (pfill K e) e₁ e₂
  | .ifTPCtx e' K e₂, e => .ite e' (pfill K e) e₂
  | .ifEPCtx e' e₁ K, e => .ite e' e₁ (pfill K e)
  | .pairLPCtx K e₂, e => .pair (pfill K e) e₂
  | .pairRPCtx e₁ K, e => .pair e₁ (pfill K e)
  | .fstPCtx K, e => .fst (pfill K e)
  | .sndPCtx K, e => .snd (pfill K e)
  | .injLPCtx K, e => .injL (pfill K e)
  | .injRPCtx K, e => .injR (pfill K e)
  | .casePCtx K e₁ e₂, e => .case (pfill K e) e₁ e₂
  | .caseTPCtx e' K e₂, e => .case e' (pfill K e) e₂
  | .caseEPCtx e' e₁ K, e => .case e' e₁ (pfill K e)
  | .lamPCtx x K, e => .lam x (pfill K e)
  | .tLamPCtx K, e => .tLam (pfill K e)

/-- `PctxTyped Δ Γ A K Δ' Γ' B` says that plugging a `Δ; Γ ⊢ _ : A` term into
`K` yields a `Δ'; Γ' ⊢ _ : B` term. -/
inductive PctxTyped (Δ : Nat) (Γ : TypingContext) (A : Ty) :
    Pctx → Nat → TypingContext → Ty → Prop where
  | pctx_typed_HolePCtx : PctxTyped Δ Γ A .holePCtx Δ Γ A
  | pctx_typed_AppLPCtx K e₂ B C Δ' Γ' :
      PctxTyped Δ Γ A K Δ' Γ' (.fn B C) →
      SynTyped Δ' Γ' e₂ B →
      PctxTyped Δ Γ A (.appLPCtx K e₂) Δ' Γ' C
  | pctx_typed_AppRPCtx e₁ K B C Δ' Γ' :
      SynTyped Δ' Γ' e₁ (.fn B C) →
      PctxTyped Δ Γ A K Δ' Γ' B →
      PctxTyped Δ Γ A (.appRPCtx e₁ K) Δ' Γ' C
  | pctx_typed_TLamPCtx K B Δ' Γ' :
      PctxTyped Δ Γ A K (Δ' + 1) (shiftCtx Γ') B →
      PctxTyped Δ Γ A (.tLamPCtx K) Δ' Γ' (.all B)
  | pctx_typed_TAppPCtx K B C Δ' Γ' :
      TypeWf Δ' C →
      PctxTyped Δ Γ A K Δ' Γ' (.all B) →
      PctxTyped Δ Γ A (.tAppPCtx K) Δ' Γ' (B.subst1 C)
  | pctx_typed_PackPCtx K B C Δ' Γ' :
      TypeWf Δ' C →
      TypeWf (Δ' + 1) B →
      PctxTyped Δ Γ A K Δ' Γ' (B.subst1 C) →
      PctxTyped Δ Γ A (.packPCtx K) Δ' Γ' (.exist B)
  | pctx_typed_UnpackLPCtx (x : String) K e₂ B C Δ' Γ' :
      TypeWf Δ' C →
      PctxTyped Δ Γ A K Δ' Γ' (.exist B) →
      SynTyped (Δ' + 1) (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ') x B) e₂
        (C.rename (· + 1)) →
      PctxTyped Δ Γ A (.unpackLPCtx (.bNamed x) K e₂) Δ' Γ' C
  | pctx_typed_UnpackRPCtx (x : String) e₁ K B C Δ' Γ' :
      TypeWf Δ' C →
      SynTyped Δ' Γ' e₁ (.exist B) →
      PctxTyped Δ Γ A K (Δ' + 1) (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ') x B)
        (C.rename (· + 1)) →
      PctxTyped Δ Γ A (.unpackRPCtx (.bNamed x) e₁ K) Δ' Γ' C
  | pctx_typed_UnOpPCtx op K Δ' Γ' B C :
      UnOpTyped op B C →
      PctxTyped Δ Γ A K Δ' Γ' B →
      PctxTyped Δ Γ A (.unOpPCtx op K) Δ' Γ' C
  | pctx_typed_BinOpLPCtx op K e₂ B₁ B₂ C Δ' Γ' :
      BinOpTyped op B₁ B₂ C →
      PctxTyped Δ Γ A K Δ' Γ' B₁ →
      SynTyped Δ' Γ' e₂ B₂ →
      PctxTyped Δ Γ A (.binOpLPCtx op K e₂) Δ' Γ' C
  | pctx_typed_BinOpRPCtx op K e₁ B₁ B₂ C Δ' Γ' :
      BinOpTyped op B₁ B₂ C →
      SynTyped Δ' Γ' e₁ B₁ →
      PctxTyped Δ Γ A K Δ' Γ' B₂ →
      PctxTyped Δ Γ A (.binOpRPCtx op e₁ K) Δ' Γ' C
  | pctx_typed_IfPCtx K e₁ e₂ B Δ' Γ' :
      PctxTyped Δ Γ A K Δ' Γ' .bool →
      SynTyped Δ' Γ' e₁ B →
      SynTyped Δ' Γ' e₂ B →
      PctxTyped Δ Γ A (.ifPCtx K e₁ e₂) Δ' Γ' B
  | pctx_typed_IfTPCtx K e e₂ B Δ' Γ' :
      SynTyped Δ' Γ' e .bool →
      PctxTyped Δ Γ A K Δ' Γ' B →
      SynTyped Δ' Γ' e₂ B →
      PctxTyped Δ Γ A (.ifTPCtx e K e₂) Δ' Γ' B
  | pctx_typed_IfEPCtx K e e₁ B Δ' Γ' :
      SynTyped Δ' Γ' e .bool →
      SynTyped Δ' Γ' e₁ B →
      PctxTyped Δ Γ A K Δ' Γ' B →
      PctxTyped Δ Γ A (.ifEPCtx e e₁ K) Δ' Γ' B
  | pctx_typed_PairLPCtx K e₂ B₁ B₂ Δ' Γ' :
      PctxTyped Δ Γ A K Δ' Γ' B₁ →
      SynTyped Δ' Γ' e₂ B₂ →
      PctxTyped Δ Γ A (.pairLPCtx K e₂) Δ' Γ' (.prod B₁ B₂)
  | pctx_typed_PairRPCtx K e₁ B₁ B₂ Δ' Γ' :
      SynTyped Δ' Γ' e₁ B₁ →
      PctxTyped Δ Γ A K Δ' Γ' B₂ →
      PctxTyped Δ Γ A (.pairRPCtx e₁ K) Δ' Γ' (.prod B₁ B₂)
  | pctx_typed_FstPCtx K Δ' Γ' B C :
      PctxTyped Δ Γ A K Δ' Γ' (.prod B C) →
      PctxTyped Δ Γ A (.fstPCtx K) Δ' Γ' B
  | pctx_typed_SndPCtx K Δ' Γ' B C :
      PctxTyped Δ Γ A K Δ' Γ' (.prod B C) →
      PctxTyped Δ Γ A (.sndPCtx K) Δ' Γ' C
  | pctx_typed_InjLPCtx K Δ' Γ' B C :
      TypeWf Δ' C →
      PctxTyped Δ Γ A K Δ' Γ' B →
      PctxTyped Δ Γ A (.injLPCtx K) Δ' Γ' (.sum B C)
  | pctx_typed_InjRPCtx K Δ' Γ' B C :
      TypeWf Δ' B →
      PctxTyped Δ Γ A K Δ' Γ' C →
      PctxTyped Δ Γ A (.injRPCtx K) Δ' Γ' (.sum B C)
  | pctx_typed_CasePCtx K e₁ e₂ B C D Δ' Γ' :
      PctxTyped Δ Γ A K Δ' Γ' (.sum B C) →
      SynTyped Δ' Γ' e₁ (.fn B D) →
      SynTyped Δ' Γ' e₂ (.fn C D) →
      PctxTyped Δ Γ A (.casePCtx K e₁ e₂) Δ' Γ' D
  | pctx_typed_CaseTPCtx K e e₂ B C D Δ' Γ' :
      SynTyped Δ' Γ' e (.sum B C) →
      PctxTyped Δ Γ A K Δ' Γ' (.fn B D) →
      SynTyped Δ' Γ' e₂ (.fn C D) →
      PctxTyped Δ Γ A (.caseTPCtx e K e₂) Δ' Γ' D
  | pctx_typed_CaseEPCtx K e e₁ B C D Δ' Γ' :
      SynTyped Δ' Γ' e (.sum B C) →
      SynTyped Δ' Γ' e₁ (.fn B D) →
      PctxTyped Δ Γ A K Δ' Γ' (.fn C D) →
      PctxTyped Δ Γ A (.caseEPCtx e e₁ K) Δ' Γ' D
  | pctx_typed_named_LamPCtx (x : String) K B C Γ' Δ' :
      TypeWf Δ' B →
      PctxTyped Δ Γ A K Δ' (Iris.Std.insert (M := TyMapStr) Γ' x B) C →
      PctxTyped Δ Γ A (.lamPCtx (.bNamed x) K) Δ' Γ' (.fn B C)
  | pctx_typed_anon_LamPCtx K B C Γ' Δ' :
      TypeWf Δ' B →
      PctxTyped Δ Γ A K Δ' Γ' C →
      PctxTyped Δ Γ A (.lamPCtx .bAnon K) Δ' Γ' (.fn B C)

theorem pfill_typed {C : Pctx} {Δ Δ' : Nat} {Γ Γ' : TypingContext} {e : Expr} {A B : Ty}
    (hC : PctxTyped Δ Γ A C Δ' Γ' B) (he : SynTyped Δ Γ e A) :
    SynTyped Δ' Γ' (pfill C e) B := by
  induction hC with
  | pctx_typed_HolePCtx => exact he
  | pctx_typed_AppLPCtx K e₂ B C Δ' Γ' _ h₂ ih => exact .typed_app _ _ _ _ _ _ ih h₂
  | pctx_typed_AppRPCtx e₁ K B C Δ' Γ' h₁ _ ih => exact .typed_app _ _ _ _ _ _ h₁ ih
  | pctx_typed_TLamPCtx K B Δ' Γ' _ ih => exact .typed_tLam _ _ _ _ ih
  | pctx_typed_TAppPCtx K B C Δ' Γ' hwf _ ih => exact .typed_tApp _ _ _ _ _ hwf ih
  | pctx_typed_PackPCtx K B C Δ' Γ' hwf₁ hwf₂ _ ih => exact .typed_pack _ _ _ _ _ hwf₁ hwf₂ ih
  | pctx_typed_UnpackLPCtx x K e₂ B C Δ' Γ' hwf _ h₂ ih =>
    exact .typed_unpack _ _ _ _ _ _ _ hwf ih h₂
  | pctx_typed_UnpackRPCtx x e₁ K B C Δ' Γ' hwf h₁ _ ih =>
    exact .typed_unpack _ _ _ _ _ _ _ hwf h₁ ih
  | pctx_typed_UnOpPCtx op K Δ' Γ' B C hop _ ih => exact .typed_unOp _ _ _ _ _ _ hop ih
  | pctx_typed_BinOpLPCtx op K e₂ B₁ B₂ C Δ' Γ' hop _ h₂ ih =>
    exact .typed_binOp _ _ _ _ _ _ _ _ hop ih h₂
  | pctx_typed_BinOpRPCtx op K e₁ B₁ B₂ C Δ' Γ' hop h₁ _ ih =>
    exact .typed_binOp _ _ _ _ _ _ _ _ hop h₁ ih
  | pctx_typed_IfPCtx K e₁ e₂ B Δ' Γ' _ h₁ h₂ ih => exact .typed_if _ _ _ _ _ _ ih h₁ h₂
  | pctx_typed_IfTPCtx K e e₂ B Δ' Γ' h₀ _ h₂ ih => exact .typed_if _ _ _ _ _ _ h₀ ih h₂
  | pctx_typed_IfEPCtx K e e₁ B Δ' Γ' h₀ h₁ _ ih => exact .typed_if _ _ _ _ _ _ h₀ h₁ ih
  | pctx_typed_PairLPCtx K e₂ B₁ B₂ Δ' Γ' _ h₂ ih => exact .typed_pair _ _ _ _ _ _ ih h₂
  | pctx_typed_PairRPCtx K e₁ B₁ B₂ Δ' Γ' h₁ _ ih => exact .typed_pair _ _ _ _ _ _ h₁ ih
  | pctx_typed_FstPCtx K Δ' Γ' B C _ ih => exact .typed_fst _ _ _ _ _ ih
  | pctx_typed_SndPCtx K Δ' Γ' B C _ ih => exact .typed_snd _ _ _ _ _ ih
  | pctx_typed_InjLPCtx K Δ' Γ' B C hwf _ ih => exact .typed_injL _ _ _ _ _ hwf ih
  | pctx_typed_InjRPCtx K Δ' Γ' B C hwf _ ih => exact .typed_injR _ _ _ _ _ hwf ih
  | pctx_typed_CasePCtx K e₁ e₂ B C D Δ' Γ' _ h₁ h₂ ih => exact .typed_case _ _ _ _ _ _ _ _ ih h₁ h₂
  | pctx_typed_CaseTPCtx K e e₂ B C D Δ' Γ' h₀ _ h₂ ih => exact .typed_case _ _ _ _ _ _ _ _ h₀ ih h₂
  | pctx_typed_CaseEPCtx K e e₁ B C D Δ' Γ' h₀ h₁ _ ih => exact .typed_case _ _ _ _ _ _ _ _ h₀ h₁ ih
  | pctx_typed_named_LamPCtx x K B C Γ' Δ' hwf _ ih => exact .typed_lam _ _ _ _ _ _ hwf ih
  | pctx_typed_anon_LamPCtx K B C Γ' Δ' hwf _ ih => exact .typed_lam_anon _ _ _ _ _ hwf ih

/-- Rocq's `syn_typed_closed` specialised to the context's own domain. -/
theorem syn_typed_closed_dom {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (ht : SynTyped n Γ e A) : closed Γ.domList e :=
  syn_typed_closed ht fun x hx => by
    cases hget : get? (M := TyMapStr) Γ x with
    | none => exact absurd hget hx
    | some C => exact mem_ctx_domList.mpr ⟨C, hget⟩

/-- Weakening past one term binder over a shifted context. -/
private theorem closed_insert_shift {Γ : TypingContext} {x : String} {B : Ty} {e : Expr}
    (h : closed (TypingContext.domList
      (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ) x B)) e) :
    closed (x :: Γ.domList) e :=
  closed_weaken h fun y hy => by
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (mem_shiftCtx_domList.mp hy')

/-- Weakening past one term binder. -/
private theorem closed_insert {Γ : TypingContext} {x : String} {B : Ty} {e : Expr}
    (h : closed (TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x B)) e) :
    closed (x :: Γ.domList) e :=
  closed_weaken h fun y hy => by
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ hy'

/-- Introduce a two-way conjunctive closedness goal. -/
private theorem and_true_intro {b₁ b₂ : Bool} (h₁ : b₁ = true) (h₂ : b₂ = true) :
    (b₁ && b₂) = true := by simp [h₁, h₂]

theorem pctx_typed_fill_closed {Δ Δ' : Nat} {Γ Γ' : TypingContext} {A B : Ty} {K : Pctx}
    {e : Expr} (hcl : closed Γ.domList e) (hK : PctxTyped Δ Γ A K Δ' Γ' B) :
    closed Γ'.domList (pfill K e) := by
  induction hK with
  | pctx_typed_HolePCtx => exact hcl
  | pctx_typed_AppLPCtx K e₂ B C Δ' Γ' _ h₂ ih =>
    exact and_true_intro ih (syn_typed_closed_dom h₂)
  | pctx_typed_AppRPCtx e₁ K B C Δ' Γ' h₁ _ ih =>
    exact and_true_intro (syn_typed_closed_dom h₁) ih
  | pctx_typed_TLamPCtx K B Δ' Γ' _ ih =>
    exact closed_weaken ih fun y hy => mem_shiftCtx_domList.mp hy
  | pctx_typed_TAppPCtx K B C Δ' Γ' hwf _ ih => exact ih
  | pctx_typed_PackPCtx K B C Δ' Γ' _ _ _ ih => exact ih
  | pctx_typed_UnpackLPCtx x K e₂ B C Δ' Γ' _ _ h₂ ih =>
    exact and_true_intro ih (closed_insert_shift (syn_typed_closed_dom h₂))
  | pctx_typed_UnpackRPCtx x e₁ K B C Δ' Γ' _ h₁ _ ih =>
    exact and_true_intro (syn_typed_closed_dom h₁) (closed_insert_shift ih)
  | pctx_typed_UnOpPCtx op K Δ' Γ' B C _ _ ih => exact ih
  | pctx_typed_BinOpLPCtx op K e₂ B₁ B₂ C Δ' Γ' _ _ h₂ ih =>
    exact and_true_intro ih (syn_typed_closed_dom h₂)
  | pctx_typed_BinOpRPCtx op K e₁ B₁ B₂ C Δ' Γ' _ h₁ _ ih =>
    exact and_true_intro (syn_typed_closed_dom h₁) ih
  | pctx_typed_IfPCtx K e₁ e₂ B Δ' Γ' _ h₁ h₂ ih =>
    exact and_true_intro (and_true_intro ih (syn_typed_closed_dom h₁)) (syn_typed_closed_dom h₂)
  | pctx_typed_IfTPCtx K e e₂ B Δ' Γ' h₀ _ h₂ ih =>
    exact and_true_intro (and_true_intro (syn_typed_closed_dom h₀) ih) (syn_typed_closed_dom h₂)
  | pctx_typed_IfEPCtx K e e₁ B Δ' Γ' h₀ h₁ _ ih =>
    exact and_true_intro
      (and_true_intro (syn_typed_closed_dom h₀) (syn_typed_closed_dom h₁)) ih
  | pctx_typed_PairLPCtx K e₂ B₁ B₂ Δ' Γ' _ h₂ ih =>
    exact and_true_intro ih (syn_typed_closed_dom h₂)
  | pctx_typed_PairRPCtx K e₁ B₁ B₂ Δ' Γ' h₁ _ ih =>
    exact and_true_intro (syn_typed_closed_dom h₁) ih
  | pctx_typed_FstPCtx K Δ' Γ' B C _ ih => exact ih
  | pctx_typed_SndPCtx K Δ' Γ' B C _ ih => exact ih
  | pctx_typed_InjLPCtx K Δ' Γ' B C _ _ ih => exact ih
  | pctx_typed_InjRPCtx K Δ' Γ' B C _ _ ih => exact ih
  | pctx_typed_CasePCtx K e₁ e₂ B C D Δ' Γ' _ h₁ h₂ ih =>
    exact and_true_intro (and_true_intro ih (syn_typed_closed_dom h₁)) (syn_typed_closed_dom h₂)
  | pctx_typed_CaseTPCtx K e e₂ B C D Δ' Γ' h₀ _ h₂ ih =>
    exact and_true_intro (and_true_intro (syn_typed_closed_dom h₀) ih) (syn_typed_closed_dom h₂)
  | pctx_typed_CaseEPCtx K e e₁ B C D Δ' Γ' h₀ h₁ _ ih =>
    exact and_true_intro
      (and_true_intro (syn_typed_closed_dom h₀) (syn_typed_closed_dom h₁)) ih
  | pctx_typed_named_LamPCtx x K B C Γ' Δ' _ _ ih => exact closed_insert ih
  | pctx_typed_anon_LamPCtx K B C Γ' Δ' _ _ ih => exact ih

theorem sem_typed_congruence {Δ Δ' : Nat} {Γ Γ' : TypingContext} {e₁ e₂ : Expr} {C : Pctx}
    {A B : Ty} (hsem : semTyped Γ e₁ e₂ A) (hK : PctxTyped Δ Γ A C Δ' Γ' B) :
    semTyped Γ' (pfill C e₁) (pfill C e₂) B := by
  induction hK with
  | pctx_typed_HolePCtx => exact hsem
  | pctx_typed_AppLPCtx K e₂' B C Δ' Γ' _ h₂ ih =>
    exact compat_app Γ' _ _ e₂' e₂' B C ih (sem_soundness h₂)
  | pctx_typed_AppRPCtx e₁' K B C Δ' Γ' h₁ _ ih =>
    exact compat_app Γ' e₁' e₁' _ _ B C (sem_soundness h₁) ih
  | pctx_typed_TLamPCtx K B Δ' Γ' _ ih => exact compat_tlam Γ' _ _ B ih
  | pctx_typed_TAppPCtx K B C Δ' Γ' _ _ ih => exact compat_tapp Γ' _ _ B C ih
  | pctx_typed_PackPCtx K B C Δ' Γ' _ _ _ ih => exact compat_pack Γ' _ _ B C ih
  | pctx_typed_UnpackLPCtx x K e₂' B C Δ' Γ' _ _ h₂ ih =>
    exact compat_unpack Γ' B C _ _ e₂' e₂' x ih (sem_soundness h₂)
  | pctx_typed_UnpackRPCtx x e₁' K B C Δ' Γ' _ h₁ _ ih =>
    exact compat_unpack Γ' B C e₁' e₁' _ _ x (sem_soundness h₁) ih
  | pctx_typed_UnOpPCtx op K Δ' Γ' B C hop _ ih => exact compat_unop Γ' op B C _ _ hop ih
  | pctx_typed_BinOpLPCtx op K e₂' B₁ B₂ C Δ' Γ' hop _ h₂ ih =>
    cases hop <;>
      first
        | exact compat_int_binop Γ' _ _ _ e₂' e₂' (by constructor) ih (sem_soundness h₂)
        | exact compat_int_bool_binop Γ' _ _ _ e₂' e₂' (by constructor) ih (sem_soundness h₂)
  | pctx_typed_BinOpRPCtx op K e₁' B₁ B₂ C Δ' Γ' hop h₁ _ ih =>
    cases hop <;>
      first
        | exact compat_int_binop Γ' _ e₁' e₁' _ _ (by constructor) (sem_soundness h₁) ih
        | exact compat_int_bool_binop Γ' _ e₁' e₁' _ _ (by constructor) (sem_soundness h₁) ih
  | pctx_typed_IfPCtx K e₁' e₂' B Δ' Γ' _ h₁ h₂ ih =>
    exact compat_if Γ' _ _ e₁' e₁' e₂' e₂' B ih (sem_soundness h₁) (sem_soundness h₂)
  | pctx_typed_IfTPCtx K e e₂' B Δ' Γ' h₀ _ h₂ ih =>
    exact compat_if Γ' e e _ _ e₂' e₂' B (sem_soundness h₀) ih (sem_soundness h₂)
  | pctx_typed_IfEPCtx K e e₁' B Δ' Γ' h₀ h₁ _ ih =>
    exact compat_if Γ' e e e₁' e₁' _ _ B (sem_soundness h₀) (sem_soundness h₁) ih
  | pctx_typed_PairLPCtx K e₂' B₁ B₂ Δ' Γ' _ h₂ ih =>
    exact compat_pair Γ' _ _ e₂' e₂' B₁ B₂ ih (sem_soundness h₂)
  | pctx_typed_PairRPCtx K e₁' B₁ B₂ Δ' Γ' h₁ _ ih =>
    exact compat_pair Γ' e₁' e₁' _ _ B₁ B₂ (sem_soundness h₁) ih
  | pctx_typed_FstPCtx K Δ' Γ' B C _ ih => exact compat_fst Γ' _ _ B C ih
  | pctx_typed_SndPCtx K Δ' Γ' B C _ ih => exact compat_snd Γ' _ _ B C ih
  | pctx_typed_InjLPCtx K Δ' Γ' B C _ _ ih => exact compat_injl Γ' _ _ B C ih
  | pctx_typed_InjRPCtx K Δ' Γ' B C _ _ ih => exact compat_injr Γ' _ _ B C ih
  | pctx_typed_CasePCtx K e₁' e₂' B C D Δ' Γ' _ h₁ h₂ ih =>
    exact compat_case Γ' _ _ e₁' e₁' e₂' e₂' D B C ih (sem_soundness h₁) (sem_soundness h₂)
  | pctx_typed_CaseTPCtx K e e₂' B C D Δ' Γ' h₀ _ h₂ ih =>
    exact compat_case Γ' e e _ _ e₂' e₂' D B C (sem_soundness h₀) ih (sem_soundness h₂)
  | pctx_typed_CaseEPCtx K e e₁' B C D Δ' Γ' h₀ h₁ _ ih =>
    exact compat_case Γ' e e e₁' e₁' _ _ D B C (sem_soundness h₀) (sem_soundness h₁) ih
  | pctx_typed_named_LamPCtx x K B C Γ' Δ' _ _ ih => exact compat_lam_named Γ' x _ _ B C ih
  | pctx_typed_anon_LamPCtx K B C Γ' Δ' _ _ ih => exact compat_lam_anon Γ' _ _ B C ih

/-- At type `Int`, related expressions compute the same integer. -/
theorem adequacy (δ : TyVarInterp) (e₁ e₂ : Expr) (h : exprRel δ .int e₁ e₂) :
    ∃ z : Int, BigStep e₁ (.litV (.litInt z)) ∧ BigStep e₂ (.litV (.litInt z)) := by
  obtain ⟨v₁, v₂, hb₁, hb₂, hv⟩ := h
  simp only [valRel] at hv
  obtain ⟨z, rfl, rfl⟩ := hv
  exact ⟨z, hb₁, hb₂⟩

def ctx_equiv (Δ : Nat) (Γ : TypingContext) (e₁ e₂ : Expr) (A : Ty) : Prop :=
  ∀ K : Pctx, PctxTyped Δ Γ A K 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) .int →
    ∃ z : Int, BigStep (pfill K e₁) (.litV (.litInt z)) ∧
      BigStep (pfill K e₂) (.litV (.litInt z))

/-- Semantic equivalence implies contextual equivalence. -/
theorem sem_typing_ctx_equiv {Δ : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {A : Ty}
    (hsem : semTyped Γ e₁ e₂ A) : ctx_equiv Δ Γ e₁ e₂ A := by
  intro K hK
  obtain ⟨_, _, hty⟩ := sem_typed_congruence hsem hK
  have he := hty (PartialMap.empty (M := MapStr) (V := Expr))
    (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty, substMap_empty] at he
  exact adequacy δ_any _ _ he

theorem soundness_wrt_ctx_equiv {Δ : Nat} {Γ : TypingContext} {e₁ e₂ : Expr} {A : Ty}
    (_h₁ : SynTyped Δ Γ e₁ A) (_h₂ : SynTyped Δ Γ e₂ A) (hsem : semTyped Γ e₁ e₂ A) :
    ctx_equiv Δ Γ e₁ e₂ A :=
  sem_typing_ctx_equiv hsem

end SystemF.Binary
