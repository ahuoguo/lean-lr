import LeanLR.TypeSystems.SystemFMu.Lang
import LeanLR.TypeSystems.SystemFMu.Notation
import LeanLR.TypeSystems.SystemFMu.Types
import LeanLR.TypeSystems.SystemFMu.TypeSafety
import LeanLR.TypeSystems.SystemFMu.Pure
import LeanLR.TypeSystems.SystemFMu.ParallelSubst

/-!
# System F + μ: the step-indexed logical relation

`systemf_mu/logrel.v`. `valRel δ A k v` says `v` behaves like an `A` for `k` more steps; unrolling
a `μ` spends one step. This is `SystemFMuState/LogRel.lean` without the heap.
-/

open Iris.Std

namespace SystemFMu

/-! ## Semantic types -/

/-- A step-indexed predicate on values, closed under lowering the index and
holding only of closed values. -/
structure SemType where
  car : Nat → Val → Prop
  closed_val : ∀ k v, car k v → closed [] v.toExpr
  mono : ∀ k k' v, car k v → k' ≤ k → car k' v

abbrev TyVarInterp := Nat → SemType

/-- Autosubst's `τ .: δ`. -/
def TyVarInterp.cons (τ : SemType) (δ : TyVarInterp) : TyVarInterp
  | 0 => τ
  | n + 1 => δ n

@[inherit_doc] notation:max τ " .: " δ => TyVarInterp.cons τ δ

@[simp] theorem cons_zero (τ : SemType) (δ : TyVarInterp) : (τ .: δ) 0 = τ := rfl

@[simp] theorem cons_succ (τ : SemType) (δ : TyVarInterp) (n : Nat) : (τ .: δ) (n + 1) = δ n := rfl

/-- Unrolling a `μ` grows the type, so the recursion is on the step index
there; the other constructors decrease this measure. -/
def Ty.size : Ty → Nat
  | .tVar _ => 1
  | .int => 1
  | .bool => 1
  | .unit => 1
  | .fn A B => A.size + B.size + 1
  | .all A => A.size + 2
  | .exist A => A.size + 2
  | .prod A B => A.size + B.size + 1
  | .sum A B => A.size + B.size + 1
  | .mu A => A.size + 2

/-! ### Termination helpers: the lexicographic triple `(k, A.size, case_bit)` -/

private theorem lex_decr {k₁ k₂ s₁ s₂ c₁ c₂ : Nat} (hk : k₁ ≤ k₂) (hs : s₁ < s₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s₁, c₁) (k₂, s₂, c₂) := by
  obtain hlt | heq := Nat.lt_or_eq_of_le hk
  · exact Prod.Lex.left _ _ hlt
  · subst heq
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hs)

private theorem lex_decr_case {k₁ k₂ s : Nat} (hk : k₁ ≤ k₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s, 0) (k₂, s, 1) := by
  obtain hlt | heq := Nat.lt_or_eq_of_le hk
  · exact Prod.Lex.left _ _ hlt
  · subst heq
    exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

mutual
  /-- `valRel δ A k v`: the value `v` belongs to `A` for `k` more steps. -/
  def valRel (δ : TyVarInterp) : Ty → Nat → Val → Prop
    | .int, _, v => ∃ z : Int, v = .litV (.litInt z)
    | .bool, _, v => ∃ b : Bool, v = .litV (.litBool b)
    | .unit, _, v => v = .litV .litUnit
    | .tVar α, k, v => (δ α).car k v
    | .prod A B, k, v => ∃ v₁ v₂ : Val, v = .pairV v₁ v₂ ∧ valRel δ A k v₁ ∧ valRel δ B k v₂
    | .sum A B, k, v =>
        (∃ v' : Val, v = .injLV v' ∧ valRel δ A k v') ∨
        (∃ v' : Val, v = .injRV v' ∧ valRel δ B k v')
    | .fn A B, k, v =>
        ∃ (x : Binder) (e : Expr), v = .lamV x e ∧ SystemFMu.closed (x :b: []) e ∧
          ∀ (v' : Val) (k' : Nat), k' ≤ k → valRel δ A k' v' →
            exprRel δ B k' (subst' x v'.toExpr e)
    | .all A, k, v =>
        ∃ e : Expr, v = .tLamV e ∧ SystemFMu.closed [] e ∧
          ∀ τ : SemType, exprRel (τ .: δ) A k e
    | .exist A, k, v => ∃ v' : Val, v = .packV v' ∧ ∃ τ : SemType, valRel (τ .: δ) A k v'
    | .mu A, k, v =>
        ∃ v' : Val, v = .rollV v' ∧ SystemFMu.closed [] v'.toExpr ∧
          ∀ k' : Nat, k' < k → valRel δ (Ty.subst1 A (.mu A)) k' v'
  termination_by A k _ => (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Ty.size]; omega))
      | exact Prod.Lex.left _ _ (by assumption)
      | exact lex_decr (by assumption) (by simp only [Ty.size]; omega)
      | exact lex_decr (Nat.le_refl _) (by simp only [Ty.size]; omega)

  /-- `exprRel δ A k e`: every complete reduction of `e` of fewer than `k` steps ends in a value
  of type `A`, with the remaining budget. -/
  def exprRel (δ : TyVarInterp) (A : Ty) (k : Nat) (e : Expr) : Prop :=
    ∀ (e' : Expr) (n : Nat), n < k → redNsteps n e e' →
      ∃ v : Val, e'.toVal? = some v ∧ valRel δ A (k - n) v
  termination_by (k, A.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

/-! ## Basic properties -/

theorem val_rel_is_closed (v : Val) (δ : TyVarInterp) (k : Nat) (A : Ty)
    (h : valRel δ A k v) : closed [] v.toExpr := by
  induction A generalizing δ k v with
  | tVar α =>
    simp only [valRel] at h
    exact (δ α).closed_val k v h
  | int =>
    simp only [valRel] at h
    obtain ⟨z, rfl⟩ := h
    rfl
  | bool =>
    simp only [valRel] at h
    obtain ⟨b, rfl⟩ := h
    rfl
  | unit =>
    simp only [valRel] at h
    subst h
    rfl
  | fn A B _ _ =>
    simp only [valRel] at h
    obtain ⟨x, e, rfl, hcl, _⟩ := h
    exact hcl
  | all A _ =>
    simp only [valRel] at h
    obtain ⟨e, rfl, hcl, _⟩ := h
    exact hcl
  | exist A ih =>
    simp only [valRel] at h
    obtain ⟨v', rfl, τ, hv'⟩ := h
    exact ih v' _ _ hv'
  | prod A B ihA ihB =>
    simp only [valRel] at h
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ihA v₁ _ _ h₁, ihB v₂ _ _ h₂⟩
  | sum A B ihA ihB =>
    simp only [valRel] at h
    rcases h with ⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩
    · exact ihA v' _ _ h'
    · exact ihB v' _ _ h'
  | mu A _ =>
    simp only [valRel] at h
    obtain ⟨v', rfl, hcl, _⟩ := h
    exact hcl

/-- The value-inclusion lemma. -/
theorem sem_val_expr_rel (A : Ty) (δ : TyVarInterp) (k : Nat) (v : Val)
    (h : valRel δ A k v) : exprRel δ A k v.toExpr := by
  simp only [exprRel]
  intro e' n hn hred
  obtain ⟨rfl, rfl⟩ := nsteps_val_inv hred
  refine ⟨v, toVal?_toExpr v, ?_⟩
  simpa using h

theorem sem_val_expr_rel' (A : Ty) (δ : TyVarInterp) (k : Nat) (v : Val) (e : Expr)
    (he : e.toVal? = some v) (h : valRel δ A k v) : exprRel δ A k e := by
  rw [toVal?_eq he]
  exact sem_val_expr_rel A δ k v h

theorem sem_expr_rel_zero_trivial (A : Ty) (δ : TyVarInterp) (e : Expr) : exprRel δ A 0 e := by
  simp only [exprRel]
  intro e' n hn _
  omega

theorem sem_expr_rel_of_val (A : Ty) (δ : TyVarInterp) (k : Nat) (v : Val) (hk : 0 < k)
    (h : exprRel δ A k v.toExpr) : valRel δ A k v := by
  simp only [exprRel] at h
  obtain ⟨v', hv', hrel⟩ := h v.toExpr 0 hk ⟨.zero, val_irreducible (val_isVal v)⟩
  rw [toVal?_toExpr v] at hv'
  injection hv' with hv'
  subst hv'
  simpa using hrel

/-! ## Downward closure in the step index -/

mutual
  /-- Value half. -/
  theorem valRel_mono_idx (δ : TyVarInterp) (A : Ty) (k k' : Nat) (v : Val) (hle : k' ≤ k)
      (h : valRel δ A k v) : valRel δ A k' v := by
    match A with
    | .int => simpa only [valRel] using h
    | .bool => simpa only [valRel] using h
    | .unit => simpa only [valRel] using h
    | .tVar α =>
      simp only [valRel] at h ⊢
      exact (δ α).mono k k' v h hle
    | .prod A B =>
      simp only [valRel] at h ⊢
      obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
      exact ⟨v₁, v₂, rfl, valRel_mono_idx δ A k k' v₁ hle h₁,
        valRel_mono_idx δ B k k' v₂ hle h₂⟩
    | .sum A B =>
      simp only [valRel] at h ⊢
      rcases h with ⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩
      · exact Or.inl ⟨v', rfl, valRel_mono_idx δ A k k' v' hle h'⟩
      · exact Or.inr ⟨v', rfl, valRel_mono_idx δ B k k' v' hle h'⟩
    | .fn A B =>
      simp only [valRel] at h ⊢
      obtain ⟨x, e, rfl, hcl, hbody⟩ := h
      exact ⟨x, e, rfl, hcl, fun v' k'' hk'' hv' => hbody v' k'' (by omega) hv'⟩
    | .all A =>
      simp only [valRel] at h ⊢
      obtain ⟨e, rfl, hcl, hbody⟩ := h
      exact ⟨e, rfl, hcl, fun τ => exprRel_mono_idx (τ .: δ) A k k' e hle (hbody τ)⟩
    | .exist A =>
      simp only [valRel] at h ⊢
      obtain ⟨v', rfl, τ, hv'⟩ := h
      exact ⟨v', rfl, τ, valRel_mono_idx (τ .: δ) A k k' v' hle hv'⟩
    | .mu A =>
      simp only [valRel] at h ⊢
      obtain ⟨v', rfl, hcl, hbody⟩ := h
      exact ⟨v', rfl, hcl, fun k'' hk'' => hbody k'' (by omega)⟩
  termination_by (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Ty.size]; omega))
      | exact lex_decr (Nat.le_refl _) (by simp only [Ty.size]; omega)

  /-- Expression half. -/
  theorem exprRel_mono_idx (δ : TyVarInterp) (A : Ty) (k k' : Nat) (e : Expr) (hle : k' ≤ k)
      (h : exprRel δ A k e) : exprRel δ A k' e := by
    simp only [exprRel] at h ⊢
    intro e' n hn hred
    obtain ⟨v, hv, hrel⟩ := h e' n (by omega) hred
    exact ⟨v, hv, valRel_mono_idx δ A (k - n) (k' - n) v (by omega) hrel⟩
  termination_by (k, A.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

theorem val_rel_mono (A : Ty) (δ : TyVarInterp) (k k' : Nat) (v : Val) (hle : k' ≤ k)
    (h : valRel δ A k v) : valRel δ A k' v := valRel_mono_idx δ A k k' v hle h

theorem expr_rel_mono (A : Ty) (δ : TyVarInterp) (k k' : Nat) (e : Expr) (hle : k' ≤ k)
    (h : exprRel δ A k e) : exprRel δ A k' e := exprRel_mono_idx δ A k k' e hle h

def interp_type (A : Ty) (δ : TyVarInterp) : SemType where
  car k v := valRel δ A k v
  closed_val k v h := val_rel_is_closed v δ k A h
  mono k k' v h hle := val_rel_mono A δ k k' v hle h

/-! ## The context relation -/

inductive SemCtxRel (δ : TyVarInterp) (k : Nat) : TypingContext → SubstMap → Prop where
  | empty :
      SemCtxRel δ k (PartialMap.empty (M := TyMapStr) (V := Ty))
        (PartialMap.empty (M := MapStr) (V := Expr))
  | insert {Γ : TypingContext} {θ : SubstMap} (v : Val) (x : String) (A : Ty) :
      valRel δ A k v → SemCtxRel δ k Γ θ →
      SemCtxRel δ k (Iris.Std.insert (M := TyMapStr) Γ x A)
        (Iris.Std.insert (M := MapStr) θ x v.toExpr)

private theorem get?_insert_cases {V : Type} {m : MapStr V} {x y : String} {a b : V}
    (h : get? (M := MapStr) (Iris.Std.insert (M := MapStr) m x a) y = some b) :
    (x = y ∧ a = b) ∨ (x ≠ y ∧ get? (M := MapStr) m y = some b) := by
  by_cases hxy : x = y
  · rw [LawfulPartialMap.get?_insert_eq (M := MapStr) hxy] at h
    injection h with h
    exact Or.inl ⟨hxy, h⟩
  · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at h
    exact Or.inr ⟨hxy, h⟩

private theorem get?_insert_cases_ty {m : TyMapStr Ty} {x y : String} {a b : Ty}
    (h : get? (M := TyMapStr) (Iris.Std.insert (M := TyMapStr) m x a) y = some b) :
    (x = y ∧ a = b) ∨ (x ≠ y ∧ get? (M := TyMapStr) m y = some b) := by
  by_cases hxy : x = y
  · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy] at h
    injection h with h
    exact Or.inl ⟨hxy, h⟩
  · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at h
    exact Or.inr ⟨hxy, h⟩

theorem sem_context_rel_vals {δ : TyVarInterp} {k : Nat} {Γ : TypingContext} {θ : SubstMap}
    {x : String} {A : Ty} (h : SemCtxRel δ k Γ θ) (hx : get? (M := TyMapStr) Γ x = some A) :
    ∃ (e : Expr) (v : Val), get? (M := MapStr) θ x = some e ∧ e.toVal? = some v ∧
      valRel δ A k v := by
  induction h with
  | empty =>
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
      LawfulPartialMap.get?_empty (M := TyMapStr) x] at hx
    exact absurd hx (by simp)
  | insert v y B hv _ ih =>
    rcases get?_insert_cases_ty hx with ⟨rfl, rfl⟩ | ⟨hne, hx'⟩
    · exact ⟨v.toExpr, v, LawfulPartialMap.get?_insert_eq (M := MapStr) rfl,
        toVal?_toExpr v, hv⟩
    · obtain ⟨e, w, hlook, hw, hrel⟩ := ih hx'
      exact ⟨e, w, by rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hne]; exact hlook,
        hw, hrel⟩

/-- The context relation binds exactly the variables the typing context does. -/
theorem sem_context_rel_dom {δ : TyVarInterp} {k : Nat} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ k Γ θ) (x : String) :
    get? (M := TyMapStr) Γ x ≠ none ↔ get? (M := MapStr) θ x ≠ none := by
  induction h with
  | empty =>
    rw [show get? (M := TyMapStr) (PartialMap.empty (M := TyMapStr) (V := Ty)) x = none from
        LawfulPartialMap.get?_empty (M := TyMapStr) x,
      show get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) x = none from
        LawfulPartialMap.get?_empty (M := MapStr) x]
    simp
  | insert v y B hv _ ih =>
    by_cases hxy : y = x
    · rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy,
        LawfulPartialMap.get?_insert_eq (M := MapStr) hxy]
      simp
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy,
        LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]
      exact ih

theorem sem_context_rel_closed {δ : TyVarInterp} {k : Nat} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ k Γ θ) : substIsClosed [] θ := by
  induction h with
  | empty =>
    intro y e hy
    rw [show get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) y = none from
      LawfulPartialMap.get?_empty (M := MapStr) y] at hy
    exact absurd hy (by simp)
  | insert v x A hv _ ih =>
    intro y e hy
    rcases get?_insert_cases hy with ⟨_, rfl⟩ | ⟨_, hy'⟩
    · exact val_rel_is_closed v _ _ A hv
    · exact ih y e hy'

theorem sem_context_rel_mono {Γ : TypingContext} {δ : TyVarInterp} {k k' : Nat} {θ : SubstMap}
    (hle : k' ≤ k) (h : SemCtxRel δ k Γ θ) : SemCtxRel δ k' Γ θ := by
  induction h with
  | empty => exact .empty
  | insert v x A hv _ ih => exact .insert v x A (val_rel_mono A δ k k' v hle hv) ih

/-- The names a typing context binds. -/
def TypingContext.domList (Γ : TypingContext) : List String :=
  (FiniteMap.toList (M := TyMapStr) Γ).map Prod.fst

theorem mem_ctx_domList {Γ : TypingContext} {x : String} :
    x ∈ Γ.domList ↔ ∃ A, get? (M := TyMapStr) Γ x = some A := by
  simp only [TypingContext.domList, List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, hmem, rfl⟩
    exact ⟨v, (LawfulFiniteMap.toList_get (M := TyMapStr) (K := String)).mp hmem⟩
  · rintro ⟨A, hA⟩
    exact ⟨(x, A), (LawfulFiniteMap.toList_get (M := TyMapStr) (K := String)).mpr hA, rfl⟩

theorem mem_ctx_domList_insert {Γ : TypingContext} {x y : String} {A : Ty} :
    y ∈ TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A) ↔
      y = x ∨ y ∈ Γ.domList := by
  rw [mem_ctx_domList]
  constructor
  · rintro ⟨B, hB⟩
    by_cases hxy : x = y
    · exact Or.inl hxy.symm
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hB
      exact Or.inr (mem_ctx_domList.mpr ⟨B, hB⟩)
  · rintro (rfl | h)
    · exact ⟨A, LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl⟩
    · obtain ⟨B, hB⟩ := mem_ctx_domList.mp h
      by_cases hxy : x = y
      · exact ⟨A, LawfulPartialMap.get?_insert_eq (M := TyMapStr) hxy⟩
      · exact ⟨B, by rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy]; exact hB⟩

theorem mem_shiftCtx_domList {Γ : TypingContext} {x : String} :
    x ∈ TypingContext.domList (shiftCtx Γ) ↔ x ∈ Γ.domList := by
  rw [mem_ctx_domList, mem_ctx_domList, shiftCtx_get?]
  cases get? (M := TyMapStr) Γ x <;> simp

theorem sem_context_rel_domList {δ : TyVarInterp} {k : Nat} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ k Γ θ) (x : String) : x ∈ Γ.domList ↔ x ∈ θ.domList := by
  have hd := sem_context_rel_dom h x
  rw [mem_ctx_domList, mem_domList_iff_lookup]
  constructor
  · rintro ⟨A, hA⟩
    cases hget : get? (M := MapStr) θ x with
    | none => exact absurd hget (hd.mp (by rw [hA]; simp))
    | some e => exact ⟨e, rfl⟩
  · rintro ⟨e, he⟩
    cases hget : get? (M := TyMapStr) Γ x with
    | none => exact absurd hget (hd.mpr (by rw [he]; simp))
    | some A => exact ⟨A, rfl⟩

def semTyped (Γ : TypingContext) (e : Expr) (A : Ty) : Prop :=
  closed Γ.domList e ∧ ∀ (θ : SubstMap) (δ : TyVarInterp) (k : Nat), SemCtxRel δ k Γ θ →
    exprRel δ A k (substMap θ e)

/-! ## Moving the interpretation around

Each statement is proved for the value and the expression relation simultaneously, by the same
well-founded recursion the definition uses. -/

/-- Extending two pointwise-equal interpretations keeps them pointwise equal. -/
private theorem cons_iff {δ δ' : TyVarInterp} (τ : SemType)
    (hiff : ∀ n k w, (δ n).car k w ↔ (δ' n).car k w) :
    ∀ n k w, ((τ .: δ) n).car k w ↔ ((τ .: δ') n).car k w := by
  intro n k w
  cases n with
  | zero => exact Iff.rfl
  | succ m => exact hiff m k w

mutual
  /-- Value half. -/
  theorem valRel_ext (δ δ' : TyVarInterp) (B : Ty) (k : Nat) (v : Val)
      (hiff : ∀ n k w, (δ n).car k w ↔ (δ' n).car k w) : valRel δ B k v ↔ valRel δ' B k v := by
    match B with
    | .int => simp only [valRel]
    | .bool => simp only [valRel]
    | .unit => simp only [valRel]
    | .tVar α => simp only [valRel]; exact hiff α k v
    | .prod A B =>
      simp only [valRel]
      constructor
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_ext δ δ' A k v₁ hiff).mp h₁,
          (valRel_ext δ δ' B k v₂ hiff).mp h₂⟩
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_ext δ δ' A k v₁ hiff).mpr h₁,
          (valRel_ext δ δ' B k v₂ hiff).mpr h₂⟩
    | .sum A B =>
      simp only [valRel]
      constructor
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_ext δ δ' A k v' hiff).mp h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_ext δ δ' B k v' hiff).mp h'⟩
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_ext δ δ' A k v' hiff).mpr h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_ext δ δ' B k v' hiff).mpr h'⟩
    | .fn A B =>
      simp only [valRel]
      constructor
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_ext δ δ' B k' _ hiff).mp
          (hbody v' k' hk' ((valRel_ext δ δ' A k' v' hiff).mpr hv'))
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_ext δ δ' B k' _ hiff).mpr
          (hbody v' k' hk' ((valRel_ext δ δ' A k' v' hiff).mp hv'))
    | .all A =>
      simp only [valRel]
      constructor
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ =>
          (exprRel_ext (τ .: δ) (τ .: δ') A k e (cons_iff τ hiff)).mp (hbody τ)⟩
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ =>
          (exprRel_ext (τ .: δ) (τ .: δ') A k e (cons_iff τ hiff)).mpr (hbody τ)⟩
    | .exist A =>
      simp only [valRel]
      constructor
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (valRel_ext (τ .: δ) (τ .: δ') A k v' (cons_iff τ hiff)).mp hv'⟩
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (valRel_ext (τ .: δ) (τ .: δ') A k v' (cons_iff τ hiff)).mpr hv'⟩
    | .mu A =>
      simp only [valRel]
      constructor
      · rintro ⟨v', rfl, hcl, hbody⟩
        exact ⟨v', rfl, hcl, fun k' hk' =>
          (valRel_ext δ δ' _ k' v' hiff).mp (hbody k' hk')⟩
      · rintro ⟨v', rfl, hcl, hbody⟩
        exact ⟨v', rfl, hcl, fun k' hk' =>
          (valRel_ext δ δ' _ k' v' hiff).mpr (hbody k' hk')⟩
  termination_by (k, B.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.left _ _ (by assumption)
      | exact lex_decr (by assumption) (by simp only [Ty.size]; omega)
      | exact lex_decr (Nat.le_refl _) (by simp only [Ty.size]; omega)

  /-- Expression half. -/
  theorem exprRel_ext (δ δ' : TyVarInterp) (B : Ty) (k : Nat) (e : Expr)
      (hiff : ∀ n k w, (δ n).car k w ↔ (δ' n).car k w) : exprRel δ B k e ↔ exprRel δ' B k e := by
    simp only [exprRel]
    constructor
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_ext δ δ' B (k - n) v hiff).mp hrel⟩
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_ext δ δ' B (k - n) v hiff).mpr hrel⟩
  termination_by (k, B.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

mutual
  /-- Value half. -/
  theorem valRel_move_ren (δ : TyVarInterp) (σ : Nat → Nat) (B : Ty) (k : Nat) (v : Val) :
      valRel (fun n => δ (σ n)) B k v ↔ valRel δ (B.rename σ) k v := by
    match B with
    | .int => simp only [Ty.rename, valRel]
    | .bool => simp only [Ty.rename, valRel]
    | .unit => simp only [Ty.rename, valRel]
    | .tVar α => simp only [Ty.rename, valRel]
    | .prod A B =>
      simp only [Ty.rename, valRel]
      constructor
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_move_ren δ σ A k v₁).mp h₁,
          (valRel_move_ren δ σ B k v₂).mp h₂⟩
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_move_ren δ σ A k v₁).mpr h₁,
          (valRel_move_ren δ σ B k v₂).mpr h₂⟩
    | .sum A B =>
      simp only [Ty.rename, valRel]
      constructor
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_move_ren δ σ A k v').mp h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_move_ren δ σ B k v').mp h'⟩
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_move_ren δ σ A k v').mpr h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_move_ren δ σ B k v').mpr h'⟩
    | .fn A B =>
      simp only [Ty.rename, valRel]
      constructor
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_move_ren δ σ B k' _).mp
          (hbody v' k' hk' ((valRel_move_ren δ σ A k' v').mpr hv'))
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_move_ren δ σ B k' _).mpr
          (hbody v' k' hk' ((valRel_move_ren δ σ A k' v').mp hv'))
    | .all A =>
      simp only [Ty.rename, valRel]
      have hcons : ∀ (τ : SemType) (e : Expr),
          exprRel (τ .: fun n => δ (σ n)) A k e ↔
            exprRel (τ .: δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) k e := by
        intro τ e
        refine Iff.trans ?_ (exprRel_move_ren (τ .: δ) _ A k e)
        refine exprRel_ext _ _ A k e fun n j u => ?_
        cases n <;> exact Iff.rfl
      constructor
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ => (hcons τ e).mp (hbody τ)⟩
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ => (hcons τ e).mpr (hbody τ)⟩
    | .exist A =>
      simp only [Ty.rename, valRel]
      have hcons : ∀ (τ : SemType) (w : Val),
          valRel (τ .: fun n => δ (σ n)) A k w ↔
            valRel (τ .: δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) k w := by
        intro τ w
        refine Iff.trans ?_ (valRel_move_ren (τ .: δ) _ A k w)
        refine valRel_ext _ _ A k w fun n j u => ?_
        cases n <;> exact Iff.rfl
      constructor
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (hcons τ v').mp hv'⟩
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (hcons τ v').mpr hv'⟩
    | .mu A =>
      simp only [Ty.rename, valRel]
      constructor
      · rintro ⟨v', rfl, hcl, hbody⟩
        refine ⟨v', rfl, hcl, fun k' hk' => ?_⟩
        rw [Ty.subst1_mu_rename_comm A σ]
        exact (valRel_move_ren δ σ _ k' v').mp (hbody k' hk')
      · rintro ⟨v', rfl, hcl, hbody⟩
        refine ⟨v', rfl, hcl, fun k' hk' => ?_⟩
        have := hbody k' hk'
        rw [Ty.subst1_mu_rename_comm A σ] at this
        exact (valRel_move_ren δ σ _ k' v').mpr this
  termination_by (k, B.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.left _ _ (by assumption)
      | exact lex_decr (by assumption) (by simp only [Ty.size]; omega)
      | exact lex_decr (Nat.le_refl _) (by simp only [Ty.size]; omega)

  /-- Expression half. -/
  theorem exprRel_move_ren (δ : TyVarInterp) (σ : Nat → Nat) (B : Ty) (k : Nat) (e : Expr) :
      exprRel (fun n => δ (σ n)) B k e ↔ exprRel δ (B.rename σ) k e := by
    simp only [exprRel]
    constructor
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_move_ren δ σ B (k - n) v).mp hrel⟩
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_move_ren δ σ B (k - n) v).mpr hrel⟩
  termination_by (k, B.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

mutual
  /-- Value half. -/
  theorem valRel_move_subst (δ : TyVarInterp) (σ : Nat → Ty) (B : Ty) (k : Nat) (v : Val) :
      valRel (fun n => interp_type (σ n) δ) B k v ↔ valRel δ (B.substTy σ) k v := by
    match B with
    | .int => simp only [Ty.substTy, valRel]
    | .bool => simp only [Ty.substTy, valRel]
    | .unit => simp only [Ty.substTy, valRel]
    | .tVar α => simp only [Ty.substTy, valRel, interp_type]
    | .prod A B =>
      simp only [Ty.substTy, valRel]
      constructor
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_move_subst δ σ A k v₁).mp h₁,
          (valRel_move_subst δ σ B k v₂).mp h₂⟩
      · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
        exact ⟨v₁, v₂, rfl, (valRel_move_subst δ σ A k v₁).mpr h₁,
          (valRel_move_subst δ σ B k v₂).mpr h₂⟩
    | .sum A B =>
      simp only [Ty.substTy, valRel]
      constructor
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_move_subst δ σ A k v').mp h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_move_subst δ σ B k v').mp h'⟩
      · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
        · exact Or.inl ⟨v', rfl, (valRel_move_subst δ σ A k v').mpr h'⟩
        · exact Or.inr ⟨v', rfl, (valRel_move_subst δ σ B k v').mpr h'⟩
    | .fn A B =>
      simp only [Ty.substTy, valRel]
      constructor
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_move_subst δ σ B k' _).mp
          (hbody v' k' hk' ((valRel_move_subst δ σ A k' v').mpr hv'))
      · rintro ⟨x, e, rfl, hcl, hbody⟩
        refine ⟨x, e, rfl, hcl, fun v' k' hk' hv' => ?_⟩
        exact (exprRel_move_subst δ σ B k' _).mpr
          (hbody v' k' hk' ((valRel_move_subst δ σ A k' v').mp hv'))
    | .all A =>
      simp only [Ty.substTy, valRel]
      have hcons : ∀ (τ : SemType) (e : Expr),
          exprRel (τ .: fun n => interp_type (σ n) δ) A k e ↔
            exprRel (τ .: δ) (A.substTy
              (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) k e := by
        intro τ e
        refine Iff.trans ?_ (exprRel_move_subst (τ .: δ) _ A k e)
        refine exprRel_ext _ _ A k e fun n j u => ?_
        cases n with
        | zero =>
          show τ.car j u ↔ (interp_type (Ty.tVar 0) (τ .: δ)).car j u
          simp only [interp_type, valRel, cons_zero]
        | succ m =>
          show (interp_type (σ m) δ).car j u ↔
            (interp_type ((σ m).rename (· + 1)) (τ .: δ)).car j u
          exact valRel_move_ren (τ .: δ) (· + 1) (σ m) j u
      constructor
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ => (hcons τ e).mp (hbody τ)⟩
      · rintro ⟨e, rfl, hcl, hbody⟩
        exact ⟨e, rfl, hcl, fun τ => (hcons τ e).mpr (hbody τ)⟩
    | .exist A =>
      simp only [Ty.substTy, valRel]
      have hcons : ∀ (τ : SemType) (w : Val),
          valRel (τ .: fun n => interp_type (σ n) δ) A k w ↔
            valRel (τ .: δ) (A.substTy
              (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) k w := by
        intro τ w
        refine Iff.trans ?_ (valRel_move_subst (τ .: δ) _ A k w)
        refine valRel_ext _ _ A k w fun n j u => ?_
        cases n with
        | zero =>
          show τ.car j u ↔ (interp_type (Ty.tVar 0) (τ .: δ)).car j u
          simp only [interp_type, valRel, cons_zero]
        | succ m =>
          show (interp_type (σ m) δ).car j u ↔
            (interp_type ((σ m).rename (· + 1)) (τ .: δ)).car j u
          exact valRel_move_ren (τ .: δ) (· + 1) (σ m) j u
      constructor
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (hcons τ v').mp hv'⟩
      · rintro ⟨v', rfl, τ, hv'⟩
        exact ⟨v', rfl, τ, (hcons τ v').mpr hv'⟩
    | .mu A =>
      simp only [Ty.substTy, valRel]
      constructor
      · rintro ⟨v', rfl, hcl, hbody⟩
        refine ⟨v', rfl, hcl, fun k' hk' => ?_⟩
        rw [Ty.subst1_mu_substTy_comm A σ]
        exact (valRel_move_subst δ σ _ k' v').mp (hbody k' hk')
      · rintro ⟨v', rfl, hcl, hbody⟩
        refine ⟨v', rfl, hcl, fun k' hk' => ?_⟩
        have := hbody k' hk'
        rw [Ty.subst1_mu_substTy_comm A σ] at this
        exact (valRel_move_subst δ σ _ k' v').mpr this
  termination_by (k, B.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.left _ _ (by assumption)
      | exact lex_decr (by assumption) (by simp only [Ty.size]; omega)
      | exact lex_decr (Nat.le_refl _) (by simp only [Ty.size]; omega)

  /-- Expression half. -/
  theorem exprRel_move_subst (δ : TyVarInterp) (σ : Nat → Ty) (B : Ty) (k : Nat) (e : Expr) :
      exprRel (fun n => interp_type (σ n) δ) B k e ↔ exprRel δ (B.substTy σ) k e := by
    simp only [exprRel]
    constructor
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_move_subst δ σ B (k - n) v).mp hrel⟩
    · intro h e' n hn hred
      obtain ⟨v, hv, hrel⟩ := h e' n hn hred
      exact ⟨v, hv, (valRel_move_subst δ σ B (k - n) v).mpr hrel⟩
  termination_by (k, B.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

theorem sem_val_rel_move_single_subst (A B : Ty) (δ : TyVarInterp) (k : Nat) (v : Val) :
    valRel ((interp_type A δ) .: δ) B k v ↔ valRel δ (B.subst1 A) k v := by
  refine Iff.trans ?_ (valRel_move_subst δ _ B k v)
  refine valRel_ext _ _ B k v fun n j u => ?_
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    show (δ m).car j u ↔ (interp_type (Ty.tVar m) δ).car j u
    simp only [interp_type, valRel]

theorem sem_expr_rel_move_single_subst (A B : Ty) (δ : TyVarInterp) (k : Nat) (e : Expr) :
    exprRel ((interp_type A δ) .: δ) B k e ↔ exprRel δ (B.subst1 A) k e := by
  refine Iff.trans ?_ (exprRel_move_subst δ _ B k e)
  refine exprRel_ext _ _ B k e fun n j u => ?_
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    show (δ m).car j u ↔ (interp_type (Ty.tVar m) δ).car j u
    simp only [interp_type, valRel]

theorem sem_val_rel_cons (A : Ty) (δ : TyVarInterp) (k : Nat) (v : Val) (τ : SemType) :
    valRel δ A k v ↔ valRel (τ .: δ) (A.rename (· + 1)) k v :=
  valRel_move_ren (τ .: δ) (· + 1) A k v

theorem sem_expr_rel_cons (A : Ty) (δ : TyVarInterp) (k : Nat) (e : Expr) (τ : SemType) :
    exprRel δ A k e ↔ exprRel (τ .: δ) (A.rename (· + 1)) k e :=
  exprRel_move_ren (τ .: δ) (· + 1) A k e

theorem sem_context_rel_cons {Γ : TypingContext} {k : Nat} {δ : TyVarInterp} {θ : SubstMap}
    (τ : SemType) (h : SemCtxRel δ k Γ θ) : SemCtxRel (τ .: δ) k (shiftCtx Γ) θ := by
  induction h with
  | empty =>
    rw [shiftCtx_empty]
    exact .empty
  | insert v x A hv _ ih =>
    rw [shiftCtx_insert]
    exact .insert v x _ ((sem_val_rel_cons A _ k v τ).mp hv) ih

/-! ## The bind lemma and closure under deterministic reduction -/

theorem bind (K : Ectx) (e : Expr) (k : Nat) (δ : TyVarInterp) (A B : Ty)
    (h₁ : exprRel δ A k e)
    (h₂ : ∀ (j : Nat) (v : Val), j ≤ k → valRel δ A j v → exprRel δ B j (fill K v.toExpr)) :
    exprRel δ B k (fill K e) := by
  simp only [exprRel] at h₁ ⊢
  intro e' n hn hred
  obtain ⟨j, e'', hj, hred₁, hred₂⟩ := red_nsteps_fill hred
  obtain ⟨v, hv, hvrel⟩ := h₁ e'' j (by omega) hred₁
  have h₂' := h₂ (k - j) v (by omega) hvrel
  simp only [exprRel] at h₂'
  rw [toVal?_eq hv] at hred₂
  obtain ⟨w, hw, hwrel⟩ := h₂' e' (n - j) (by omega) hred₂
  refine ⟨w, hw, ?_⟩
  have hidx : k - n = k - j - (n - j) := by omega
  rw [hidx]
  exact hwrel

theorem expr_det_step_closure {e e' : Expr} {A : Ty} {δ : TyVarInterp} {k : Nat}
    (hdet : DetStep e e') (h : exprRel δ A (k - 1) e') : exprRel δ A k e := by
  simp only [exprRel] at h ⊢
  intro e'' n hn hred
  obtain ⟨hle, hred'⟩ := det_step_red hdet hred
  obtain ⟨v, hv, hrel⟩ := h e'' (n - 1) (by omega) hred'
  refine ⟨v, hv, ?_⟩
  have hidx : k - n = k - 1 - (n - 1) := by omega
  rw [hidx]
  exact hrel

theorem expr_det_steps_closure {e e' : Expr} {A : Ty} {δ : TyVarInterp} {n : Nat}
    (hsteps : DetSteps n e e') : ∀ k : Nat, exprRel δ A (k - n) e' → exprRel δ A k e := by
  induction hsteps with
  | zero => intro k h; simpa using h
  | @step e₁ e₂ m e₃ hstep hrest ih =>
    intro k h
    refine expr_det_step_closure hstep (ih (k - 1) ?_)
    have hidx : k - 1 - m = k - (m + 1) := by omega
    rwa [hidx]

/-! ## Closedness helpers -/

theorem is_closed_substMap_delete {X : List String} {Γ : TypingContext} (x : String)
    {θ : SubstMap} {A : Ty} {e : Expr} (he : closed X e) (hθ : substIsClosed [] θ)
    (hdom : ∀ y, get? (M := TyMapStr) Γ y ≠ none ↔ get? (M := MapStr) θ y ≠ none)
    (hX : ∀ y, y ∈ X → y ∈ TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A)) :
    closed (Binder.bNamed x :b: []) (substMap (delete (M := MapStr) θ x) e) := by
  refine closed_subst_weaken (X := X) ?_ (fun y hy hget => ?_) he
  · intro z ez hz
    refine hθ z ez ?_
    by_cases hxz : x = z
    · subst hxz
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hz
      exact absurd hz (by simp)
    · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hxz] at hz
  · rcases mem_ctx_domList_insert.mp (hX y hy) with rfl | hy'
    · exact List.Mem.head _
    · by_cases hxy : x = y
      · exact hxy ▸ List.Mem.head _
      · exfalso
        rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at hget
        obtain ⟨B, hB⟩ := mem_ctx_domList.mp hy'
        exact ((hdom y).mp (by rw [hB]; simp)) hget

theorem is_closed_substMap_anon {X : List String} {Γ : TypingContext} {θ : SubstMap} {e : Expr}
    (he : closed X e) (hθ : substIsClosed [] θ)
    (hdom : ∀ y, get? (M := TyMapStr) Γ y ≠ none ↔ get? (M := MapStr) θ y ≠ none)
    (hX : ∀ y, y ∈ X → y ∈ Γ.domList) : closed [] (substMap θ e) := by
  refine closed_subst_weaken (X := X) hθ (fun y hy hget => ?_) he
  exfalso
  obtain ⟨B, hB⟩ := mem_ctx_domList.mp (hX y hy)
  exact ((hdom y).mp (by rw [hB]; simp)) hget

/-! ## Compatibility lemmas -/

/-- `bind` for a single evaluation-context frame, the form every compatibility lemma uses. -/
theorem bind_item (Ki : EctxItem) (e : Expr) (k : Nat) (δ : TyVarInterp) (A B : Ty)
    (h₁ : exprRel δ A k e)
    (h₂ : ∀ (j : Nat) (v : Val), j ≤ k → valRel δ A j v →
      exprRel δ B j (fillItem Ki v.toExpr)) :
    exprRel δ B k (fillItem Ki e) :=
  bind [Ki] e k δ A B h₁ h₂

/-- Stated early because `compat_app` and `compat_case` both use it. -/
theorem semantic_app (A B : Ty) (δ : TyVarInterp) (k : Nat) (e₁ e₂ : Expr)
    (h₁ : exprRel δ (.fn A B) k e₁) (h₂ : exprRel δ A k e₂) : exprRel δ B k (.app e₁ e₂) := by
  refine bind_item (.appRCtx e₁) e₂ k δ A B h₂ (fun j v hj hv => ?_)
  show exprRel δ B j (.app e₁ v.toExpr)
  refine bind_item (.appLCtx v) e₁ j δ (.fn A B) B
    (expr_rel_mono _ δ k j e₁ hj h₁) (fun j' f hj' hf => ?_)
  simp only [valRel] at hf
  obtain ⟨x, e, rfl, _, hbody⟩ := hf
  show exprRel δ B j' (.app (.lam x e) v.toExpr)
  refine expr_det_step_closure (det_step_beta x e v.toExpr (val_isVal v)) ?_
  exact expr_rel_mono _ δ j' (j' - 1) _ (Nat.sub_le _ _)
    (hbody v j' (Nat.le_refl _) (val_rel_mono A δ j j' v hj' hv))

/-- A binary operator applied to two literals steps to its value. -/
private theorem binop_lit_step {δ : TyVarInterp} {k : Nat} {A : Ty} (op : BinOp) (v₁ v₂ v' : Val)
    (hev : binOpEval op v₁ v₂ = some v') (hv : valRel δ A (k - 1) v') :
    exprRel δ A k (.binOp op v₁.toExpr v₂.toExpr) :=
  expr_det_step_closure
    (det_step_binOp op _ _ v₁ v₂ v' (toVal?_toExpr v₁) (toVal?_toExpr v₂) hev)
    (sem_val_expr_rel A δ (k - 1) v' hv)

/-- A unary operator applied to a literal steps to its value. -/
private theorem unop_lit_step {δ : TyVarInterp} {k : Nat} {A : Ty} (op : UnOp) (v v' : Val)
    (hev : unOpEval op v = some v') (hvr : valRel δ A (k - 1) v') :
    exprRel δ A k (.unOp op v.toExpr) :=
  expr_det_step_closure (det_step_unOp op _ v v' (toVal?_toExpr v) hev)
    (sem_val_expr_rel A δ (k - 1) v' hvr)

theorem compat_int (Γ : TypingContext) (z : Int) : semTyped Γ (.lit (.litInt z)) .int := by
  refine ⟨rfl, fun θ δ k _ => ?_⟩
  simp only [substMap]
  refine sem_val_expr_rel .int δ k (.litV (.litInt z)) ?_
  simp only [valRel]
  exact ⟨z, rfl⟩

theorem compat_bool (Γ : TypingContext) (b : Bool) : semTyped Γ (.lit (.litBool b)) .bool := by
  refine ⟨rfl, fun θ δ k _ => ?_⟩
  simp only [substMap]
  refine sem_val_expr_rel .bool δ k (.litV (.litBool b)) ?_
  simp only [valRel]
  exact ⟨b, rfl⟩

theorem compat_unit (Γ : TypingContext) : semTyped Γ (.lit .litUnit) .unit := by
  refine ⟨rfl, fun θ δ k _ => ?_⟩
  simp only [substMap]
  refine sem_val_expr_rel .unit δ k (.litV .litUnit) ?_
  simp only [valRel]

theorem compat_var (Γ : TypingContext) (x : String) (A : Ty)
    (hx : get? (M := TyMapStr) Γ x = some A) : semTyped Γ (.var x) A := by
  refine ⟨?_, fun θ δ k hctx => ?_⟩
  · simpa [closed, Expr.isClosed] using mem_ctx_domList.mpr ⟨A, hx⟩
  · obtain ⟨e, v, he, hv, hrel⟩ := sem_context_rel_vals hctx hx
    simp only [substMap, he]
    exact sem_val_expr_rel' A δ k v e hv hrel

theorem compat_app (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ (.fn A B)) (h₂ : semTyped Γ e₂ A) : semTyped Γ (.app e₁ e₂) B := by
  obtain ⟨hcl₁, hfun⟩ := h₁
  obtain ⟨hcl₂, harg⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  exact semantic_app A B δ k _ _ (hfun θ δ k hctx) (harg θ δ k hctx)

theorem compat_lam_named (Γ : TypingContext) (x : String) (e : Expr) (A B : Ty)
    (h : semTyped (Iris.Std.insert (M := TyMapStr) Γ x A) e B) :
    semTyped Γ (.lam (.bNamed x) e) (.fn A B) := by
  obtain ⟨hcl, hbody⟩ := h
  refine ⟨?_, fun θ δ k hctx => ?_⟩
  · show closed (x :: TypingContext.domList Γ) e
    refine closed_weaken hcl fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ hy'
  · simp only [substMap, binderDelete]
    refine sem_val_expr_rel (.fn A B) δ k
      (.lamV (.bNamed x) (substMap (delete (M := MapStr) θ x) e)) ?_
    simp only [valRel]
    refine ⟨.bNamed x, _, rfl, ?_, fun v' k' hk' hv' => ?_⟩
    · exact is_closed_substMap_delete x hcl (sem_context_rel_closed hctx)
        (sem_context_rel_dom hctx) (fun y hy => hy)
    · have hb := hbody (Iris.Std.insert (M := MapStr) θ x v'.toExpr) δ k'
        (.insert v' x A hv' (sem_context_rel_mono hk' hctx))
      rwa [← subst_substMap x v'.toExpr θ e (sem_context_rel_closed hctx)] at hb

theorem compat_lam_anon (Γ : TypingContext) (e : Expr) (A B : Ty) (h : semTyped Γ e B) :
    semTyped Γ (.lam .bAnon e) (.fn A B) := by
  obtain ⟨hcl, hbody⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap, binderDelete]
  refine sem_val_expr_rel (.fn A B) δ k (.lamV .bAnon (substMap θ e)) ?_
  simp only [valRel]
  refine ⟨.bAnon, _, rfl, ?_, fun v' k' hk' _ => ?_⟩
  · exact is_closed_substMap_anon hcl (sem_context_rel_closed hctx)
      (sem_context_rel_dom hctx) (fun y hy => hy)
  · exact hbody θ δ k' (sem_context_rel_mono hk' hctx)

theorem compat_int_binop (Γ : TypingContext) (op : BinOp) (e₁ e₂ : Expr)
    (hop : BinOpTyped op .int .int .int) (h₁ : semTyped Γ e₁ .int) (h₂ : semTyped Γ e₂ .int) :
    semTyped Γ (.binOp op e₁ e₂) .int := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.binOpRCtx op (substMap θ e₁)) _ k δ .int .int (he₂ θ δ k hctx)
    (fun j v₂ hj hv₂ => ?_)
  show exprRel δ .int j (.binOp op (substMap θ e₁) v₂.toExpr)
  refine bind_item (.binOpLCtx op v₂) _ j δ .int .int
    (expr_rel_mono _ δ k j _ hj (he₁ θ δ k hctx)) (fun j' v₁ hj' hv₁ => ?_)
  show exprRel δ .int j' (.binOp op v₁.toExpr v₂.toExpr)
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl⟩ := hv₁
  obtain ⟨z₂, rfl⟩ := hv₂
  cases hop <;>
    exact binop_lit_step _ _ _ _ rfl (by simp only [valRel]; exact ⟨_, rfl⟩)

theorem compat_int_bool_binop (Γ : TypingContext) (op : BinOp) (e₁ e₂ : Expr)
    (hop : BinOpTyped op .int .int .bool) (h₁ : semTyped Γ e₁ .int) (h₂ : semTyped Γ e₂ .int) :
    semTyped Γ (.binOp op e₁ e₂) .bool := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.binOpRCtx op (substMap θ e₁)) _ k δ .int .bool (he₂ θ δ k hctx)
    (fun j v₂ hj hv₂ => ?_)
  show exprRel δ .bool j (.binOp op (substMap θ e₁) v₂.toExpr)
  refine bind_item (.binOpLCtx op v₂) _ j δ .int .bool
    (expr_rel_mono _ δ k j _ hj (he₁ θ δ k hctx)) (fun j' v₁ hj' hv₁ => ?_)
  show exprRel δ .bool j' (.binOp op v₁.toExpr v₂.toExpr)
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl⟩ := hv₁
  obtain ⟨z₂, rfl⟩ := hv₂
  cases hop <;>
    exact binop_lit_step _ _ _ _ rfl (by simp only [valRel]; exact ⟨_, rfl⟩)

theorem compat_unop (Γ : TypingContext) (op : UnOp) (A B : Ty) (e : Expr)
    (hop : UnOpTyped op A B) (h : semTyped Γ e A) : semTyped Γ (.unOp op e) B := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.unOpCtx op) _ k δ A B (he θ δ k hctx) (fun j v hj hv => ?_)
  show exprRel δ B j (.unOp op v.toExpr)
  cases hop
  · simp only [valRel] at hv
    obtain ⟨b, rfl⟩ := hv
    exact unop_lit_step _ _ (.litV (.litBool (!b))) rfl
      (by simp only [valRel]; exact ⟨_, rfl⟩)
  · simp only [valRel] at hv
    obtain ⟨z, rfl⟩ := hv
    exact unop_lit_step _ _ (.litV (.litInt (-z))) rfl
      (by simp only [valRel]; exact ⟨_, rfl⟩)

theorem compat_tlam (Γ : TypingContext) (e : Expr) (A : Ty)
    (h : semTyped (shiftCtx Γ) e A) : semTyped Γ (.tLam e) (.all A) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨closed_weaken hcl fun y hy => mem_shiftCtx_domList.mp hy, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine sem_val_expr_rel (.all A) δ k (.tLamV (substMap θ e)) ?_
  simp only [valRel]
  refine ⟨_, rfl, ?_, fun τ => he θ (τ .: δ) k (sem_context_rel_cons τ hctx)⟩
  exact is_closed_substMap_anon hcl (sem_context_rel_closed hctx) (sem_context_rel_dom hctx)
    (fun y hy => mem_shiftCtx_domList.mp hy)

theorem compat_tapp (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.all A)) : semTyped Γ (.tApp e) (A.subst1 B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .tAppCtx _ k δ (.all A) (A.subst1 B) (he θ δ k hctx) (fun j v hj hv => ?_)
  simp only [valRel] at hv
  obtain ⟨e', rfl, _, hbody⟩ := hv
  show exprRel δ (A.subst1 B) j (.tApp (.tLam e'))
  refine expr_det_step_closure (det_step_tBeta e') ?_
  refine (sem_expr_rel_move_single_subst B A δ (j - 1) e').mp ?_
  exact expr_rel_mono A _ j (j - 1) e' (Nat.sub_le _ _) (hbody (interp_type B δ))

theorem compat_pack (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (A.subst1 B)) : semTyped Γ (.pack e) (.exist A) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .packCtx _ k δ (A.subst1 B) (.exist A) (he θ δ k hctx) (fun j v hj hv => ?_)
  show exprRel δ (.exist A) j (.pack v.toExpr)
  refine sem_val_expr_rel (.exist A) δ j (.packV v) ?_
  simp only [valRel]
  exact ⟨v, rfl, interp_type B δ, (sem_val_rel_move_single_subst B A δ j v).mpr hv⟩

theorem compat_unpack (Γ : TypingContext) (A B : Ty) (e e' : Expr) (x : String)
    (h : semTyped Γ e (.exist A))
    (h' : semTyped (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ) x A) e' (B.rename (· + 1))) :
    semTyped Γ (.unpack (.bNamed x) e e') B := by
  obtain ⟨hcl, he⟩ := h
  obtain ⟨hcl', he'⟩ := h'
  refine ⟨?_, fun θ δ k hctx => ?_⟩
  · simp only [closed, Expr.isClosed, Bool.and_eq_true]
    refine ⟨hcl, ?_⟩
    show closed (x :: TypingContext.domList Γ) e'
    refine closed_weaken hcl' fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (mem_shiftCtx_domList.mp hy')
  · simp only [substMap, binderDelete]
    refine bind_item (.unpackCtx (.bNamed x) (substMap (delete (M := MapStr) θ x) e')) _ k δ
      (.exist A) B (he θ δ k hctx) (fun j v hj hv => ?_)
    simp only [valRel] at hv
    obtain ⟨v', rfl, τ, hv'⟩ := hv
    show exprRel δ B j
      (.unpack (.bNamed x) (.pack v'.toExpr) (substMap (delete (M := MapStr) θ x) e'))
    refine expr_det_step_closure
      (det_step_unpack (.bNamed x) v'.toExpr _ (val_isVal v')) ?_
    rw [show subst' (Binder.bNamed x) v'.toExpr (substMap (delete (M := MapStr) θ x) e') =
        substMap (Iris.Std.insert (M := MapStr) θ x v'.toExpr) e' from
      subst_substMap x v'.toExpr θ e' (sem_context_rel_closed hctx)]
    refine (sem_expr_rel_cons B δ (j - 1) _ τ).mpr (he' _ (τ .: δ) (j - 1) ?_)
    exact .insert v' x A (val_rel_mono A _ j (j - 1) v' (Nat.sub_le _ _) hv')
      (sem_context_rel_cons τ (sem_context_rel_mono (show j - 1 ≤ k by omega) hctx))

theorem compat_if (Γ : TypingContext) (e₀ e₁ e₂ : Expr) (A : Ty)
    (h₀ : semTyped Γ e₀ .bool) (h₁ : semTyped Γ e₁ A) (h₂ : semTyped Γ e₂ A) :
    semTyped Γ (.ite e₀ e₁ e₂) A := by
  obtain ⟨hcl₀, he₀⟩ := h₀
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hcl₀, hcl₁⟩, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.ifCtx (substMap θ e₁) (substMap θ e₂)) _ k δ .bool A (he₀ θ δ k hctx)
    (fun j v hj hv => ?_)
  simp only [valRel] at hv
  obtain ⟨b, rfl⟩ := hv
  show exprRel δ A j (.ite (.lit (.litBool b)) (substMap θ e₁) (substMap θ e₂))
  cases b
  · exact expr_det_step_closure (det_step_if_false _ _)
      (expr_rel_mono A δ k (j - 1) _ (by omega) (he₂ θ δ k hctx))
  · exact expr_det_step_closure (det_step_if_true _ _)
      (expr_rel_mono A δ k (j - 1) _ (by omega) (he₁ θ δ k hctx))

theorem compat_pair (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ A) (h₂ : semTyped Γ e₂ B) : semTyped Γ (.pair e₁ e₂) (.prod A B) := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.pairRCtx (substMap θ e₁)) _ k δ B (.prod A B) (he₂ θ δ k hctx)
    (fun j v₂ hj hv₂ => ?_)
  show exprRel δ (.prod A B) j (.pair (substMap θ e₁) v₂.toExpr)
  refine bind_item (.pairLCtx v₂) _ j δ A (.prod A B)
    (expr_rel_mono A δ k j _ hj (he₁ θ δ k hctx)) (fun j' v₁ hj' hv₁ => ?_)
  show exprRel δ (.prod A B) j' (.pair v₁.toExpr v₂.toExpr)
  refine sem_val_expr_rel (.prod A B) δ j' (.pairV v₁ v₂) ?_
  simp only [valRel]
  exact ⟨v₁, v₂, rfl, hv₁, val_rel_mono B δ j j' v₂ hj' hv₂⟩

theorem compat_fst (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.prod A B)) : semTyped Γ (.fst e) A := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .fstCtx _ k δ (.prod A B) A (he θ δ k hctx) (fun j v hj hv => ?_)
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
  show exprRel δ A j (.fst (.pair v₁.toExpr v₂.toExpr))
  refine expr_det_step_closure (det_step_fst _ _ (val_isVal v₁) (val_isVal v₂)) ?_
  exact sem_val_expr_rel A δ (j - 1) v₁ (val_rel_mono A δ j (j - 1) v₁ (Nat.sub_le _ _) hv₁)

theorem compat_snd (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.prod A B)) : semTyped Γ (.snd e) B := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .sndCtx _ k δ (.prod A B) B (he θ δ k hctx) (fun j v hj hv => ?_)
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
  show exprRel δ B j (.snd (.pair v₁.toExpr v₂.toExpr))
  refine expr_det_step_closure (det_step_snd _ _ (val_isVal v₁) (val_isVal v₂)) ?_
  exact sem_val_expr_rel B δ (j - 1) v₂ (val_rel_mono B δ j (j - 1) v₂ (Nat.sub_le _ _) hv₂)

theorem compat_injl (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e A) : semTyped Γ (.injL e) (.sum A B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .injLCtx _ k δ A (.sum A B) (he θ δ k hctx) (fun j v hj hv => ?_)
  show exprRel δ (.sum A B) j (.injL v.toExpr)
  refine sem_val_expr_rel (.sum A B) δ j (.injLV v) ?_
  simp only [valRel]
  exact Or.inl ⟨v, rfl, hv⟩

theorem compat_injr (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e B) : semTyped Γ (.injR e) (.sum A B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .injRCtx _ k δ B (.sum A B) (he θ δ k hctx) (fun j v hj hv => ?_)
  show exprRel δ (.sum A B) j (.injR v.toExpr)
  refine sem_val_expr_rel (.sum A B) δ j (.injRV v) ?_
  simp only [valRel]
  exact Or.inr ⟨v, rfl, hv⟩

theorem compat_case (Γ : TypingContext) (e e₁ e₂ : Expr) (A B C : Ty)
    (h : semTyped Γ e (.sum B C)) (h₁ : semTyped Γ e₁ (.fn B A))
    (h₂ : semTyped Γ e₂ (.fn C A)) : semTyped Γ (.case e e₁ e₂) A := by
  obtain ⟨hcl, he⟩ := h
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hcl, hcl₁⟩, hcl₂⟩,
    fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item (.caseCtx (substMap θ e₁) (substMap θ e₂)) _ k δ (.sum B C) A
    (he θ δ k hctx) (fun j v hj hv => ?_)
  simp only [valRel] at hv
  rcases hv with ⟨v', rfl, hv'⟩ | ⟨v', rfl, hv'⟩
  · show exprRel δ A j (.case (.injL v'.toExpr) (substMap θ e₁) (substMap θ e₂))
    refine expr_det_step_closure (det_step_caseL _ _ _ (val_isVal v')) ?_
    exact semantic_app B A δ (j - 1) _ _
      (expr_rel_mono _ δ k (j - 1) _ (by omega) (he₁ θ δ k hctx))
      (sem_val_expr_rel B δ (j - 1) v' (val_rel_mono B δ j (j - 1) v' (Nat.sub_le _ _) hv'))
  · show exprRel δ A j (.case (.injR v'.toExpr) (substMap θ e₁) (substMap θ e₂))
    refine expr_det_step_closure (det_step_caseR _ _ _ (val_isVal v')) ?_
    exact semantic_app C A δ (j - 1) _ _
      (expr_rel_mono _ δ k (j - 1) _ (by omega) (he₂ θ δ k hctx))
      (sem_val_expr_rel C δ (j - 1) v' (val_rel_mono C δ j (j - 1) v' (Nat.sub_le _ _) hv'))

theorem compat_roll (Γ : TypingContext) (e : Expr) (A : Ty)
    (h : semTyped Γ e (Ty.subst1 A (.mu A))) : semTyped Γ (.roll e) (.mu A) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .rollCtx _ k δ (Ty.subst1 A (.mu A)) (.mu A) (he θ δ k hctx)
    (fun j v hj hv => ?_)
  show exprRel δ (.mu A) j (.roll v.toExpr)
  refine sem_val_expr_rel (.mu A) δ j (.rollV v) ?_
  simp only [valRel]
  exact ⟨v, rfl, val_rel_is_closed v δ j _ hv,
    fun k' hk' => val_rel_mono _ δ j k' v (Nat.le_of_lt hk') hv⟩

theorem compat_unroll (Γ : TypingContext) (e : Expr) (A : Ty)
    (h : semTyped Γ e (.mu A)) : semTyped Γ (.unroll e) (Ty.subst1 A (.mu A)) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ k hctx => ?_⟩
  simp only [substMap]
  refine bind_item .unrollCtx _ k δ (.mu A) (Ty.subst1 A (.mu A)) (he θ δ k hctx)
    (fun j v hj hv => ?_)
  match j, hv with
  | 0, _ => exact sem_expr_rel_zero_trivial _ δ _
  | j + 1, hv =>
    simp only [valRel] at hv
    obtain ⟨v', rfl, _, hv'⟩ := hv
    show exprRel δ (Ty.subst1 A (.mu A)) (j + 1) (.unroll (.roll v'.toExpr))
    refine expr_det_step_closure (det_step_unroll _ (val_isVal v')) ?_
    exact sem_val_expr_rel _ δ _ v' (hv' (j + 1 - 1) (by omega))

/-! ## The fundamental theorem and semantic type safety -/

theorem sem_soundness {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (h : SynTyped n Γ e A) : semTyped Γ e A := by
  induction h with
  | typed_lit_int _ Γ z => exact compat_int Γ z
  | typed_lit_bool _ Γ b => exact compat_bool Γ b
  | typed_lit_unit _ Γ => exact compat_unit Γ
  | typed_var _ Γ x A hx => exact compat_var Γ x A hx
  | typed_lam _ Γ x e A B _ _ ih => exact compat_lam_named Γ x e A B ih
  | typed_lam_anon _ Γ e A B _ _ ih => exact compat_lam_anon Γ e A B ih
  | typed_app _ Γ e₁ e₂ A B _ _ ih₁ ih₂ => exact compat_app Γ e₁ e₂ A B ih₁ ih₂
  | typed_tLam _ Γ e A _ ih => exact compat_tlam Γ e A ih
  | typed_tApp _ Γ e A B _ _ ih => exact compat_tapp Γ e A B ih
  | typed_pack _ Γ e A B _ _ _ ih => exact compat_pack Γ e A B ih
  | typed_unpack _ Γ x e₁ e₂ A B _ _ _ ih₁ ih₂ => exact compat_unpack Γ A B e₁ e₂ x ih₁ ih₂
  | typed_pair _ Γ e₁ e₂ A B _ _ ih₁ ih₂ => exact compat_pair Γ e₁ e₂ A B ih₁ ih₂
  | typed_fst _ Γ e A B _ ih => exact compat_fst Γ e A B ih
  | typed_snd _ Γ e A B _ ih => exact compat_snd Γ e A B ih
  | typed_injL _ Γ e A B _ _ ih => exact compat_injl Γ e A B ih
  | typed_injR _ Γ e A B _ _ ih => exact compat_injr Γ e A B ih
  | typed_case _ Γ e e₁ e₂ A B C _ _ _ ih ih₁ ih₂ => exact compat_case Γ e e₁ e₂ C A B ih ih₁ ih₂
  | typed_unOp _ Γ op e A B hop _ ih => exact compat_unop Γ op A B e hop ih
  | typed_binOp _ Γ op e₁ e₂ A B C hop _ _ ih₁ ih₂ =>
    cases hop <;>
      first
        | exact compat_int_binop Γ _ e₁ e₂ (by constructor) ih₁ ih₂
        | exact compat_int_bool_binop Γ _ e₁ e₂ (by constructor) ih₁ ih₂
  | typed_if _ Γ e₀ e₁ e₂ A _ _ _ ih₀ ih₁ ih₂ => exact compat_if Γ e₀ e₁ e₂ A ih₀ ih₁ ih₂
  | typed_roll _ Γ e A _ ih => exact compat_roll Γ e A ih
  | typed_unroll _ Γ e A _ ih => exact compat_unroll Γ e A ih

/-- The dummy interpretation: every closed value, at every index. -/
def any_type : SemType where
  car _ v := closed [] v.toExpr
  closed_val _ _ h := h
  mono _ _ _ h _ := h

def δ_any : TyVarInterp := fun _ => any_type

/-- No reduction of `e` ever gets stuck. -/
def safe (e : Expr) : Prop :=
  ∀ (e' : Expr) (n : Nat), redNsteps n e e' → Expr.isVal e'

theorem type_safety {e : Expr} {A : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) : safe e := by
  obtain ⟨_, hsem⟩ := sem_soundness h
  intro e' n hred
  have hE := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any (n + 1) .empty
  rw [substMap_empty] at hE
  simp only [exprRel] at hE
  obtain ⟨v, hv, _⟩ := hE e' n (by omega) hred
  exact toVal?_isVal hv

end SystemFMu
