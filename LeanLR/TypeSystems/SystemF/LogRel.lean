import LeanLR.TypeSystems.SystemF.Lang
import LeanLR.TypeSystems.SystemF.Notation
import LeanLR.TypeSystems.SystemF.Types
import LeanLR.TypeSystems.SystemF.TypeSafety
import LeanLR.TypeSystems.SystemF.BigStep
import LeanLR.TypeSystems.SystemF.ParallelSubst

/-!
# System F: the unary logical relation

`systemf/logrel.v`. A logical relation over the big-step semantics, indexed by an interpretation
`δ` of the free type variables, culminating in the fundamental theorem (`sem_soundness`) and
termination of well-typed programs.

There is no step index: System F has no recursive types, so the relation recurses on the type. The
measure is `Ty.size`, with the expression relation charged one more than the value relation at the
same type, exactly as Rocq's `mut_measure` does.
-/

open Iris.Std

namespace SystemF

/-! ## Semantic types -/

/-- A predicate on values that only holds of closed ones. -/
structure SemType where
  car : Val → Prop
  closed_val : ∀ v, car v → closed [] v.toExpr

abbrev TyVarInterp := Nat → SemType

/-- Autosubst's `τ .: δ`: extend an interpretation at index `0`. -/
def TyVarInterp.cons (τ : SemType) (δ : TyVarInterp) : TyVarInterp
  | 0 => τ
  | n + 1 => δ n

@[inherit_doc] notation:max τ " .: " δ => TyVarInterp.cons τ δ

@[simp] theorem cons_zero (τ : SemType) (δ : TyVarInterp) : (τ .: δ) 0 = τ := rfl

@[simp] theorem cons_succ (τ : SemType) (δ : TyVarInterp) (n : Nat) : (τ .: δ) (n + 1) = δ n := rfl

def Ty.size : Ty → Nat
  | .tVar _ => 1
  | .int => 1
  | .bool => 1
  | .unit => 1
  | .fn A B => A.size + B.size + 1
  | .all A => A.size + 2
  | .exist A => A.size + 2
  | .prod A B => A.size + B.size + 1
  | .sum A B => max A.size B.size + 1

/-! ## The logical relation

Rocq defines the two relations as one `Equations` definition over `val_or_expr`; Lean's `mutual`
does the same job, with `2 * Ty.size` for the value relation and `2 * Ty.size + 1` for the
expression relation as the common measure (Rocq's `mut_measure`). -/

/-- `valRel δ A v`: the value `v` belongs to type `A` under the interpretation `δ`. The function
and universal cases inline the expression relation (`exprRel` below), exactly as Rocq's single
`Equations` definition over `val_or_expr` does, so that the recursion is on the type alone. -/
def valRel (δ : TyVarInterp) : Ty → Val → Prop
  | .int, v => ∃ z : Int, v = .litV (.litInt z)
  | .bool, v => ∃ b : Bool, v = .litV (.litBool b)
  | .unit, v => v = .litV .litUnit
  | .tVar α, v => (δ α).car v
  | .prod A B, v => ∃ v₁ v₂ : Val, v = .pairV v₁ v₂ ∧ valRel δ A v₁ ∧ valRel δ B v₂
  | .sum A B, v =>
      (∃ v' : Val, v = .injLV v' ∧ valRel δ A v') ∨
      (∃ v' : Val, v = .injRV v' ∧ valRel δ B v')
  | .fn A B, v =>
      ∃ (x : Binder) (e : Expr), v = .lamV x e ∧ closed (x :b: []) e ∧
        ∀ v' : Val, valRel δ A v' →
          ∃ w : Val, BigStep (subst' x v'.toExpr e) w ∧ valRel δ B w
  | .all A, v =>
      ∃ e : Expr, v = .tLamV e ∧ closed [] e ∧
        ∀ τ : SemType, ∃ w : Val, BigStep e w ∧ valRel (τ .: δ) A w
  | .exist A, v => ∃ v' : Val, v = .packV v' ∧ ∃ τ : SemType, valRel (τ .: δ) A v'
termination_by A _ => A.size
decreasing_by all_goals simp_wf <;> simp [Ty.size] <;> omega

/-- `exprRel δ A e`: `e` evaluates to a value of type `A`. -/
def exprRel (δ : TyVarInterp) (A : Ty) (e : Expr) : Prop :=
  ∃ v : Val, BigStep e v ∧ valRel δ A v

/-! ## Basic properties -/

/-- The value relation only relates closed values. -/
theorem val_rel_closed (v : Val) (δ : TyVarInterp) (A : Ty) (h : valRel δ A v) :
    closed [] v.toExpr := by
  induction A generalizing δ v with
  | tVar α =>
    simp only [valRel] at h
    exact (δ α).closed_val v h
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
    exact ih v' _ hv'
  | prod A B ihA ihB =>
    simp only [valRel] at h
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    simp only [closed, Val.toExpr, Expr.isClosed, Bool.and_eq_true]
    exact ⟨ihA _ _ h₁, ihB _ _ h₂⟩
  | sum A B ihA ihB =>
    simp only [valRel] at h
    rcases h with ⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩
    · exact ihA v' _ h'
    · exact ihB v' _ h'

/-- A syntactic type denotes a semantic type. -/
def interp_type (A : Ty) (δ : TyVarInterp) : SemType where
  car v := valRel δ A v
  closed_val v h := val_rel_closed v δ A h

theorem sem_expr_rel_of_val (A : Ty) (δ : TyVarInterp) (v : Val) (h : exprRel δ A v.toExpr) :
    valRel δ A v := by
  simp only [exprRel] at h
  obtain ⟨v', hbs, hv'⟩ := h
  rw [big_step_val hbs] at hv'
  exact hv'

theorem val_inclusion (A : Ty) (δ : TyVarInterp) (v : Val) (h : valRel δ A v) :
    exprRel δ A v.toExpr := by
  simp only [exprRel]
  exact ⟨v, big_step_of_val rfl, h⟩

/-! ## The context relation -/

inductive SemCtxRel (δ : TyVarInterp) : TypingContext → SubstMap → Prop where
  | empty :
      SemCtxRel δ (PartialMap.empty (M := TyMapStr) (V := Ty))
        (PartialMap.empty (M := MapStr) (V := Expr))
  | insert {Γ : TypingContext} {θ : SubstMap} (v : Val) (x : String) (A : Ty) :
      valRel δ A v → SemCtxRel δ Γ θ →
      SemCtxRel δ (Iris.Std.insert (M := TyMapStr) Γ x A)
        (Iris.Std.insert (M := MapStr) θ x v.toExpr)

/-- Inversion for a lookup in an extended map. -/
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

theorem sem_context_rel_closed {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ Γ θ) : substIsClosed [] θ := by
  induction h with
  | empty =>
    intro y e hy
    rw [show get? (M := MapStr) (PartialMap.empty (M := MapStr) (V := Expr)) y = none from
      LawfulPartialMap.get?_empty (M := MapStr) y] at hy
    exact absurd hy (by simp)
  | insert v x A hv _ ih =>
    intro y e hy
    rcases get?_insert_cases hy with ⟨_, rfl⟩ | ⟨_, hy'⟩
    · exact val_rel_closed v _ A hv
    · exact ih y e hy'

theorem sem_context_rel_vals {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap} {x : String}
    {A : Ty} (h : SemCtxRel δ Γ θ) (hx : get? (M := TyMapStr) Γ x = some A) :
    ∃ (e : Expr) (v : Val), get? (M := MapStr) θ x = some e ∧ e.toVal? = some v ∧
      valRel δ A v := by
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

/-- As the pointwise statement the port uses. -/
theorem sem_context_rel_dom {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ Γ θ) (x : String) :
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

def semTyped (Γ : TypingContext) (e : Expr) (A : Ty) : Prop :=
  closed Γ.domList e ∧ ∀ (θ : SubstMap) (δ : TyVarInterp), SemCtxRel δ Γ θ →
    exprRel δ A (substMap θ e)

/-! ## Moving the interpretation around

Rocq's `boring_lemmas` section: the value relation only depends on the interpretation pointwise,
and renaming or substituting in the type can be traded for a change of interpretation. -/

/-- Extending two pointwise-equal interpretations keeps them pointwise equal. -/
private theorem cons_iff {δ δ' : TyVarInterp} (τ : SemType)
    (hiff : ∀ n w, (δ n).car w ↔ (δ' n).car w) :
    ∀ n w, ((τ .: δ) n).car w ↔ ((τ .: δ') n).car w := by
  intro n w
  cases n with
  | zero => exact Iff.rfl
  | succ m => exact hiff m w

theorem sem_val_rel_ext (B : Ty) (δ δ' : TyVarInterp) (v : Val)
    (hiff : ∀ n w, (δ n).car w ↔ (δ' n).car w) : valRel δ B v ↔ valRel δ' B v := by
  induction B generalizing δ δ' v with
  | tVar α => simp only [valRel]; exact hiff α v
  | int | bool | unit => simp only [valRel]
  | fn A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ δ' v' hiff).mpr hv')
      exact ⟨w, hbs, (ihB δ δ' w hiff).mp hw⟩
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ δ' v' hiff).mp hv')
      exact ⟨w, hbs, (ihB δ δ' w hiff).mpr hw⟩
  | all A ih =>
    simp only [valRel]
    constructor
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (ih _ _ w (cons_iff τ hiff)).mp hw⟩
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (ih _ _ w (cons_iff τ hiff)).mpr hw⟩
  | exist A ih =>
    simp only [valRel]
    constructor
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (ih _ _ v' (cons_iff τ hiff)).mp hv'⟩
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (ih _ _ v' (cons_iff τ hiff)).mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA _ _ v₁ hiff).mp h₁, (ihB _ _ v₂ hiff).mp h₂⟩
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA _ _ v₁ hiff).mpr h₁, (ihB _ _ v₂ hiff).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [valRel]
    constructor
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA _ _ v' hiff).mp h'⟩
      · exact Or.inr ⟨v', rfl, (ihB _ _ v' hiff).mp h'⟩
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA _ _ v' hiff).mpr h'⟩
      · exact Or.inr ⟨v', rfl, (ihB _ _ v' hiff).mpr h'⟩

theorem sem_val_rel_move_ren (B : Ty) (δ : TyVarInterp) (σ : Nat → Nat) (v : Val) :
    valRel (fun n => δ (σ n)) B v ↔ valRel δ (B.rename σ) v := by
  induction B generalizing δ σ v with
  | tVar α => simp only [Ty.rename, valRel]
  | int | bool | unit => simp only [Ty.rename, valRel]
  | fn A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ σ v').mpr hv')
      exact ⟨w, hbs, (ihB δ σ w).mp hw⟩
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ σ v').mp hv')
      exact ⟨w, hbs, (ihB δ σ w).mpr hw⟩
  | all A ih =>
    simp only [Ty.rename, valRel]
    have hcons : ∀ (τ : SemType) (w : Val),
        valRel (τ .: fun n => δ (σ n)) A w ↔
          valRel (τ .: δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) w := by
      intro τ w
      refine Iff.trans ?_ (ih (τ .: δ) _ w)
      refine sem_val_rel_ext A _ _ w fun n u => ?_
      cases n <;> exact Iff.rfl
    constructor
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (hcons τ w).mp hw⟩
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (hcons τ w).mpr hw⟩
  | exist A ih =>
    simp only [Ty.rename, valRel]
    have hcons : ∀ (τ : SemType) (w : Val),
        valRel (τ .: fun n => δ (σ n)) A w ↔
          valRel (τ .: δ) (A.rename (fun n => match n with | 0 => 0 | n+1 => σ n + 1)) w := by
      intro τ w
      refine Iff.trans ?_ (ih (τ .: δ) _ w)
      refine sem_val_rel_ext A _ _ w fun n u => ?_
      cases n <;> exact Iff.rfl
    constructor
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (hcons τ v').mp hv'⟩
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (hcons τ v').mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA δ σ v₁).mp h₁, (ihB δ σ v₂).mp h₂⟩
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA δ σ v₁).mpr h₁, (ihB δ σ v₂).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [Ty.rename, valRel]
    constructor
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA δ σ v').mp h'⟩
      · exact Or.inr ⟨v', rfl, (ihB δ σ v').mp h'⟩
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA δ σ v').mpr h'⟩
      · exact Or.inr ⟨v', rfl, (ihB δ σ v').mpr h'⟩

theorem sem_val_rel_move_subst (B : Ty) (δ : TyVarInterp) (σ : Nat → Ty) (v : Val) :
    valRel (fun n => interp_type (σ n) δ) B v ↔ valRel δ (B.substTy σ) v := by
  induction B generalizing δ σ v with
  | tVar α => simp only [Ty.substTy, valRel, interp_type]
  | int | bool | unit => simp only [Ty.substTy, valRel]
  | fn A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ σ v').mpr hv')
      exact ⟨w, hbs, (ihB δ σ w).mp hw⟩
    · rintro ⟨x, e, rfl, hcl, hbody⟩
      refine ⟨x, e, rfl, hcl, fun v' hv' => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody v' ((ihA δ σ v').mp hv')
      exact ⟨w, hbs, (ihB δ σ w).mpr hw⟩
  | all A ih =>
    simp only [Ty.substTy, valRel]
    have hcons : ∀ (τ : SemType) (w : Val),
        valRel (τ .: fun n => interp_type (σ n) δ) A w ↔
          valRel (τ .: δ) (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) w := by
      intro τ w
      refine Iff.trans ?_ (ih (τ .: δ) _ w)
      refine sem_val_rel_ext A _ _ w fun n u => ?_
      cases n with
      | zero =>
        show τ.car u ↔ (interp_type (Ty.tVar 0) (τ .: δ)).car u
        simp only [interp_type, valRel, cons_zero]
      | succ m =>
        show (interp_type (σ m) δ).car u ↔ (interp_type ((σ m).rename (· + 1)) (τ .: δ)).car u
        exact sem_val_rel_move_ren (σ m) (τ .: δ) (· + 1) u
    constructor
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (hcons τ w).mp hw⟩
    · rintro ⟨e, rfl, hcl, hbody⟩
      refine ⟨e, rfl, hcl, fun τ => ?_⟩
      obtain ⟨w, hbs, hw⟩ := hbody τ
      exact ⟨w, hbs, (hcons τ w).mpr hw⟩
  | exist A ih =>
    simp only [Ty.substTy, valRel]
    have hcons : ∀ (τ : SemType) (w : Val),
        valRel (τ .: fun n => interp_type (σ n) δ) A w ↔
          valRel (τ .: δ) (A.substTy
            (fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1))) w := by
      intro τ w
      refine Iff.trans ?_ (ih (τ .: δ) _ w)
      refine sem_val_rel_ext A _ _ w fun n u => ?_
      cases n with
      | zero =>
        show τ.car u ↔ (interp_type (Ty.tVar 0) (τ .: δ)).car u
        simp only [interp_type, valRel, cons_zero]
      | succ m =>
        show (interp_type (σ m) δ).car u ↔ (interp_type ((σ m).rename (· + 1)) (τ .: δ)).car u
        exact sem_val_rel_move_ren (σ m) (τ .: δ) (· + 1) u
    constructor
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (hcons τ v').mp hv'⟩
    · rintro ⟨v', rfl, τ, hv'⟩
      exact ⟨v', rfl, τ, (hcons τ v').mpr hv'⟩
  | prod A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA δ σ v₁).mp h₁, (ihB δ σ v₂).mp h₂⟩
    · rintro ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihA δ σ v₁).mpr h₁, (ihB δ σ v₂).mpr h₂⟩
  | sum A B ihA ihB =>
    simp only [Ty.substTy, valRel]
    constructor
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA δ σ v').mp h'⟩
      · exact Or.inr ⟨v', rfl, (ihB δ σ v').mp h'⟩
    · rintro (⟨v', rfl, h'⟩ | ⟨v', rfl, h'⟩)
      · exact Or.inl ⟨v', rfl, (ihA δ σ v').mpr h'⟩
      · exact Or.inr ⟨v', rfl, (ihB δ σ v').mpr h'⟩

theorem sem_val_rel_move_single_subst (A B : Ty) (δ : TyVarInterp) (v : Val) :
    valRel ((interp_type A δ) .: δ) B v ↔ valRel δ (B.subst1 A) v := by
  refine Iff.trans ?_ (sem_val_rel_move_subst B δ _ v)
  refine sem_val_rel_ext B _ _ v fun n u => ?_
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    show (δ m).car u ↔ (interp_type (Ty.tVar m) δ).car u
    simp only [interp_type, valRel]

theorem sem_val_rel_cons (A : Ty) (δ : TyVarInterp) (v : Val) (τ : SemType) :
    valRel δ A v ↔ valRel (τ .: δ) (A.rename (· + 1)) v :=
  sem_val_rel_move_ren A (τ .: δ) (· + 1) v

theorem sem_context_rel_cons {Γ : TypingContext} {δ : TyVarInterp} {θ : SubstMap} (τ : SemType)
    (h : SemCtxRel δ Γ θ) : SemCtxRel (τ .: δ) (shiftCtx Γ) θ := by
  induction h with
  | empty =>
    rw [shiftCtx_empty]
    exact .empty
  | insert v x A hv _ ih =>
    rw [shiftCtx_insert]
    exact .insert v x _ ((sem_val_rel_cons A _ v τ).mp hv) ih

/-! ## Domain bookkeeping -/

theorem mem_ctx_domList_insert {Γ : TypingContext} {x y : String} {A : Ty} :
    y ∈ TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A) ↔ y = x ∨ y ∈ Γ.domList := by
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

theorem sem_context_rel_domList {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap}
    (h : SemCtxRel δ Γ θ) (x : String) : x ∈ Γ.domList ↔ x ∈ θ.domList := by
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

/-- The closedness half of `compat_lam`; -/
theorem lam_closed {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap} (x : String) (A : Ty)
    (e : Expr) (hcl : closed (TypingContext.domList (Iris.Std.insert (M := TyMapStr) Γ x A)) e)
    (hctx : SemCtxRel δ Γ θ) :
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
        obtain ⟨B, hB⟩ := mem_ctx_domList.mp hy'
        obtain ⟨e', v, he', _, _⟩ := sem_context_rel_vals hctx hB
        exact ⟨e', by rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]; exact he'⟩
  · intro y e' hy
    refine closed_weaken (sem_context_rel_closed hctx y e' ?_) (by simp)
    by_cases hxy : x = y
    · subst hxy
      rw [LawfulPartialMap.get?_delete_eq (M := MapStr) rfl] at hy
      exact absurd hy (by simp)
    · rwa [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy] at hy

/-- The closedness half of `compat_lam_anon` and `compat_tlam`. -/
theorem substMap_ctx_closed {δ : TyVarInterp} {Γ : TypingContext} {θ : SubstMap} {e : Expr}
    (hcl : closed Γ.domList e) (hctx : SemCtxRel δ Γ θ) : closed [] (substMap θ e) := by
  refine substMap_closed ?_ (sem_context_rel_closed hctx)
  refine closed_weaken hcl fun y hy => ?_
  exact List.mem_append.mpr (Or.inr ((sem_context_rel_domList hctx y).mp hy))

/-! ## Compatibility lemmas -/

theorem compat_int (Γ : TypingContext) (z : Int) : semTyped Γ (.lit (.litInt z)) .int := by
  refine ⟨rfl, fun θ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV (.litInt z), .bs_lit _, ⟨z, rfl⟩⟩

theorem compat_bool (Γ : TypingContext) (b : Bool) : semTyped Γ (.lit (.litBool b)) .bool := by
  refine ⟨rfl, fun θ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV (.litBool b), .bs_lit _, ⟨b, rfl⟩⟩

theorem compat_unit (Γ : TypingContext) : semTyped Γ (.lit .litUnit) .unit := by
  refine ⟨rfl, fun θ δ _ => ?_⟩
  simp only [substMap, exprRel, valRel]
  exact ⟨.litV .litUnit, .bs_lit _, rfl⟩

theorem compat_var (Γ : TypingContext) (x : String) (A : Ty)
    (hx : get? (M := TyMapStr) Γ x = some A) : semTyped Γ (.var x) A := by
  refine ⟨?_, fun θ δ hctx => ?_⟩
  · simpa [closed, Expr.isClosed] using mem_ctx_domList.mpr ⟨A, hx⟩
  · obtain ⟨e, v, he, hv, hrel⟩ := sem_context_rel_vals hctx hx
    simp only [substMap, he, exprRel]
    exact ⟨v, big_step_of_val (toVal?_eq hv), hrel⟩

theorem compat_app (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ (.fn A B)) (h₂ : semTyped Γ e₂ A) : semTyped Γ (.app e₁ e₂) B := by
  obtain ⟨hcl₁, hfun⟩ := h₁
  obtain ⟨hcl₂, harg⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v₁, hb₁, hv₁⟩ := hfun θ δ hctx
  simp only [valRel] at hv₁
  obtain ⟨x, e, rfl, _, hbody⟩ := hv₁
  obtain ⟨v₂, hb₂, hv₂⟩ := harg θ δ hctx
  obtain ⟨v, hbv, hv⟩ := hbody v₂ hv₂
  simp only [substMap, exprRel]
  exact ⟨v, .bs_app _ _ x e v₂ v hb₁ hb₂ hbv, hv⟩

theorem compat_lam (Γ : TypingContext) (x : String) (e : Expr) (A B : Ty)
    (h : semTyped (Iris.Std.insert (M := TyMapStr) Γ x A) e B) :
    semTyped Γ (.lam (.bNamed x) e) (.fn A B) := by
  obtain ⟨hcl, hbody⟩ := h
  refine ⟨?_, fun θ δ hctx => ?_⟩
  · show closed (x :: TypingContext.domList Γ) e
    refine closed_weaken hcl fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ hy'
  · simp only [substMap, binderDelete, exprRel]
    refine ⟨.lamV (.bNamed x) (substMap (delete (M := MapStr) θ x) e), .bs_lam _ _, ?_⟩
    simp only [valRel]
    refine ⟨.bNamed x, _, rfl, lam_closed x A e hcl hctx, fun v' hv' => ?_⟩
    have hb := hbody (Iris.Std.insert (M := MapStr) θ x v'.toExpr) δ (.insert v' x A hv' hctx)
    rwa [← subst_substMap x v'.toExpr θ e (sem_context_rel_closed hctx)] at hb

theorem compat_lam_anon (Γ : TypingContext) (e : Expr) (A B : Ty) (h : semTyped Γ e B) :
    semTyped Γ (.lam .bAnon e) (.fn A B) := by
  obtain ⟨hcl, hbody⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  simp only [substMap, binderDelete, exprRel]
  refine ⟨.lamV .bAnon (substMap θ e), .bs_lam _ _, ?_⟩
  simp only [valRel]
  exact ⟨.bAnon, _, rfl, substMap_ctx_closed hcl hctx, fun v' _ => hbody θ δ hctx⟩

theorem compat_int_binop (Γ : TypingContext) (op : BinOp) (e₁ e₂ : Expr)
    (hop : BinOpTyped op .int .int .int) (h₁ : semTyped Γ e₁ .int) (h₂ : semTyped Γ e₂ .int) :
    semTyped Γ (.binOp op e₁ e₂) .int := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v₁, hb₁, hv₁⟩ := he₁ θ δ hctx
  obtain ⟨v₂, hb₂, hv₂⟩ := he₂ θ δ hctx
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl⟩ := hv₁
  obtain ⟨z₂, rfl⟩ := hv₂
  simp only [substMap, exprRel, valRel]
  cases hop
  · exact ⟨.litV (.litInt (z₁ + z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩
  · exact ⟨.litV (.litInt (z₁ - z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩
  · exact ⟨.litV (.litInt (z₁ * z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩

theorem compat_int_bool_binop (Γ : TypingContext) (op : BinOp) (e₁ e₂ : Expr)
    (hop : BinOpTyped op .int .int .bool) (h₁ : semTyped Γ e₁ .int) (h₂ : semTyped Γ e₂ .int) :
    semTyped Γ (.binOp op e₁ e₂) .bool := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v₁, hb₁, hv₁⟩ := he₁ θ δ hctx
  obtain ⟨v₂, hb₂, hv₂⟩ := he₂ θ δ hctx
  simp only [valRel] at hv₁ hv₂
  obtain ⟨z₁, rfl⟩ := hv₁
  obtain ⟨z₂, rfl⟩ := hv₂
  simp only [substMap, exprRel, valRel]
  cases hop
  · exact ⟨.litV (.litBool (z₁ < z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩
  · exact ⟨.litV (.litBool (z₁ ≤ z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩
  · exact ⟨.litV (.litBool (z₁ = z₂)), .bs_binop _ _ _ _ _ _ hb₁ hb₂ rfl, ⟨_, rfl⟩⟩

theorem compat_unop (Γ : TypingContext) (op : UnOp) (A B : Ty) (e : Expr)
    (hop : UnOpTyped op A B) (h : semTyped Γ e A) : semTyped Γ (.unOp op e) B := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [substMap, exprRel]
  cases hop
  · simp only [valRel] at hv
    obtain ⟨b, rfl⟩ := hv
    refine ⟨.litV (.litBool (!b)), .bs_unop _ _ _ _ hb rfl, ?_⟩
    simp only [valRel]
    exact ⟨_, rfl⟩
  · simp only [valRel] at hv
    obtain ⟨z, rfl⟩ := hv
    refine ⟨.litV (.litInt (-z)), .bs_unop _ _ _ _ hb rfl, ?_⟩
    simp only [valRel]
    exact ⟨_, rfl⟩

theorem compat_tlam (Γ : TypingContext) (e : Expr) (A : Ty)
    (h : semTyped (shiftCtx Γ) e A) : semTyped Γ (.tLam e) (.all A) := by
  obtain ⟨hcl, he⟩ := h
  have hcl' : closed Γ.domList e :=
    closed_weaken hcl fun y hy => mem_shiftCtx_domList.mp hy
  refine ⟨hcl', fun θ δ hctx => ?_⟩
  simp only [substMap, exprRel]
  refine ⟨.tLamV (substMap θ e), .bs_tlam _, ?_⟩
  simp only [valRel]
  exact ⟨_, rfl, substMap_ctx_closed hcl' hctx, fun τ => he θ (τ .: δ) (sem_context_rel_cons τ hctx)⟩

theorem compat_tapp (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.all A)) : semTyped Γ (.tApp e) (A.subst1 B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [valRel] at hv
  obtain ⟨e', rfl, _, hbody⟩ := hv
  obtain ⟨w, hb', hw⟩ := hbody (interp_type B δ)
  simp only [substMap, exprRel]
  exact ⟨w, .bs_tapp _ _ _ hb hb', (sem_val_rel_move_single_subst B A δ w).mp hw⟩

theorem compat_pack (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (A.subst1 B)) : semTyped Γ (.pack e) (.exist A) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.packV v, .bs_pack _ v hb, ?_⟩
  simp only [valRel]
  exact ⟨v, rfl, interp_type B δ, (sem_val_rel_move_single_subst B A δ v).mpr hv⟩

theorem compat_unpack (Γ : TypingContext) (A B : Ty) (e e' : Expr) (x : String)
    (h : semTyped Γ e (.exist A))
    (h' : semTyped (Iris.Std.insert (M := TyMapStr) (shiftCtx Γ) x A) e' (B.rename (· + 1))) :
    semTyped Γ (.unpack (.bNamed x) e e') B := by
  obtain ⟨hcl, he⟩ := h
  obtain ⟨hcl', he'⟩ := h'
  refine ⟨?_, fun θ δ hctx => ?_⟩
  · simp only [closed, Expr.isClosed, Bool.and_eq_true]
    refine ⟨hcl, ?_⟩
    show closed (x :: TypingContext.domList Γ) e'
    refine closed_weaken hcl' fun y hy => ?_
    rcases mem_ctx_domList_insert.mp hy with rfl | hy'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (mem_shiftCtx_domList.mp hy')
  · obtain ⟨v, hb, hv⟩ := he θ δ hctx
    simp only [valRel] at hv
    obtain ⟨v', rfl, τ, hv'⟩ := hv
    obtain ⟨w, hbw, hw⟩ := he' (Iris.Std.insert (M := MapStr) θ x v'.toExpr) (τ .: δ)
      (.insert v' x A hv' (sem_context_rel_cons τ hctx))
    simp only [substMap, binderDelete, exprRel]
    refine ⟨w, .bs_unpack _ _ v' w (.bNamed x) hb ?_, (sem_val_rel_cons B δ w τ).mpr hw⟩
    rwa [← subst_substMap x v'.toExpr θ e' (sem_context_rel_closed hctx)] at hbw

theorem compat_if (Γ : TypingContext) (e₀ e₁ e₂ : Expr) (A : Ty)
    (h₀ : semTyped Γ e₀ .bool) (h₁ : semTyped Γ e₁ A) (h₂ : semTyped Γ e₂ A) :
    semTyped Γ (.ite e₀ e₁ e₂) A := by
  obtain ⟨hcl₀, he₀⟩ := h₀
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hcl₀, hcl₁⟩, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v₀, hb₀, hv₀⟩ := he₀ θ δ hctx
  simp only [valRel] at hv₀
  obtain ⟨b, rfl⟩ := hv₀
  obtain ⟨v₁, hb₁, hv₁⟩ := he₁ θ δ hctx
  obtain ⟨v₂, hb₂, hv₂⟩ := he₂ θ δ hctx
  simp only [substMap, exprRel]
  cases b
  · exact ⟨v₂, .bs_if_false _ _ _ v₂ hb₀ hb₂, hv₂⟩
  · exact ⟨v₁, .bs_if_true _ _ _ v₁ hb₀ hb₁, hv₁⟩

theorem compat_pair (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty)
    (h₁ : semTyped Γ e₁ A) (h₂ : semTyped Γ e₂ B) : semTyped Γ (.pair e₁ e₂) (.prod A B) := by
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨hcl₁, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v₁, hb₁, hv₁⟩ := he₁ θ δ hctx
  obtain ⟨v₂, hb₂, hv₂⟩ := he₂ θ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.pairV v₁ v₂, .bs_pair _ _ v₁ v₂ hb₁ hb₂, ?_⟩
  simp only [valRel]
  exact ⟨v₁, v₂, rfl, hv₁, hv₂⟩

theorem compat_fst (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.prod A B)) : semTyped Γ (.fst e) A := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
  simp only [substMap, exprRel]
  exact ⟨v₁, .bs_fst _ v₁ v₂ hb, hv₁⟩

theorem compat_snd (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e (.prod A B)) : semTyped Γ (.snd e) B := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [valRel] at hv
  obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
  simp only [substMap, exprRel]
  exact ⟨v₂, .bs_snd _ v₁ v₂ hb, hv₂⟩

theorem compat_injl (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e A) : semTyped Γ (.injL e) (.sum A B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.injLV v, .bs_injl _ v hb, ?_⟩
  simp only [valRel]
  exact Or.inl ⟨v, rfl, hv⟩

theorem compat_injr (Γ : TypingContext) (e : Expr) (A B : Ty)
    (h : semTyped Γ e B) : semTyped Γ (.injR e) (.sum A B) := by
  obtain ⟨hcl, he⟩ := h
  refine ⟨hcl, fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [substMap, exprRel]
  refine ⟨.injRV v, .bs_injr _ v hb, ?_⟩
  simp only [valRel]
  exact Or.inr ⟨v, rfl, hv⟩

theorem compat_case (Γ : TypingContext) (e e₁ e₂ : Expr) (A B C : Ty)
    (h : semTyped Γ e (.sum B C)) (h₁ : semTyped Γ e₁ (.fn B A))
    (h₂ : semTyped Γ e₂ (.fn C A)) : semTyped Γ (.case e e₁ e₂) A := by
  obtain ⟨hcl, he⟩ := h
  obtain ⟨hcl₁, he₁⟩ := h₁
  obtain ⟨hcl₂, he₂⟩ := h₂
  refine ⟨by simp only [closed, Expr.isClosed, Bool.and_eq_true]; exact ⟨⟨hcl, hcl₁⟩, hcl₂⟩,
    fun θ δ hctx => ?_⟩
  obtain ⟨v, hb, hv⟩ := he θ δ hctx
  simp only [valRel] at hv
  simp only [substMap, exprRel]
  rcases hv with ⟨v', rfl, hv'⟩ | ⟨v', rfl, hv'⟩
  · obtain ⟨w, hbw, hw⟩ := he₁ θ δ hctx
    simp only [valRel] at hw
    obtain ⟨x, e', rfl, _, hbody⟩ := hw
    obtain ⟨u, hbu, hu⟩ := hbody v' hv'
    exact ⟨u, .bs_casel _ _ _ v' u hb
      (.bs_app _ _ x e' v' u hbw (big_step_of_val rfl) hbu), hu⟩
  · obtain ⟨w, hbw, hw⟩ := he₂ θ δ hctx
    simp only [valRel] at hw
    obtain ⟨x, e', rfl, _, hbody⟩ := hw
    obtain ⟨u, hbu, hu⟩ := hbody v' hv'
    exact ⟨u, .bs_caser _ _ _ v' u hb
      (.bs_app _ _ x e' v' u hbw (big_step_of_val rfl) hbu), hu⟩

/-! ## The fundamental theorem -/

theorem sem_soundness {n : Nat} {Γ : TypingContext} {e : Expr} {A : Ty}
    (h : SynTyped n Γ e A) : semTyped Γ e A := by
  induction h with
  | typed_lit_int _ Γ z => exact compat_int Γ z
  | typed_lit_bool _ Γ b => exact compat_bool Γ b
  | typed_lit_unit _ Γ => exact compat_unit Γ
  | typed_var _ Γ x A hx => exact compat_var Γ x A hx
  | typed_lam _ Γ x e A B _ _ ih => exact compat_lam Γ x e A B ih
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

/-- The dummy interpretation: every closed value. -/
def any_type : SemType where
  car v := closed [] v.toExpr
  closed_val _ h := h

def δ_any : TyVarInterp := fun _ => any_type

/-- Every well-typed closed program evaluates to a value. -/
theorem termination {e : Expr} {A : Ty}
    (h : SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) e A) :
    ∃ v : Val, BigStep e v := by
  obtain ⟨_, hsem⟩ := sem_soundness h
  obtain ⟨v, hb, _⟩ := hsem (PartialMap.empty (M := MapStr) (V := Expr)) δ_any .empty
  rw [substMap_empty] at hb
  exact ⟨v, hb⟩

end SystemF
