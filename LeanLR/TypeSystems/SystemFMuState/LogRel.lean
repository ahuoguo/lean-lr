/-
  System F with recursive types and mutable state - Logical Relation
  Step-indexed logical relation with world satisfaction for mutable state.
  Ported from semantics-2025/theories/type_systems/systemf_mu_state/logrel.v
-/

import LeanLR.TypeSystems.SystemFMuState.Lang
import LeanLR.TypeSystems.SystemFMuState.Types
import LeanLR.TypeSystems.SystemFMuState.Execution
import LeanLR.TypeSystems.SystemFMuState.ParallelSubst

open Iris.Std

namespace SystemFMuState

abbrev HeapInv := Nat → Val → Prop
abbrev World := List HeapInv

instance : Inhabited HeapInv := ⟨fun _ _ => True⟩

def worldExt (W W' : World) : Prop := ∃ Wn, W' = W ++ Wn

-- Semantic type: step-indexed, world-indexed value predicate with closure properties
structure SemType where
  rel : Nat → World → Val → Prop
  closed_val : ∀ k W v, rel k W v → SystemFMuState.closed [] v.toExpr
  mono : ∀ k k' W v, rel k W v → k' ≤ k → rel k' W v
  mono_world : ∀ k W W' v, rel k W v → worldExt W W' → rel k W' v

-- World satisfaction
def wsat (W : World) (h : Heap) : Prop :=
  ∀ (i : Nat), i < W.length →
    ∃ v, h ⟨i⟩ = some v ∧ (W[i]!) 0 v -- simplified: invariant holds at step 0

-- Type variable interpretation
abbrev TyVarInterp := Nat → SemType

-- Type size measure (for termination)
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
  | .ref _ => 2

-- Helper theorems for termination proofs on lex product (k, type_size, case_bit)
private theorem lex_decr {k₁ k₂ s₁ s₂ c₁ c₂ : Nat}
    (hk : k₁ ≤ k₂) (hs : s₁ < s₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s₁, c₁) (k₂, s₂, c₂) := by
  rcases Nat.lt_or_eq_of_le hk with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · subst heq; exact Prod.Lex.right _ (Prod.Lex.left _ _ hs)

private theorem lex_decr_case {k₁ k₂ s : Nat}
    (hk : k₁ ≤ k₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s, 0) (k₂, s, 1) := by
  rcases Nat.lt_or_eq_of_le hk with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · subst heq; exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

private theorem lex_mu {k kd s₁ s₂ c : Nat} :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k - kd, s₁, c) (k + 1, s₂, 0) :=
  Prod.Lex.left _ _ (by omega)

-- Value relation 𝒱⟦A⟧(δ, k, W, v) and Expression relation ℰ⟦A⟧(δ, k, W, e)
-- Defined by well-founded recursion on (k, Ty.size A, case_bit)
mutual
  def valRel (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) : Prop :=
    match A, k, v with
    | .int, k, .litV (.litInt _) => True
    | .int, k, _ => False
    | .bool, k, .litV (.litBool _) => True
    | .bool, k, _ => False
    | .unit, k, .litV .litUnit => True
    | .unit, k, _ => False
    | .tVar n, k, v => (δ n).rel k W v
    | .prod A B, k, .pairV v₁ v₂ => valRel δ A k W v₁ ∧ valRel δ B k W v₂
    | .prod _ _, k, _ => False
    | .sum A _, k, .injLV v => valRel δ A k W v
    | .sum _ B, k, .injRV v => valRel δ B k W v
    | .sum _ _, k, _ => False
    | .fn A B, k, .lamV x e =>
        SystemFMuState.closed (x :b: []) e ∧
        ∀ v' kd W', worldExt W W' →
          valRel δ A (k - kd) W' v' →
          exprRel δ B (k - kd) W' (subst' x v'.toExpr e)
    | .fn _ _, k, _ => False
    | .all A, k, .tLamV e =>
        SystemFMuState.closed [] e ∧
        ∀ τ : SemType, exprRel (fun n => match n with | 0 => τ | n+1 => δ n) A k W e
    | .all _, k, _ => False
    | .exist A, k, .packV v =>
        ∃ τ : SemType, valRel (fun n => match n with | 0 => τ | n+1 => δ n) A k W v
    | .exist _, k, _ => False
    | .mu _, 0, .rollV v => SystemFMuState.closed [] v.toExpr
    | .mu A, k+1, .rollV v =>
        SystemFMuState.closed [] v.toExpr ∧
        ∀ kd, valRel δ (A.subst1 (.mu A)) (k - kd) W v
    | .mu _, _, _ => False
    | .ref _, k, .litV (.litLoc l) => ∃ i : Nat, l = ⟨i⟩ ∧ i < W.length
    | .ref _, k, _ => False
  termination_by (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]; omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | exact lex_decr (Nat.sub_le _ _) (by simp [Ty.size]; omega)
      | exact Prod.Lex.left _ _ (by omega)
      -- all/exist calling exprRel at same k, smaller type
      | exact lex_decr Nat.le.refl (by simp [Ty.size])

  def exprRel (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (e : Expr) : Prop :=
    ∀ e' h h' n, worldExt W W → wsat W h → n < k →
      redNsteps n e h e' h' →
      ∃ v W', e'.toVal? = some v ∧
        worldExt W W' ∧ wsat W' h' ∧ valRel δ A (k - n) W' v
  termination_by (k, A.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

-- Semantic context relation
def semCtxRel (δ : TyVarInterp) (Γ : TypingContext) (W : World) (k : Nat) (θ : SubstMap) : Prop :=
  ∀ x A, get? (M := TyMapStr) Γ x = some A →
    ∃ v, get? (M := MapStr) θ x = some v.toExpr ∧ valRel δ A k W v

-- Semantic typing
def semTyped (Γ : TypingContext) (e : Expr) (A : Ty) : Prop :=
  ∀ δ W k θ, semCtxRel δ Γ W k θ → exprRel δ A k W (substMap θ e)

-- Compatibility lemmas
theorem compat_int (Γ : TypingContext) (z : Int) : semTyped Γ (.lit (.litInt z)) .int := by
  intro δ W k θ hctx
  unfold exprRel substMap
  intro e' h h' n hext hwsat hn hred
  unfold redNsteps at hred
  obtain ⟨hsteps, hirred⟩ := hred
  cases hsteps with
  | zero =>
    refine ⟨.litV (.litInt z), W, rfl, ⟨[], (List.append_nil W).symm⟩, hwsat, ?_⟩
    unfold valRel; trivial
  | step hstep _ =>
    -- A literal can't take a contextual step
    sorry

theorem compat_var (Γ : TypingContext) (x : String) (A : Ty) :
    get? (M := TyMapStr) Γ x = some A → semTyped Γ (.var x) A := by
  intro hlookup δ W k θ hctx
  -- Get the value from the context relation
  obtain ⟨v, hθ, hv⟩ := hctx x A hlookup
  -- substMap θ (var x) = v.toExpr
  unfold exprRel
  simp only [substMap, hθ]
  -- v.toExpr is already a value, use the same pattern as compat_int
  intro e' h h' n hext hwsat hn hred
  unfold redNsteps at hred
  obtain ⟨hsteps, hirred⟩ := hred
  cases hsteps with
  | zero =>
    refine ⟨v, W, ?_, ⟨[], (List.append_nil W).symm⟩, hwsat, ?_⟩
    · sorry -- need: Expr.toVal? v.toExpr = some v
    · sorry -- need: valRel with (k - 0) = k
  | step hstep _ =>
    sorry -- v.toExpr can't step (same as compat_int)
theorem compat_lam (Γ : TypingContext) (x : String) (e : Expr) (A B : Ty) :
    semTyped (insert (M := TyMapStr) Γ x A) e B → semTyped Γ (.lam (.bNamed x) e) (.fn A B) := by sorry
theorem compat_app (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ (.fn A B) → semTyped Γ e₂ A → semTyped Γ (.app e₁ e₂) B := by sorry
theorem compat_tLam (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e A → semTyped Γ (.tLam e) (.all A) := by sorry
theorem compat_tApp (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.all A) → semTyped Γ (.tApp e) (A.subst1 B) := by sorry
theorem compat_pack (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (A.subst1 B) → semTyped Γ (.pack e) (.exist A) := by sorry
theorem compat_unpack (Γ : TypingContext) (x : String) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ (.exist A) → semTyped (insert (M := TyMapStr) Γ x A) e₂ B →
    semTyped Γ (.unpack (.bNamed x) e₁ e₂) B := by sorry
theorem compat_pair (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ A → semTyped Γ e₂ B → semTyped Γ (.pair e₁ e₂) (.prod A B) := by sorry
theorem compat_fst (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.prod A B) → semTyped Γ (.fst e) A := by sorry
theorem compat_snd (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.prod A B) → semTyped Γ (.snd e) B := by sorry
theorem compat_injL (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e A → semTyped Γ (.injL e) (.sum A B) := by sorry
theorem compat_injR (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e B → semTyped Γ (.injR e) (.sum A B) := by sorry
theorem compat_case (Γ : TypingContext) (e e₁ e₂ : Expr) (A B C : Ty) :
    semTyped Γ e (.sum A B) → semTyped Γ e₁ (.fn A C) → semTyped Γ e₂ (.fn B C) →
    semTyped Γ (.case e e₁ e₂) C := by sorry
theorem compat_roll (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e (A.subst1 (.mu A)) → semTyped Γ (.roll e) (.mu A) := by sorry
theorem compat_unroll (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e (.mu A) → semTyped Γ (.unroll e) (A.subst1 (.mu A)) := by sorry
theorem compat_new (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e A → semTyped Γ (.new e) (.ref A) := by sorry
theorem compat_load (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e (.ref A) → semTyped Γ (.load e) A := by sorry
theorem compat_store (Γ : TypingContext) (e₁ e₂ : Expr) (A : Ty) :
    semTyped Γ e₁ (.ref A) → semTyped Γ e₂ A → semTyped Γ (.store e₁ e₂) .unit := by sorry

-- Fundamental theorem (by induction on typing derivation, applying compatibility lemmas)
theorem sem_soundness {n Γ hctx e A} : SynTyped n Γ hctx e A → semTyped Γ e A := by
  sorry

-- Type safety
theorem type_safety {e e' : Expr} {A : Ty} {n h'} :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) [] e A →
    redNsteps n e Heap.empty e' h' → Expr.isVal e' := by
  intro hty hred
  have hsem := sem_soundness hty
  -- Apply semantic typing with empty context
  unfold semTyped at hsem
  sorry

end SystemFMuState
