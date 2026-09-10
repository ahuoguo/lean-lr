import LeanLR.TypeSystems.Stlc.Lang
import LeanLR.TypeSystems.Stlc.Notation
import LeanLR.TypeSystems.Stlc.Types
import LeanLR.TypeSystems.Stlc.Operational
import LeanLR.TypeSystems.Stlc.ParallelSubst

/-!
# Syntactic type safety for the STLC

Progress and preservation for the contextual semantics of `Stlc.Operational`, following the
standard recipe: inversion lemmas, weakening, substitutivity, canonical values, progress,
decomposition of a typed `fill K e`, preservation, and finally `typed_safety`.

This is the *syntactic* half of the safety story; `Stlc.LogRel` proves the stronger semantic
statement (termination) for the big-step semantics.
-/

open Iris.Std

namespace STLC

/-! ## Typing contexts

`Std.ExtTreeMap` has no analogue of stdpp's `simplify_map_eq`, so the map facts the proofs below
need are spelled out here. -/

@[simp] theorem Context.lookup_empty (x : String) : Context.empty.lookup x = none :=
  LawfulPartialMap.get?_empty (M := MapStr) x

theorem Context.lookup_insert (Γ : Context) (x : String) (A : Ty) (k : String) :
    (Γ <[ x := A ]>).lookup k = if x = k then some A else Γ.lookup k := by
  simp only [Context.insert, Context.lookup]
  by_cases h : x = k
  · subst h
    rw [if_pos rfl]
    exact LawfulPartialMap.get?_insert_eq (M := MapStr) rfl
  · simp only [if_neg h]
    rw [LawfulPartialMap.get?_insert_ne (M := MapStr) h,
      LawfulPartialMap.get?_delete_ne (M := MapStr) h]

@[simp] theorem Context.lookup_insert_eq (Γ : Context) (x : String) (A : Ty) :
    (Γ <[ x := A ]>).lookup x = some A := by simp [Context.lookup_insert]

theorem Context.lookup_insert_ne {Γ : Context} {x k : String} (A : Ty) (h : x ≠ k) :
    (Γ <[ x := A ]>).lookup k = Γ.lookup k := by simp [Context.lookup_insert, h]

theorem Context.ext {Γ Δ : Context} (h : ∀ x, Γ.lookup x = Δ.lookup x) : Γ = Δ :=
  LawfulPartialMap.equiv_iff_eq.mp h

/-- Inserting twice at the same name keeps only the later type. -/
theorem Context.insert_insert_eq (Γ : Context) (x : String) (A B : Ty) :
    (Γ <[ x := A ]>) <[ x := B ]> = Γ <[ x := B ]> := by
  refine Context.ext fun k => ?_
  by_cases h : x = k <;> simp [Context.lookup_insert, h]

/-- Inserts at distinct names commute. -/
theorem Context.insert_insert_ne (Γ : Context) {x y : String} (A B : Ty) (h : x ≠ y) :
    (Γ <[ x := A ]>) <[ y := B ]> = (Γ <[ y := B ]>) <[ x := A ]> := by
  refine Context.ext fun k => ?_
  by_cases hx : x = k <;> by_cases hy : y = k <;>
    simp_all [Context.lookup_insert]

/-- Context inclusion: `Δ` types everything `Γ` types, at the same type. -/
def Context.Subseteq (Γ Δ : Context) : Prop := ∀ x A, Γ.lookup x = some A → Δ.lookup x = some A

@[inherit_doc] scoped infix:50 " ⊑ " => Context.Subseteq

theorem Context.Subseteq.refl (Γ : Context) : Γ ⊑ Γ := fun _ _ h => h

/-- The empty context is included in every context. -/
theorem Context.empty_subseteq (Γ : Context) : Context.empty ⊑ Γ := by
  intro x A h; simp at h

/-- Inclusion is preserved by extending both sides at the same name. -/
theorem Context.Subseteq.insert {Γ Δ : Context} (h : Γ ⊑ Δ) (x : String) (A : Ty) :
    (Γ <[ x := A ]>) ⊑ (Δ <[ x := A ]>) := by
  intro y B hy
  rw [Context.lookup_insert] at hy ⊢
  by_cases hxy : x = y
  · simpa [hxy] using hy
  · simp only [if_neg hxy] at hy ⊢
    exact h y B hy

/-! ## Inversion lemmas

Deriving these once is cleaner than reaching for `cases` at every use site. -/

theorem var_inversion {Γ : Context} {x : String} {A : Ty} (h : Γ ⊢ Expr.var x : A) :
    Γ.lookup x = some A := by cases h; assumption

theorem lam_inversion {Γ : Context} {x : Binder} {e : Expr} {C : Ty}
    (h : Γ ⊢ Expr.lam x e : C) :
    ∃ A B y, C = (A ⇒ B) ∧ x = Binder.named y ∧ (Γ <[ y := A ]> ⊢ e : B) := by
  cases h with
  | lam_named ht => exact ⟨_, _, _, rfl, rfl, ht⟩

theorem lit_int_inversion {Γ : Context} {n : Int} {A : Ty} (h : Γ ⊢ Expr.litInt n : A) :
    A = Ty.int := by cases h; rfl

theorem app_inversion {Γ : Context} {e₁ e₂ : Expr} {B : Ty} (h : Γ ⊢ Expr.app e₁ e₂ : B) :
    ∃ A, (Γ ⊢ e₁ : (A ⇒ B)) ∧ (Γ ⊢ e₂ : A) := by
  cases h with
  | app ht₁ ht₂ => exact ⟨_, ht₁, ht₂⟩

theorem plus_inversion {Γ : Context} {e₁ e₂ : Expr} {B : Ty} (h : Γ ⊢ Expr.plus e₁ e₂ : B) :
    B = Ty.int ∧ (Γ ⊢ e₁ : Ty.int) ∧ (Γ ⊢ e₂ : Ty.int) := by
  cases h with
  | plus ht₁ ht₂ => exact ⟨rfl, ht₁, ht₂⟩

/-! ## Closedness and weakening -/

/-- A well-typed term only mentions variables its context binds.

The Rocq statement is phrased with `dom Γ ⊆ X`; here the same hypothesis is written directly in
terms of `Context.lookup`, which avoids reasoning about `Context.domList`. -/
theorem syn_typed_closed {Γ : Context} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) :
    ∀ X : List String, (∀ x A', Γ.lookup x = some A' → x ∈ X) → e.closed X = true := by
  induction h with
  | var hlook => intro X hX; simpa [Expr.closed] using hX _ _ hlook
  | @lam_named Γ' x e' A' B' _ ih =>
    intro X hX
    refine ih _ fun y B hy => ?_
    rw [Context.lookup_insert] at hy
    by_cases hxy : x = y
    · simp [Binder.cons, hxy]
    · simp only [if_neg hxy] at hy
      exact List.Mem.tail _ (hX y B hy)
  | app _ _ ih₁ ih₂ =>
    intro X hX; simp [Expr.closed, ih₁ X hX, ih₂ X hX]
  | litInt => intro X _; rfl
  | plus _ _ ih₁ ih₂ =>
    intro X hX; simp [Expr.closed, ih₁ X hX, ih₂ X hX]

/-- Typing is preserved by enlarging the context. -/
theorem typed_weakening {Γ : Context} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) :
    ∀ {Δ : Context}, Γ ⊑ Δ → (Δ ⊢ e : A) := by
  induction h with
  | var hlook => intro Δ hsub; exact .var (hsub _ _ hlook)
  | lam_named _ ih => intro Δ hsub; exact .lam_named (ih (hsub.insert _ _))
  | app _ _ ih₁ ih₂ => intro Δ hsub; exact .app (ih₁ hsub) (ih₂ hsub)
  | litInt => intro Δ _; exact .litInt
  | plus _ _ ih₁ ih₂ => intro Δ hsub; exact .plus (ih₁ hsub) (ih₂ hsub)

/-! ## Substitutivity -/

/-- Substituting a closed term of the right type for a variable preserves typing. -/
theorem typed_substitutivity {e e' : Expr} {Γ : Context} {x : String} {A B : Ty}
    (he' : Context.empty ⊢ e' : A) (h : Γ <[ x := A ]> ⊢ e : B) :
    Γ ⊢ subst x e' e : B := by
  induction e generalizing B Γ with
  | var y =>
    have hp := var_inversion h
    rw [Context.lookup_insert] at hp
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hp
      cases hp
      simpa [subst] using typed_weakening he' (Context.empty_subseteq Γ)
    · simp only [if_neg hxy] at hp
      simpa [subst, hxy] using SynTyped.var hp
  | lam y e ih =>
    obtain ⟨C, D, z, rfl, rfl, hty⟩ := lam_inversion h
    by_cases hxz : Binder.named x = Binder.named z
    · have hxz' : x = z := by simpa using hxz
      subst hxz'
      rw [Context.insert_insert_eq] at hty
      simpa [subst, hxz] using SynTyped.lam_named hty
    · have hxz' : x ≠ z := fun hc => hxz (by simp [hc])
      rw [Context.insert_insert_ne _ _ _ hxz'] at hty
      simpa [subst, hxz] using SynTyped.lam_named (ih hty)
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    exact .app (ih₁ ht₁) (ih₂ ht₂)
  | litInt n => cases lit_int_inversion h; exact .litInt
  | plus e₁ e₂ ih₁ ih₂ =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    exact .plus (ih₁ ht₁) (ih₂ ht₂)

/-! ## Canonical values -/

theorem canonical_values_arr {Γ : Context} {e : Expr} {A B : Ty}
    (h : Γ ⊢ e : (A ⇒ B)) (hv : e.isValue = true) :
    ∃ x e', e = Expr.lam x e' := by
  cases h <;> first | exact ⟨_, _, rfl⟩ | simp [Expr.isValue] at hv

theorem canonical_values_int {Γ : Context} {e : Expr}
    (h : Γ ⊢ e : Ty.int) (hv : e.isValue = true) :
    ∃ n : Int, e = Expr.litInt n := by
  cases h <;> first | exact ⟨_, rfl⟩ | simp [Expr.isValue] at hv

/-! ## Progress -/

/-- A closed well-typed term is either a value or can take a step. -/
theorem typed_progress {e : Expr} {A : Ty} (h : Context.empty ⊢ e : A) :
    e.isValue = true ∨ contextualReducible e := by
  generalize hΓ : (Context.empty : Context) = Γ at h
  induction h with
  | var hlook => subst hΓ; simp at hlook
  | litInt => exact Or.inl rfl
  | lam_named => exact Or.inl rfl
  | @app _ e₁ e₂ A B ht₁ _ ih₁ ih₂ =>
    right
    rcases ih₂ hΓ with h₂ | ⟨e₂', h₂⟩
    · rcases ih₁ hΓ with h₁ | ⟨e₁', h₁⟩
      · obtain ⟨x, e, rfl⟩ := canonical_values_arr (hΓ ▸ ht₁) h₁
        exact ⟨_, base_contextual_step (.betaS h₂ rfl)⟩
      · obtain ⟨v, rfl⟩ := isValue_exists h₂
        exact ⟨_, fill_contextual_step (.appLCtx .holeCtx v) h₁⟩
    · exact ⟨_, fill_contextual_step (.appRCtx e₁ .holeCtx) h₂⟩
  | @plus _ e₁ e₂ ht₁ ht₂ ih₁ ih₂ =>
    right
    rcases ih₂ hΓ with h₂ | ⟨e₂', h₂⟩
    · rcases ih₁ hΓ with h₁ | ⟨e₁', h₁⟩
      · obtain ⟨n₁, rfl⟩ := canonical_values_int (hΓ ▸ ht₁) h₁
        obtain ⟨n₂, rfl⟩ := canonical_values_int (hΓ ▸ ht₂) h₂
        exact ⟨_, base_contextual_step (.plusS rfl rfl rfl)⟩
      · obtain ⟨v, rfl⟩ := isValue_exists h₂
        exact ⟨_, fill_contextual_step (.plusLCtx .holeCtx v) h₁⟩
    · exact ⟨_, fill_contextual_step (.plusRCtx e₁ .holeCtx) h₂⟩

/-! ## Contextual typing -/

/-- `K` turns a hole of type `A` into a term of type `B`. -/
def ectxTyping (K : Ectx) (A B : Ty) : Prop :=
  ∀ e, (Context.empty ⊢ e : A) → (Context.empty ⊢ fill K e : B)

/-- A typed `fill K e` decomposes into a type for the hole and a typing for the context. -/
theorem fill_typing_decompose {K : Ectx} {e : Expr} {A : Ty}
    (h : Context.empty ⊢ fill K e : A) :
    ∃ B, (Context.empty ⊢ e : B) ∧ ectxTyping K B A := by
  induction K generalizing e A with
  | holeCtx => exact ⟨A, h, fun _ ht => ht⟩
  | appLCtx K v₂ ih =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₁
    exact ⟨B, hB, fun e' he' => .app (hK e' he') ht₂⟩
  | appRCtx e₁ K ih =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₂
    exact ⟨B, hB, fun e' he' => .app ht₁ (hK e' he')⟩
  | plusLCtx K v₂ ih =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₁
    exact ⟨B, hB, fun e' he' => .plus (hK e' he') ht₂⟩
  | plusRCtx e₁ K ih =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₂
    exact ⟨B, hB, fun e' he' => .plus ht₁ (hK e' he')⟩

theorem fill_typing_compose {K : Ectx} {e : Expr} {A B : Ty}
    (h : Context.empty ⊢ e : B) (hK : ectxTyping K B A) : Context.empty ⊢ fill K e : A :=
  hK e h

/-! ## Preservation and safety -/

theorem typed_preservation_base_step {e e' : Expr} {A : Ty}
    (h : Context.empty ⊢ e : A) (hstep : BaseStep e e') : Context.empty ⊢ e' : A := by
  cases hstep with
  | @betaS x e₁ e₂ e' hv heq =>
    subst heq
    obtain ⟨B, ht₁, ht₂⟩ := app_inversion h
    obtain ⟨A', B', y, heq, hxy, hty⟩ := lam_inversion ht₁
    injection heq with hA hB
    subst hA; subst hB; subst hxy
    exact typed_substitutivity ht₂ hty
  | plusS =>
    obtain ⟨rfl, _, _⟩ := plus_inversion h
    exact .litInt

theorem typed_preservation {e e' : Expr} {A : Ty}
    (h : Context.empty ⊢ e : A) (hstep : ContextualStep e e') : Context.empty ⊢ e' : A := by
  obtain ⟨K, e₁, e₂, rfl, rfl, hb⟩ := hstep
  obtain ⟨B, hB, hK⟩ := fill_typing_decompose h
  exact fill_typing_compose (typed_preservation_base_step hB hb) hK

/-- A closed well-typed term never gets stuck. -/
theorem typed_safety {e₁ e₂ : Expr} {A : Ty}
    (h : Context.empty ⊢ e₁ : A) (hsteps : ContextualSteps e₁ e₂) :
    e₂.isValue = true ∨ contextualReducible e₂ := by
  induction hsteps with
  | refl => exact typed_progress h
  | step hstep _ ih => exact ih (typed_preservation h hstep)

end STLC
