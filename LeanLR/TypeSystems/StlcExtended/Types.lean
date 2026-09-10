import LeanLR.TypeSystems.StlcExtended.Lang
import LeanLR.TypeSystems.StlcExtended.Maps
import LeanLR.TypeSystems.StlcExtended.CtxStep

/-!
# Extended STLC: syntactic typing and type safety

The typing judgment for products and sums, and progress plus preservation for the contextual
semantics of `CtxStep`.
-/

open Iris.Std

namespace StlcExtended

/-! ## Types and contexts -/

inductive Ty where
  | int
  | fn (A B : Ty)
  | prod (A B : Ty)
  | sum (A B : Ty)
  deriving Repr, DecidableEq

/-- Function type. -/
infixr:70 " ⇒ " => Ty.fn
/-- Product type. -/
infixr:75 " ×ₜ " => Ty.prod
/-- Sum type. -/
infixr:72 " +ₜ " => Ty.sum

/-- Assigns types to the term variables in scope. -/
abbrev TypingContext := MapStr Ty

namespace TypingContext

/-- The context binding nothing. -/
def empty : TypingContext := PartialMap.empty (M := MapStr) (V := Ty)

@[simp] theorem get?_empty (x : String) : get? (M := MapStr) empty x = none :=
  LawfulPartialMap.get?_empty (M := MapStr) x

/-- Context inclusion: `Δ` types everything `Γ` types, at the same type. -/
def Subseteq (Γ Δ : TypingContext) : Prop :=
  ∀ x A, get? (M := MapStr) Γ x = some A → get? (M := MapStr) Δ x = some A

@[inherit_doc] scoped infix:50 " ⊑ " => TypingContext.Subseteq

theorem Subseteq.refl (Γ : TypingContext) : Γ ⊑ Γ := fun _ _ h => h

theorem empty_subseteq (Γ : TypingContext) : empty ⊑ Γ := by intro x A h; simp at h

theorem Subseteq.insert {Γ Δ : TypingContext} (h : Γ ⊑ Δ) (x : String) (A : Ty) :
    insert (M := MapStr) Γ x A ⊑ insert (M := MapStr) Δ x A := by
  intro y B hy
  rw [get?_insert] at hy ⊢
  by_cases hxy : x = y
  · simpa [hxy] using hy
  · simp only [if_neg hxy] at hy ⊢
    exact h y B hy

/-- Inserting twice at the same name keeps only the later type. -/
theorem insert_insert_eq (Γ : TypingContext) (x : String) (A B : Ty) :
    insert (M := MapStr) (insert (M := MapStr) Γ x A) x B = insert (M := MapStr) Γ x B := by
  refine map_ext fun k => ?_
  by_cases h : x = k <;> simp [get?_insert, h]

/-- Inserts at distinct names commute. -/
theorem insert_insert_ne (Γ : TypingContext) {x y : String} (A B : Ty) (h : x ≠ y) :
    insert (M := MapStr) (insert (M := MapStr) Γ x A) y B
      = insert (M := MapStr) (insert (M := MapStr) Γ y B) x A := by
  refine map_ext fun k => ?_
  by_cases hx : x = k <;> by_cases hy : y = k <;> simp_all [get?_insert]

end TypingContext

/-! ## Typing judgment -/

/-- The syntactic typing judgment. -/
inductive SynTyped : TypingContext → Expr → Ty → Prop where
  | typed_var {Γ} (x : String) {A} :
      get? (M := MapStr) Γ x = some A →
      SynTyped Γ (.var x) A
  | typed_lam {Γ} (x : String) {e A B} :
      SynTyped (insert (M := MapStr) Γ x A) e B →
      SynTyped Γ (.lam (.bNamed x) e) (A ⇒ B)
  | typed_lam_anon {Γ e A B} :
      SynTyped Γ e B →
      SynTyped Γ (.lam .bAnon e) (A ⇒ B)
  | typed_int {Γ} (z : Int) :
      SynTyped Γ (.litInt z) .int
  | typed_app {Γ e₁ e₂ A B} :
      SynTyped Γ e₁ (A ⇒ B) →
      SynTyped Γ e₂ A →
      SynTyped Γ (.app e₁ e₂) B
  | typed_add {Γ e₁ e₂} :
      SynTyped Γ e₁ .int →
      SynTyped Γ e₂ .int →
      SynTyped Γ (.plus e₁ e₂) .int
  | typed_pair {Γ e₁ e₂ A B} :
      SynTyped Γ e₁ A →
      SynTyped Γ e₂ B →
      SynTyped Γ (.pair e₁ e₂) (A ×ₜ B)
  | typed_fst {Γ e A B} :
      SynTyped Γ e (A ×ₜ B) →
      SynTyped Γ (.fst e) A
  | typed_snd {Γ e A B} :
      SynTyped Γ e (A ×ₜ B) →
      SynTyped Γ (.snd e) B
  | typed_injl {Γ e A B} :
      SynTyped Γ e A →
      SynTyped Γ (.injL e) (A +ₜ B)
  | typed_injr {Γ e A B} :
      SynTyped Γ e B →
      SynTyped Γ (.injR e) (A +ₜ B)
  | typed_case {Γ e e₁ e₂ A B C} :
      SynTyped Γ e (B +ₜ C) →
      SynTyped Γ e₁ (B ⇒ A) →
      SynTyped Γ e₂ (C ⇒ A) →
      SynTyped Γ (.case e e₁ e₂) A

/-- `Γ ⊢ e : A` is the syntactic typing judgment. -/
notation:74 Γ " ⊢ " e " : " A => SynTyped Γ e A

/-! ## Inversion lemmas -/

theorem var_inversion {Γ : TypingContext} {x : String} {A : Ty} (h : Γ ⊢ .var x : A) :
    get? (M := MapStr) Γ x = some A := by cases h; assumption

theorem lam_inversion {Γ : TypingContext} {x : String} {e : Expr} {C : Ty}
    (h : Γ ⊢ .lam (.bNamed x) e : C) :
    ∃ A B, C = (A ⇒ B) ∧ (insert (M := MapStr) Γ x A ⊢ e : B) := by
  cases h with | typed_lam _ ht => exact ⟨_, _, rfl, ht⟩

theorem lam_anon_inversion {Γ : TypingContext} {e : Expr} {C : Ty}
    (h : Γ ⊢ .lam .bAnon e : C) : ∃ A B, C = (A ⇒ B) ∧ (Γ ⊢ e : B) := by
  cases h with | typed_lam_anon ht => exact ⟨_, _, rfl, ht⟩

theorem lit_int_inversion {Γ : TypingContext} {n : Int} {A : Ty} (h : Γ ⊢ .litInt n : A) :
    A = .int := by cases h; rfl

theorem app_inversion {Γ : TypingContext} {e₁ e₂ : Expr} {B : Ty} (h : Γ ⊢ .app e₁ e₂ : B) :
    ∃ A, (Γ ⊢ e₁ : (A ⇒ B)) ∧ (Γ ⊢ e₂ : A) := by
  cases h with | typed_app ht₁ ht₂ => exact ⟨_, ht₁, ht₂⟩

theorem plus_inversion {Γ : TypingContext} {e₁ e₂ : Expr} {B : Ty} (h : Γ ⊢ .plus e₁ e₂ : B) :
    B = .int ∧ (Γ ⊢ e₁ : .int) ∧ (Γ ⊢ e₂ : .int) := by
  cases h with | typed_add ht₁ ht₂ => exact ⟨rfl, ht₁, ht₂⟩

theorem pair_inversion {Γ : TypingContext} {e₁ e₂ : Expr} {C : Ty} (h : Γ ⊢ .pair e₁ e₂ : C) :
    ∃ A B, C = (A ×ₜ B) ∧ (Γ ⊢ e₁ : A) ∧ (Γ ⊢ e₂ : B) := by
  cases h with | typed_pair ht₁ ht₂ => exact ⟨_, _, rfl, ht₁, ht₂⟩

theorem fst_inversion {Γ : TypingContext} {e : Expr} {A : Ty} (h : Γ ⊢ .fst e : A) :
    ∃ B, Γ ⊢ e : (A ×ₜ B) := by
  cases h with | typed_fst ht => exact ⟨_, ht⟩

theorem snd_inversion {Γ : TypingContext} {e : Expr} {B : Ty} (h : Γ ⊢ .snd e : B) :
    ∃ A, Γ ⊢ e : (A ×ₜ B) := by
  cases h with | typed_snd ht => exact ⟨_, ht⟩

theorem injl_inversion {Γ : TypingContext} {e : Expr} {C : Ty} (h : Γ ⊢ .injL e : C) :
    ∃ A B, C = (A +ₜ B) ∧ (Γ ⊢ e : A) := by
  cases h with | typed_injl ht => exact ⟨_, _, rfl, ht⟩

theorem injr_inversion {Γ : TypingContext} {e : Expr} {C : Ty} (h : Γ ⊢ .injR e : C) :
    ∃ A B, C = (A +ₜ B) ∧ (Γ ⊢ e : B) := by
  cases h with | typed_injr ht => exact ⟨_, _, rfl, ht⟩

theorem case_inversion {Γ : TypingContext} {e e₁ e₂ : Expr} {A : Ty}
    (h : Γ ⊢ .case e e₁ e₂ : A) :
    ∃ B C, (Γ ⊢ e : (B +ₜ C)) ∧ (Γ ⊢ e₁ : (B ⇒ A)) ∧ (Γ ⊢ e₂ : (C ⇒ A)) := by
  cases h with | typed_case ht ht₁ ht₂ => exact ⟨_, _, ht, ht₁, ht₂⟩

/-! ## Closedness and weakening -/

/-- A well-typed term only mentions variables its context binds.

As in `Stlc.TypeSafety`, the Rocq hypothesis `dom Γ ⊆ X` is written directly as a lookup
condition. -/
theorem syn_typed_closed {Γ : TypingContext} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) :
    ∀ X : List String, (∀ x A', get? (M := MapStr) Γ x = some A' → x ∈ X) → closed X e := by
  induction h with
  | typed_var x hlook => intro X hX; simpa [closed, Expr.isClosed] using hX _ _ hlook
  | @typed_lam Γ' x e' A' B' _ ih =>
    intro X hX
    refine ih _ fun y B hy => ?_
    rw [get?_insert] at hy
    by_cases hxy : x = y
    · simp [Binder.cons, hxy]
    · simp only [if_neg hxy] at hy
      exact List.Mem.tail _ (hX y B hy)
  | typed_lam_anon _ ih => intro X hX; exact ih X hX
  | typed_int => intro X _; rfl
  | typed_app _ _ ih₁ ih₂ | typed_add _ _ ih₁ ih₂ | typed_pair _ _ ih₁ ih₂ =>
    intro X hX; simp [closed, Expr.isClosed, ih₁ X hX, ih₂ X hX]
  | typed_fst _ ih | typed_snd _ ih | typed_injl _ ih | typed_injr _ ih =>
    intro X hX; exact ih X hX
  | typed_case _ _ _ ih₀ ih₁ ih₂ =>
    intro X hX; simp [closed, Expr.isClosed, ih₀ X hX, ih₁ X hX, ih₂ X hX]

open TypingContext in
/-- Typing is preserved by enlarging the context. -/
theorem typed_weakening {Γ : TypingContext} {e : Expr} {A : Ty} (h : Γ ⊢ e : A) :
    ∀ {Δ : TypingContext}, Γ ⊑ Δ → (Δ ⊢ e : A) := by
  induction h with
  | typed_var x hlook => intro Δ hsub; exact .typed_var x (hsub _ _ hlook)
  | typed_lam x _ ih => intro Δ hsub; exact .typed_lam x (ih (hsub.insert _ _))
  | typed_lam_anon _ ih => intro Δ hsub; exact .typed_lam_anon (ih hsub)
  | typed_int z => intro Δ _; exact .typed_int z
  | typed_app _ _ ih₁ ih₂ => intro Δ hsub; exact .typed_app (ih₁ hsub) (ih₂ hsub)
  | typed_add _ _ ih₁ ih₂ => intro Δ hsub; exact .typed_add (ih₁ hsub) (ih₂ hsub)
  | typed_pair _ _ ih₁ ih₂ => intro Δ hsub; exact .typed_pair (ih₁ hsub) (ih₂ hsub)
  | typed_fst _ ih => intro Δ hsub; exact .typed_fst (ih hsub)
  | typed_snd _ ih => intro Δ hsub; exact .typed_snd (ih hsub)
  | typed_injl _ ih => intro Δ hsub; exact .typed_injl (ih hsub)
  | typed_injr _ ih => intro Δ hsub; exact .typed_injr (ih hsub)
  | typed_case _ _ _ ih₀ ih₁ ih₂ =>
    intro Δ hsub; exact .typed_case (ih₀ hsub) (ih₁ hsub) (ih₂ hsub)

/-! ## Substitutivity -/

open TypingContext in
theorem typed_substitutivity {e e' : Expr} {Γ : TypingContext} {x : String} {A B : Ty}
    (he' : TypingContext.empty ⊢ e' : A) (h : insert (M := MapStr) Γ x A ⊢ e : B) :
    Γ ⊢ subst x e' e : B := by
  induction e generalizing B Γ with
  | var y =>
    have hp := var_inversion h
    rw [get?_insert] at hp
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hp
      cases hp
      simpa [subst] using typed_weakening he' (empty_subseteq Γ)
    · simp only [if_neg hxy] at hp
      simpa [subst, hxy] using SynTyped.typed_var y hp
  | lam y e ih =>
    cases y with
    | bAnon =>
      obtain ⟨A', C, rfl, hty⟩ := lam_anon_inversion h
      simpa [subst, if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))] using
        SynTyped.typed_lam_anon (A := A') (ih hty)
    | bNamed z =>
      obtain ⟨A', C, rfl, hty⟩ := lam_inversion h
      by_cases hxz : x = z
      · subst hxz
        rw [insert_insert_eq] at hty
        simpa [subst] using SynTyped.typed_lam x hty
      · rw [insert_insert_ne _ _ _ hxz] at hty
        simpa [subst, hxz] using SynTyped.typed_lam z (ih hty)
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    exact .typed_app (ih₁ ht₁) (ih₂ ht₂)
  | litInt n => cases lit_int_inversion h; exact .typed_int n
  | plus e₁ e₂ ih₁ ih₂ =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    exact .typed_add (ih₁ ht₁) (ih₂ ht₂)
  | pair e₁ e₂ ih₁ ih₂ =>
    obtain ⟨C, D, rfl, ht₁, ht₂⟩ := pair_inversion h
    exact .typed_pair (ih₁ ht₁) (ih₂ ht₂)
  | fst e ih => obtain ⟨C, ht⟩ := fst_inversion h; exact .typed_fst (ih ht)
  | snd e ih => obtain ⟨C, ht⟩ := snd_inversion h; exact .typed_snd (ih ht)
  | injL e ih => obtain ⟨C, D, rfl, ht⟩ := injl_inversion h; exact .typed_injl (ih ht)
  | injR e ih => obtain ⟨C, D, rfl, ht⟩ := injr_inversion h; exact .typed_injr (ih ht)
  | case e e₁ e₂ ih₀ ih₁ ih₂ =>
    obtain ⟨C, D, ht, ht₁, ht₂⟩ := case_inversion h
    exact .typed_case (ih₀ ht) (ih₁ ht₁) (ih₂ ht₂)

/-! ## Canonical values -/

theorem canonical_values_arr {Γ : TypingContext} {e : Expr} {A B : Ty}
    (h : Γ ⊢ e : (A ⇒ B)) (hv : e.isVal) : ∃ x e', e = .lam x e' := by
  cases h <;> first | exact ⟨_, _, rfl⟩ | exact hv.elim

theorem canonical_values_int {Γ : TypingContext} {e : Expr}
    (h : Γ ⊢ e : .int) (hv : e.isVal) : ∃ n : Int, e = .litInt n := by
  cases h <;> first | exact ⟨_, rfl⟩ | exact hv.elim

theorem canonical_values_prod {Γ : TypingContext} {e : Expr} {A B : Ty}
    (h : Γ ⊢ e : (A ×ₜ B)) (hv : e.isVal) :
    ∃ e₁ e₂, e = .pair e₁ e₂ ∧ e₁.isVal ∧ e₂.isVal := by
  cases h <;> first | exact ⟨_, _, rfl, hv.1, hv.2⟩ | exact hv.elim

theorem canonical_values_sum {Γ : TypingContext} {e : Expr} {A B : Ty}
    (h : Γ ⊢ e : (A +ₜ B)) (hv : e.isVal) :
    (∃ e', e = .injL e' ∧ e'.isVal) ∨ (∃ e', e = .injR e' ∧ e'.isVal) := by
  cases h with
  | typed_injl _ => exact Or.inl ⟨_, rfl, hv⟩
  | typed_injr _ => exact Or.inr ⟨_, rfl, hv⟩
  | _ => exact hv.elim

/-! ## Progress -/

theorem typed_progress {e : Expr} {A : Ty} (h : TypingContext.empty ⊢ e : A) :
    e.isVal ∨ reducible e := by
  generalize hΓ : (TypingContext.empty : TypingContext) = Γ at h
  induction h with
  | typed_var x hlook => subst hΓ; simp at hlook
  | typed_int => exact Or.inl trivial
  | typed_lam => exact Or.inl trivial
  | typed_lam_anon => exact Or.inl trivial
  | @typed_app _ e₁ e₂ A B ht₁ _ ih₁ ih₂ =>
    right
    rcases ih₂ hΓ with h₂ | ⟨e₂', h₂⟩
    · rcases ih₁ hΓ with h₁ | ⟨e₁', h₁⟩
      · obtain ⟨x, e, rfl⟩ := canonical_values_arr (hΓ ▸ ht₁) h₁
        exact ⟨_, base_contextual_step (.betaS h₂ rfl)⟩
      · exact ⟨_, contextual_step_app_l h₂ h₁⟩
    · exact ⟨_, contextual_step_app_r e₁ h₂⟩
  | @typed_add _ e₁ e₂ ht₁ ht₂ ih₁ ih₂ =>
    right
    rcases ih₂ hΓ with h₂ | ⟨e₂', h₂⟩
    · rcases ih₁ hΓ with h₁ | ⟨e₁', h₁⟩
      · obtain ⟨n₁, rfl⟩ := canonical_values_int (hΓ ▸ ht₁) h₁
        obtain ⟨n₂, rfl⟩ := canonical_values_int (hΓ ▸ ht₂) h₂
        exact ⟨_, base_contextual_step (.plusS rfl rfl rfl)⟩
      · exact ⟨_, contextual_step_plus_l h₂ h₁⟩
    · exact ⟨_, contextual_step_plus_r e₁ h₂⟩
  | @typed_pair _ e₁ e₂ A B _ _ ih₁ ih₂ =>
    rcases ih₂ hΓ with h₂ | ⟨e₂', h₂⟩
    · rcases ih₁ hΓ with h₁ | ⟨e₁', h₁⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨_, contextual_step_pair_l h₂ h₁⟩
    · exact Or.inr ⟨_, contextual_step_pair_r e₁ h₂⟩
  | @typed_fst _ e A B ht ih =>
    right
    rcases ih hΓ with h | ⟨e', h⟩
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod (hΓ ▸ ht) h
      exact ⟨_, base_contextual_step (.fstS hv₁ hv₂)⟩
    · exact ⟨_, contextual_step_fst h⟩
  | @typed_snd _ e A B ht ih =>
    right
    rcases ih hΓ with h | ⟨e', h⟩
    · obtain ⟨e₁, e₂, rfl, hv₁, hv₂⟩ := canonical_values_prod (hΓ ▸ ht) h
      exact ⟨_, base_contextual_step (.sndS hv₁ hv₂)⟩
    · exact ⟨_, contextual_step_snd h⟩
  | typed_injl _ ih =>
    rcases ih hΓ with h | ⟨e', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, contextual_step_injl h⟩
  | typed_injr _ ih =>
    rcases ih hΓ with h | ⟨e', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, contextual_step_injr h⟩
  | @typed_case _ e e₁ e₂ A B C hte _ _ ihe _ _ =>
    right
    rcases ihe hΓ with h | ⟨e', h⟩
    · rcases canonical_values_sum (hΓ ▸ hte) h with ⟨e'', rfl, hv⟩ | ⟨e'', rfl, hv⟩
      · exact ⟨_, base_contextual_step (.caseLS hv)⟩
      · exact ⟨_, base_contextual_step (.caseRS hv)⟩
    · exact ⟨_, contextual_step_case e₁ e₂ h⟩

/-! ## Contextual typing, preservation and safety -/

/-- `K` turns a hole of type `A` into a term of type `B`. -/
def ectxTyping (K : Ectx) (A B : Ty) : Prop :=
  ∀ e, (TypingContext.empty ⊢ e : A) → (TypingContext.empty ⊢ fill K e : B)

theorem fill_typing_decompose {K : Ectx} {e : Expr} {A : Ty}
    (h : TypingContext.empty ⊢ fill K e : A) :
    ∃ B, (TypingContext.empty ⊢ e : B) ∧ ectxTyping K B A := by
  induction K generalizing e A with
  | holeCtx => exact ⟨A, h, fun _ ht => ht⟩
  | appLCtx K v₂ ih =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₁
    exact ⟨B, hB, fun e' he' => .typed_app (hK e' he') ht₂⟩
  | appRCtx e₁ K ih =>
    obtain ⟨C, ht₁, ht₂⟩ := app_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₂
    exact ⟨B, hB, fun e' he' => .typed_app ht₁ (hK e' he')⟩
  | plusLCtx K v₂ ih =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₁
    exact ⟨B, hB, fun e' he' => .typed_add (hK e' he') ht₂⟩
  | plusRCtx e₁ K ih =>
    obtain ⟨rfl, ht₁, ht₂⟩ := plus_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₂
    exact ⟨B, hB, fun e' he' => .typed_add ht₁ (hK e' he')⟩
  | pairLCtx K v₂ ih =>
    obtain ⟨C, D, rfl, ht₁, ht₂⟩ := pair_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₁
    exact ⟨B, hB, fun e' he' => .typed_pair (hK e' he') ht₂⟩
  | pairRCtx e₁ K ih =>
    obtain ⟨C, D, rfl, ht₁, ht₂⟩ := pair_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht₂
    exact ⟨B, hB, fun e' he' => .typed_pair ht₁ (hK e' he')⟩
  | fstCtx K ih =>
    obtain ⟨C, ht⟩ := fst_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht
    exact ⟨B, hB, fun e' he' => .typed_fst (hK e' he')⟩
  | sndCtx K ih =>
    obtain ⟨C, ht⟩ := snd_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht
    exact ⟨B, hB, fun e' he' => .typed_snd (hK e' he')⟩
  | injLCtx K ih =>
    obtain ⟨C, D, rfl, ht⟩ := injl_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht
    exact ⟨B, hB, fun e' he' => .typed_injl (hK e' he')⟩
  | injRCtx K ih =>
    obtain ⟨C, D, rfl, ht⟩ := injr_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht
    exact ⟨B, hB, fun e' he' => .typed_injr (hK e' he')⟩
  | caseCtx K e₁ e₂ ih =>
    obtain ⟨C, D, ht, ht₁, ht₂⟩ := case_inversion h
    obtain ⟨B, hB, hK⟩ := ih ht
    exact ⟨B, hB, fun e' he' => .typed_case (hK e' he') ht₁ ht₂⟩

theorem fill_typing_compose {K : Ectx} {e : Expr} {A B : Ty}
    (h : TypingContext.empty ⊢ e : B) (hK : ectxTyping K B A) :
    TypingContext.empty ⊢ fill K e : A := hK e h

theorem typed_preservation_base_step {e e' : Expr} {A : Ty}
    (h : TypingContext.empty ⊢ e : A) (hstep : BaseStep e e') :
    TypingContext.empty ⊢ e' : A := by
  cases hstep with
  | @betaS x e₁ e₂ _ hv heq =>
    subst heq
    obtain ⟨B, ht₁, ht₂⟩ := app_inversion h
    cases x with
    | bAnon =>
      obtain ⟨C, D, heq, hty⟩ := lam_anon_inversion ht₁
      injection heq with _ hD
      subst hD
      exact hty
    | bNamed y =>
      obtain ⟨C, D, heq, hty⟩ := lam_inversion ht₁
      injection heq with hC hD
      subst hC; subst hD
      exact typed_substitutivity ht₂ hty
  | plusS => obtain ⟨rfl, _, _⟩ := plus_inversion h; exact .typed_int _
  | fstS _ _ =>
    obtain ⟨B, ht⟩ := fst_inversion h
    obtain ⟨C, D, heq, ht₁, _⟩ := pair_inversion ht
    injection heq with hC _
    subst hC
    exact ht₁
  | sndS _ _ =>
    obtain ⟨A', ht⟩ := snd_inversion h
    obtain ⟨C, D, heq, _, ht₂⟩ := pair_inversion ht
    injection heq with _ hD
    subst hD
    exact ht₂
  | caseLS _ =>
    obtain ⟨B, C, ht, ht₁, _⟩ := case_inversion h
    obtain ⟨B', C', heq, ht'⟩ := injl_inversion ht
    injection heq with hB _
    subst hB
    exact .typed_app ht₁ ht'
  | caseRS _ =>
    obtain ⟨B, C, ht, _, ht₂⟩ := case_inversion h
    obtain ⟨B', C', heq, ht'⟩ := injr_inversion ht
    injection heq with _ hC
    subst hC
    exact .typed_app ht₂ ht'

theorem typed_preservation {e e' : Expr} {A : Ty}
    (h : TypingContext.empty ⊢ e : A) (hstep : ContextualStep e e') :
    TypingContext.empty ⊢ e' : A := by
  obtain ⟨K, e₁, e₂, rfl, rfl, hb⟩ := hstep
  obtain ⟨B, hB, hK⟩ := fill_typing_decompose h
  exact fill_typing_compose (typed_preservation_base_step hB hb) hK

/-- A closed well-typed term never gets stuck. -/
theorem type_safety {e₁ e₂ : Expr} {A : Ty}
    (h : TypingContext.empty ⊢ e₁ : A) (hsteps : ContextualSteps e₁ e₂) :
    e₂.isVal ∨ reducible e₂ := by
  induction hsteps with
  | refl => exact typed_progress h
  | step hstep _ ih => exact ih (typed_preservation h hstep)

end StlcExtended
