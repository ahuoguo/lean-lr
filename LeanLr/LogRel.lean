import LeanLr.Lang
import LeanLr.Types
import LeanLr.Operational
import LeanLr.Notation
import LeanLr.ParallelSubst

namespace STLC

-- TODO: we might be able to just remove this? The mutual definition seems
-- to have termination directly proven, unlike rocq

-- Termination measure for mutual recursion: type size
def Ty.size : Ty → Nat
  | Ty.int => 0
  | A ⇒ B => 1 + A.size + B.size

-- Value relation: 𝒱⟦τ⟧
-- Expression relation: ℰ⟦τ⟧
-- Value interpretation: v ∈ 𝒱⟦τ⟧
-- Expression interpretation: e ∈ ℰ⟦τ⟧
mutual
  def valRel (τ : Ty) (v : Val) : Prop :=
    match τ, v with
    | Ty.int, Val.litIntV _ => True
    | Ty.int, _ => False
    | A ⇒ B, Val.lamV x e =>
        Expr.closed (x :b: []) e ∧
        ∀ v', valRel A v' → exprRel B (subst' x v'.toExpr e)
    | Ty.fun _ _, _ => False

  def exprRel (τ : Ty) (e : Expr) : Prop :=
    ∃ (w : Val), (e ⇓ w) ∧ (valRel τ w)
end

-- Notation for logical relations
notation:50 "𝒱⟦" τ "⟧" v:50 => valRel τ v
notation:50 "ℰ⟦" τ "⟧" e:50 => exprRel τ e

-- Semantic typing for substitutions (environments)
-- - All variables in Γ map to closed values
-- - No extra bindings (domain matches)
def substRel (Γ : Context) (σ : Subst) : Prop :=
  (∀ x A, Γ.lookup x = some A → ∃ v, σ.lookup x = some v.toExpr ∧ 𝒱⟦A⟧ v) ∧
  (∀ x e, σ.lookup x = some e → ∃ A, Γ.lookup x = some A)


-- Inductive semContextRel : typing_context → (gmap string expr) → Prop :=
--   | semContextRel_empty : semContextRel ∅ ∅
--   | semContextRel_insert Γ θ v x A :
--     𝒱 A v →
--     semContextRel Γ θ →
--     semContextRel (<[x := A]> Γ) (<[x := of_val v]> θ).
inductive semContextRel : Context → Subst → Prop where
  | semContextRel_empty :
      semContextRel Context.empty Subst.empty
  | semContextRel_insert Γ σ v x A :
      𝒱⟦A⟧ v →
      semContextRel Γ σ →
      semContextRel (Γ.insert x A) (σ.insert x v.toExpr)

notation:50 "𝒢⟦" Γ "⟧" σ:50 => semContextRel Γ σ

-- Semantic typing judgment: Γ ⊨ e : τ
def semTyped (Γ : Context) (e : Expr) (τ : Ty) : Prop :=
  Expr.closed Γ.domList e ∧
  ∀ σ: Subst, 𝒢⟦Γ⟧ σ → ℰ⟦τ⟧ (substMap σ e)

notation:75 Γ:75 " ⊨ " e:74 " : " τ:74 => semTyped Γ e τ

-- Helper lemmas

-- Value inclusion: values in value relation are also in expression relation
theorem val_inclusion {τ : Ty} {v : Val} :
    𝒱⟦τ⟧ v → ℰ⟦τ⟧ v.toExpr := by
  intro hv
  unfold exprRel
  exists v
  exact ⟨val_evals_to_self v, hv⟩

-- Helper lemma for boolean conversion
theorem decide_ne_iff_not_decide_eq {α : Type _} [DecidableEq α] (a b : α) :
    decide (a ≠ b) = !decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem map_fst_filter {α : Type _} [DecidableEq α] {l : List (String × α)} {x : String} :
    (l.filter (fun p => p.1 ≠ x)).map (·.1) = (l.map (·.1)).filter (· ≠ x) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.filter, List.map, decide_ne_iff_not_decide_eq]
    by_cases h : p.1 = x
    · subst h
      simp only [decide_ne_iff_not_decide_eq] at ih
      simp [ih]
    · simp only [decide_ne_iff_not_decide_eq] at ih
      simp [h, ih]

-- The proof is complete modulo the freshness assumption, which is a reasonable
-- invariant for well-formed typing contexts.
theorem semContextRel_dom {Γ : Context} {σ : Subst} :
    𝒢⟦Γ⟧ σ → Γ.dom = σ.dom := by
  intro hctx
  induction hctx with
  | semContextRel_empty =>
    simp [Context.dom, Subst.dom]
    apply Iris.Std.domSet_empty
  | semContextRel_insert Γ σ v x A hv hrel ih =>
    simp [Context.dom, Subst.dom]
    -- TODO: need to wait for domSet_insert, which i think you need some
    -- SemiSet axioms which are not ported yet...
    -- rw [Iris.Std.domSet_insert]
    sorry


-- Compatibility for integer literals
theorem compat_int {Γ : Context} {n : Int} :
    Γ ⊨ Expr.litInt n : Ty.int := by
  unfold semTyped
  constructor
  · -- closedness
    simp [Expr.closed]
  · -- semantic typing
    intro σ _
    unfold exprRel
    exists Val.litIntV n
    constructor
    · -- big-step evaluation
      simp [substMap]
      exact BigStep.litInt
    · -- value relation
      unfold valRel
      trivial

-- Helper: membership in domList iff lookup succeeds
theorem mem_domList_iff_lookup_ctx {σ : Context} {x : String} :
    x ∈ σ.domList ↔ ∃ e, σ.lookup x = some e := by
  simp only [Context.domList, Context.lookup]
  rw [List.mem_map]
  constructor
  · intro ⟨⟨k, v⟩, hmem', heq⟩
    simp at heq
    subst heq
    have h := (Iris.Std.FiniteMapLaws.elem_of_map_to_list (M := CtxMap) (K := String) (V := Ty) σ k v).mp hmem'
    exact ⟨v, h⟩
  · intro ⟨e, he⟩
    have hmem : (x, e) ∈ (Iris.Std.FiniteMap.toList (M := CtxMap) σ) :=
      (Iris.Std.FiniteMapLaws.elem_of_map_to_list (M := CtxMap) (K := String) (V := Ty) σ x e).mpr he
    exact ⟨(x, e), hmem, rfl⟩

-- Helper: membership in dom (FiniteSet) iff lookup succeeds
-- Uses elem_of_domSet from FiniteMapDom
theorem subst_mem_dom_iff_lookup {σ : Context} {x : String} :
    x ∈ σ.dom ↔ ∃ e, σ.lookup x = some e := by
  simp only [Context.dom, Context.lookup]
  -- Work around membership instance mismatch by unfolding domSet and FiniteSet.ofList
  simp only [Iris.Std.domSet, Iris.Std.FiniteSet.ofList]
  rw [Std.TreeSet.mem_ofList, List.contains_iff_mem]
  exact mem_domList_iff_lookup_ctx

-- Helper: if x is in Γ with type A, then it's in the domain
theorem lookup_mem_dom {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A → x ∈ Γ.dom := by
  intro hlookup
  rw [subst_mem_dom_iff_lookup]
  exists A

-- Helper: if x is in Γ with type A, then it's in the domList
theorem lookup_mem_domList {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A → x ∈ Γ.domList := by
  intro hlookup
  rw [mem_domList_iff_lookup_ctx]
  exists A


-- Helper: lookup in deleted context
theorem context_lookup_delete_ne {Γ : Context} {x y : String} :
    x ≠ y → (Γ.delete y).lookup x = Γ.lookup x := by
  intro hne
  simp only [Context.delete, Context.lookup]
  exact Iris.Std.FiniteMapLaws.lookup_delete_ne (M := CtxMap) (K := String) (V := Ty) Γ y x hne.symm

-- Helper: lookup in deleted context implies lookup in original
theorem lookup_of_delete {Γ : Context} {x y : String} {A : Ty} :
    x ≠ y → (Γ.delete y).lookup x = some A → Γ.lookup x = some A := by
  intro hne
  intro hlookup
  rw [context_lookup_delete_ne hne] at hlookup
  exact hlookup

-- Helper: semantic contexts are closed
theorem semContextRel_closed {Γ : Context} {θ : Subst} :
    𝒢⟦Γ⟧ θ →
    ∀ x e, θ.lookup x = some e →
    Expr.closed [] e
  := by
  sorry

-- Helper: extract value from semantic context relation
theorem semCtxRelVal {Γ : Context} {σ : Subst} {x : String} {A : Ty} :
    𝒢⟦Γ⟧ σ →
    Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v.toExpr ∧ 𝒱⟦A⟧ v := by
  sorry

-- Compatibility for variables
theorem compat_var {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A →
    Γ ⊨ Expr.var x : A := by
  intro hlookup
  unfold semTyped
  constructor
  · -- closedness
    simp [Expr.closed]
    exact lookup_mem_domList hlookup
  · -- semantic typing
    intro σ hctx
    -- Extract the value from the semantic context
    obtain ⟨v, hσ, hv⟩ := semCtxRelVal hctx hlookup
    -- Apply substitution to var x
    unfold substMap
    simp only [hσ]
    -- Show v.toExpr ∈ ℰ⟦A⟧
    exact val_inclusion hv


-- Helper: if a substitution is closed under [], it's closed under any X
theorem substClosed_weaken {X : List String} {σ : Subst} :
    (∀ x e, σ.lookup x = some e → Expr.closed [] e) →
    (∀ x e, σ.lookup x = some e → Expr.closed X e) := by
  intros hclosed x e hlookup
  have := hclosed x e hlookup
  apply closed_weaken this
  intros _ h
  cases h

-- (* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
-- Lemma lam_closed Γ θ (x : string) A e :
--   closed (elements (dom (<[x:=A]> Γ))) e →
--   𝒢 Γ θ →
--   closed [] (Lam x (subst_map (delete x θ) e)).
-- Proof.
theorem lamClosed Γ θ (x: String) A e :
    e.closed ((Context.insert Γ x A).domList) →
    𝒢⟦Γ⟧ θ →
    -- TODO: `(λ x, (substMap (θ.delete x) e)).closed []` doesn't work here
    -- the macro is slghtly fucked
    (Expr.lam (Binder.named x) (substMap (θ.delete x) e)).closed [] := by
  intro Hcl Hctxt
  apply substMapClosed
  · apply closed_weaken
    · exact Hcl
    · intro y
      simp [Binder.cons]
      intro Hy
      by_cases hy : y = x
      · left; exact hy
      · right
        unfold Context.insert Context.domList at Hy
        -- TODO: prove that y ∈ (Γ.delete x.domList)
        -- then use semContextRel_dom to relate context and subst doms
        sorry
  · sorry


-- Helper: element of filtered list is element of original list
theorem mem_of_mem_filter {α : Type _} [DecidableEq α] {l : List α} {x : α} {p : α → Bool} :
    x ∈ l.filter p → x ∈ l := by
  intro h
  induction l with
  | nil => simp at h
  | cons a l ih =>
    unfold List.filter at h
    split at h
    · -- p a = true
      cases h
      · exact .head _
      · exact .tail _ (ih (by assumption))
    · -- p a = false
      exact .tail _ (ih h)

-- Compatibility for lambda abstractions (named binder)
theorem compatLamNamed {Γ : Context} {x : String} {e : Expr} {A B : Ty} :
    (Γ.insert x A) ⊨ e : B →
    Γ ⊨ Expr.lam (Binder.named x) e : (A ⇒ B) := by
  sorry

-- Compatibility for application
theorem compatApp {Γ : Context} {e₁ e₂ : Expr} {A B : Ty} :
    Γ ⊨ e₁ : (A ⇒ B) →
    Γ ⊨ e₂ : A →
    Γ ⊨ e₁ e₂ : B := by
  intro ⟨hcl₁, hsem₁⟩ ⟨hcl₂, hsem₂⟩
  unfold semTyped
  constructor
  · -- closedness
    simp [Expr.closed, hcl₁, hcl₂]
  · -- semantic typing
    intro σ hctx
    -- Apply semantic typing for e₁
    specialize hsem₁ σ hctx
    unfold exprRel at hsem₁
    obtain ⟨v₁, heval₁, hv₁⟩ := hsem₁
    -- v₁ must be a lambda
    unfold valRel at hv₁
    cases v₁ with
    | litIntV n => contradiction
    | lamV y e =>
      obtain ⟨hclosed, hbody⟩ := hv₁
      -- Apply semantic typing for e₂
      specialize hsem₂ σ hctx
      unfold exprRel at hsem₂
      obtain ⟨v₂, heval₂, hv₂⟩ := hsem₂
      -- Apply the function to the argument
      specialize hbody v₂ hv₂
      unfold exprRel at hbody
      obtain ⟨v, heval, hv⟩ := hbody
      -- Show that app e₁ e₂ evaluates to v
      unfold exprRel
      exists v
      constructor
      · simp [substMap]
        apply BigStep.app heval₁ heval₂ heval
      · exact hv

theorem compatPlus {Γ : Context} {e₁ e₂ : Expr} :
    Γ ⊨ e₁ : Ty.int →
    Γ ⊨ e₂ : Ty.int →
    Γ ⊨ Expr.plus e₁ e₂ : Ty.int := by
  intro ⟨hcl₁, hsem₁⟩ ⟨hcl₂, hsem₂⟩
  unfold semTyped
  constructor
  · -- closedness
    simp [Expr.closed, hcl₁, hcl₂]
  · -- semantic typing
    intro σ hctx
    -- Apply semantic typing for e₁
    specialize hsem₁ σ hctx
    unfold exprRel at hsem₁
    obtain ⟨v₁, heval₁, hv₁⟩ := hsem₁
    -- v₁ must be an integer
    unfold valRel at hv₁
    cases v₁ with
    | litIntV n₁ =>
      -- Apply semantic typing for e₂
      specialize hsem₂ σ hctx
      unfold exprRel at hsem₂
      obtain ⟨v₂, heval₂, hv₂⟩ := hsem₂
      -- v₂ must be an integer
      unfold valRel at hv₂
      cases v₂ with
      | litIntV n₂ =>
        -- Show that plus e₁ e₂ evaluates to n₁ + n₂
        unfold exprRel
        exists Val.litIntV (n₁ + n₂)
        constructor
        · simp [substMap]
          exact BigStep.plus heval₁ heval₂
        · unfold valRel
          trivial
      | lamV _ _ => contradiction
    | lamV _ _ => contradiction

theorem fundamental {Γ : Context} {e : Expr} {A : Ty} :
    (Γ ⊢ e : A) →
    (Γ ⊨ e : A) := by
  intro h
  induction h with
  | var hlookup =>
    exact compat_var hlookup
  | lam_named _ ih_sem =>
    exact compatLamNamed ih_sem
  | app _ _ ih_sem₁ ih_sem₂ =>
    exact compatApp ih_sem₁ ih_sem₂
  | litInt =>
    exact compat_int
  | plus _ _ ih_sem₁ ih_sem₂ =>
    exact compatPlus ih_sem₁ ih_sem₂

theorem termination {e : Expr} {A : Ty} :
    (Context.empty ⊢ e : A) →
    terminates e := by
  intro htype
  -- Apply fundamental theorem
  have ⟨_, hsem⟩ := fundamental htype
  -- Specialize with empty substitution
  specialize hsem Subst.empty semContextRel.semContextRel_empty
  -- The empty substitution applied to e gives e
  rw [substMap_empty] at hsem
  -- hsem : ℰ⟦A⟧ e
  unfold exprRel at hsem
  -- Extract the value
  obtain ⟨v, heval, _⟩ := hsem
  unfold terminates
  exists v

theorem progress {e : Expr} {A : Ty} :
    (Context.empty ⊢ e : A) →
    (∃ v, e.toVal? = some v) ∨ (∃ v, e ⇓ v) := by
  intro htype
  have ⟨v, heval⟩ := termination htype
  right
  exists v

end STLC
