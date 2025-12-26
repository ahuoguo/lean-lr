import LeanLr.Lang
import LeanLr.Types
import LeanLr.Operational
import LeanLr.Notation
import LeanLr.ParallelSubst

namespace STLC

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
      semContextRel (Context.insert Γ x A) (Subst.insert x v.toExpr σ)

notation:50 "𝒢⟦" Γ "⟧" σ:50 => semContextRel Γ σ

-- Semantic typing judgment: Γ ⊨ e : τ
def semTyped (Γ : Context) (e : Expr) (τ : Ty) : Prop :=
  Expr.closed Γ.dom e ∧
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
    rfl
  | semContextRel_insert Γ σ v x A hv hrel ih =>
    unfold Context.insert Subst.insert Context.dom Subst.dom
    simp only [List.map_cons]
    congr 1
    unfold Context.dom Subst.dom at ih
    -- Unfold delete to expose filter
    unfold Context.delete Subst.delete
    rw [map_fst_filter, ih]
    rw [← map_fst_filter]

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

-- Helper: if x is in Γ with type A, then it's in the domain
theorem lookup_mem_dom {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A → x ∈ Γ.dom := by
  intro h
  unfold Context.lookup Context.dom at *
  induction Γ with
  | nil => simp at h
  | cons p Γ ih =>
    simp only [List.lookup, List.map_cons, List.mem_cons] at h ⊢
    split at h
    · -- x = p.fst
      rename_i heq
      have : x = p.fst := eq_of_beq heq
      left; exact this
    · -- x ≠ p.fst
      right; exact ih h

-- Helper: weakening for closed expressions
theorem closed_weaken {X Y : List String} {e : Expr} :
    Expr.closed X e → (∀ x, x ∈ X → x ∈ Y) → Expr.closed Y e := by
  intro hclosed hsub
  induction e generalizing X Y with
  | var x =>
    simp [Expr.closed] at hclosed ⊢
    exact hsub x hclosed
  | lam b e ih =>
    simp [Expr.closed] at hclosed ⊢
    apply ih hclosed
    intro z hz
    cases b with
    | anon => exact hsub z hz
    | named y =>
      simp [Binder.cons] at hz ⊢
      cases hz with
      | inl heq => left; exact heq
      | inr hmem => right; exact hsub z hmem
  | app e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩
  | litInt n =>
    simp [Expr.closed]
  | plus e₁ e₂ ih₁ ih₂ =>
    simp [Expr.closed, Bool.and_eq_true] at hclosed ⊢
    exact ⟨ih₁ hclosed.1 hsub, ih₂ hclosed.2 hsub⟩

-- Helper: lookup in deleted subst
theorem lookup_delete_ne {σ : Subst} {x y : String} :
    x ≠ y → (σ.delete y).lookup x = σ.lookup x := by
  intro hne
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    unfold Subst.delete Subst.lookup
    simp only [List.lookup]
    by_cases hp : p.1 = y
    · -- p.1 = y, so p is filtered out
      rw [List.filter_cons_of_neg]
      · cases hbeq : (x == p.1)
        · exact ih
        · -- x = p.1, but p.1 = y and x ≠ y, contradiction
          have : x = p.1 := eq_of_beq hbeq
          subst this
          contradiction
      · simp [hp]
    · -- p.1 ≠ y, so p is kept
      rw [List.filter_cons_of_pos]
      · simp only [List.lookup]
        cases hbeq : (x == p.1)
        · exact ih
        · rfl
      · simp [hp]

-- Helper: lookup in deleted subst
theorem context_lookup_delete_ne {Γ : Context} {x y : String} :
    x ≠ y → (Γ.delete y).lookup x = Γ.lookup x := by
  intro hne
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    unfold Context.delete Context.lookup
    simp only [List.lookup]
    by_cases hp : p.1 = y
    · -- p.1 = y, so p is filtered out
      rw [List.filter_cons_of_neg]
      · cases hbeq : (x == p.1)
        · exact ih
        · -- x = p.1, but p.1 = y and x ≠ y, contradiction
          have : x = p.1 := eq_of_beq hbeq
          subst this
          contradiction
      · simp [hp]
    · -- p.1 ≠ y, so p is kept
      rw [List.filter_cons_of_pos]
      · simp only [List.lookup]
        cases hbeq : (x == p.1)
        · exact ih
        · rfl
      · simp [hp]

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
  intro hctx x e hlookup
  induction hctx with
  | semContextRel_empty =>
    simp [Subst.empty, Subst.lookup] at hlookup
  | semContextRel_insert Γ σ v y A hv _ ih =>
    unfold Subst.insert Subst.lookup at hlookup
    simp only [List.lookup] at hlookup
    split at hlookup
    · -- x = y, so we found the value
      rename_i heq
      have : x = y := eq_of_beq heq
      subst this
      injection hlookup with hlookup
      subst hlookup
      -- v.toExpr is closed
      cases v with
      | litIntV n => simp [Val.toExpr, Expr.closed]
      | lamV b eb =>
        simp [Val.toExpr]
        unfold valRel at hv
        cases A with
        | int => contradiction
        | «fun» A B =>
          simp at hv
          exact hv.1
    · -- x ≠ y, lookup in the tail
      rename_i hne_beq
      have hne : x ≠ y := by
        intro heq
        subst heq
        simp at hne_beq
      have : σ.lookup x = some e := by
        have : (σ.delete y).lookup x = σ.lookup x := lookup_delete_ne hne
        rw [← this]
        exact hlookup
      exact ih this

-- Helper: extract value from semantic context relation
theorem semCtxRelVal {Γ : Context} {σ : Subst} {x : String} {A : Ty} :
    𝒢⟦Γ⟧ σ →
    Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v.toExpr ∧ 𝒱⟦A⟧ v := by
  intro hctx hlookup
  induction hctx with
  | semContextRel_empty =>
    unfold Context.empty Context.lookup at hlookup
    simp at hlookup
  | semContextRel_insert Γ σ v y B hv _ ih =>
    unfold Context.insert Context.lookup at hlookup
    simp only [List.lookup] at hlookup
    by_cases heq : x = y
    · -- x is the freshly inserted variable
      subst heq
      split at hlookup
      · injection hlookup with hlookup
        subst hlookup
        exact ⟨v, by simp [Subst.insert, Subst.lookup], hv⟩
      · -- beq y y = false, contradiction
        rename_i hbeq
        simp at hbeq
    · -- x is in the tail
      split at hlookup
      · rename_i heq'
        have : x = y := eq_of_beq heq'
        contradiction
      · -- x is in the tail: use IH with lookup_of_delete
        have hlookup' := lookup_of_delete heq hlookup
        obtain ⟨w, hw_lookup, hw_val⟩ := ih hlookup'
        exists w
        constructor
        · -- Show: (Subst.insert y v.toExpr σ).lookup x = some w.toExpr
          -- hw_lookup : (Subst.delete y σ).lookup x = some w.toExpr
          unfold Subst.insert Subst.lookup
          simp only [List.lookup]
          cases hbeq : (x == y)
          · -- x ≠ y (beq is false), so List.lookup x (Subst.delete y σ) applies
            -- After insert, we have (y, v.toExpr) :: σ.delete y
            -- List.lookup x of this checks x == y (false), then looks up in σ.delete y
            simp
            rw [← hw_lookup]
            have : (σ.delete y).lookup x = σ.lookup x := lookup_delete_ne ?_
            exact this
            exact not_eq_of_beq_eq_false hbeq
          · -- x = y, contradiction
            have : x = y := eq_of_beq hbeq
            contradiction
        · exact hw_val

-- Compatibility for variables
theorem compat_var {Γ : Context} {x : String} {A : Ty} :
    Γ.lookup x = some A →
    Γ ⊨ Expr.var x : A := by
  intro hlookup
  unfold semTyped
  constructor
  · -- closedness
    simp [Expr.closed]
    exact lookup_mem_dom hlookup
  · -- semantic typing
    intro σ hctx
    -- Extract the value from the semantic context
    obtain ⟨v, hσ, hv⟩ := semCtxRelVal hctx hlookup
    -- Apply substitution to var x
    unfold substMap
    unfold Subst.lookup at hσ
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
    Expr.closed (Context.dom (Context.insert Γ x A)) e →
    𝒢⟦Γ⟧ θ →
    Expr.closed [] (Expr.lam (Binder.named x) (substMap (θ.delete x) e)) := by
  sorry

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
  intro ⟨hcl, hsem⟩
  unfold semTyped
  constructor
  · -- closedness: Expr.closed Γ.dom (Expr.lam (Binder.named x) e)
    simp [Expr.closed, Binder.cons]
    -- hcl : Expr.closed (Context.dom (Context.insert Γ x A)) e
    -- Need: Expr.closed (x :: Γ.dom) e
    apply closed_weaken hcl
    intro y hy
    -- y ∈ Context.dom (Context.insert Γ x A) → y ∈ x :: Γ.dom
    unfold Context.insert Context.dom at hy
    simp only [List.map_cons] at hy
    match hy with
    | .head _ =>
      -- y = x, so y ∈ x :: Γ.dom
      exact List.Mem.head Γ.dom
    | .tail _ hymem =>
      -- hymem : y ∈ (Γ.delete x).map Prod.fst
      -- Need to show: y ∈ x :: Γ.dom
      apply List.Mem.tail x
      -- Now need: y ∈ Γ.dom
      unfold Context.dom
      -- hymem : y ∈ (Γ.filter (fun p => p.1 ≠ x)).map Prod.fst
      -- Use map_fst_filter to rewrite
      suffices y ∈ (Γ.map Prod.fst).filter (· ≠ x) by exact mem_of_mem_filter this
      rw [← map_fst_filter]
      exact hymem
  · -- semantic typing
    intro θ hctx
    unfold exprRel
    -- substMap θ (Expr.lam (Binder.named x) e) = Expr.lam (Binder.named x) (substMap (θ.delete x) e)
    simp [substMap]
    -- Provide witness
    exists Val.lamV (Binder.named x) (substMap (θ.delete x) e)
    constructor
    · -- evaluation: Expr.lam (Binder.named x) (substMap (θ.delete x) e) ⇓ Val.lamV ...
      exact BigStep.lam
    · -- value relation: 𝒱⟦A ⇒ B⟧ (Val.lamV (Binder.named x) (substMap (θ.delete x) e))
      unfold valRel
      constructor
      · -- closedness: Expr.closed ((Binder.named x) :b: []) (substMap (θ.delete x) e)
        -- lamClosed gives: Expr.closed [] (Expr.lam (Binder.named x) (substMap (θ.delete x) e))
        -- which unfolds to: Expr.closed ((Binder.named x) :b: []) (substMap (θ.delete x) e)
        have h := lamClosed Γ θ x A e hcl hctx
        simp [Expr.closed, Binder.cons] at h
        exact h
      · -- ∀ v', 𝒱⟦A⟧ v' → ℰ⟦B⟧ (subst' (Binder.named x) v'.toExpr (substMap (θ.delete x) e))
        intro v' hv'
        -- Unfold subst'
        simp [subst']
        -- Use substitution composition
        have hθ_closed := semContextRel_closed hctx
        rw [subst_substMap_compose hθ_closed]
        -- Apply hsem with extended substitution
        apply hsem
        -- Show 𝒢⟦Γ.insert x A⟧ (Subst.insert x v'.toExpr θ)
        exact semContextRel.semContextRel_insert Γ θ v' x A hv' hctx

-- Compatibility for application
theorem compatApp {Γ : Context} {e₁ e₂ : Expr} {A B : Ty} :
    Γ ⊨ e₁ : (A ⇒ B) →
    Γ ⊨ e₂ : A →
    Γ ⊨ Expr.app e₁ e₂ : B := by
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
