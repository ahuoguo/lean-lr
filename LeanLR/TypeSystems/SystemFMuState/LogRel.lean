import LeanLR.TypeSystems.SystemFMuState.Lang
import LeanLR.TypeSystems.SystemFMuState.Types
import LeanLR.TypeSystems.SystemFMuState.Execution
import LeanLR.TypeSystems.SystemFMuState.ParallelSubst

/-!
# System F with recursive types and mutable state: logical relation

A unary, step-indexed, world-indexed logical relation for the language, culminating in the
fundamental theorem `sem_soundness` and the type safety theorem `type_safety`.

The step index `k` is what makes the recursive type `mu` well-founded; the world `W` records the
heap invariants that constrain the mutable state. Since only first-order values may be stored, the
world is a plain list of `HeapInv`s and `wsat` stays first-order.
-/

open Iris.Std

namespace SystemFMuState

/-! ## First-order values, heap invariants and worlds -/

/-- The value relation for first-order types. First-order types contain no type variables, so this
is independent of the step index, the world, and the type variable interpretation — which is
exactly what makes the heap tractable. -/
def foValRel : FoTy → Val → Prop
  | .int, .litV (.litInt _) => True
  | .bool, .litV (.litBool _) => True
  | .unit, .litV .litUnit => True
  | .prod a b, .pairV v₁ v₂ => foValRel a v₁ ∧ foValRel b v₂
  | .sum a _, .injLV v => foValRel a v
  | .sum _ b, .injRV v => foValRel b v
  | _, _ => False

/-- A heap invariant governs a single location, asserting that it holds a value of the given
first-order type.

Because `Ty.ref` is confined to first-order types, an invariant only ever has this concrete shape —
"location `l` holds a value of type `a`" — rather than being an arbitrary heap predicate. That is
what keeps `wsat` reasoning first-order. -/
structure HeapInv where
  loc : Loc
  ty : FoTy
  deriving Repr, DecidableEq

/-- A world is the list of heap invariants currently in force. -/
abbrev World := List HeapInv

/-- An arbitrary invariant, so that `World` lookups have a default. -/
instance : Inhabited HeapInv := ⟨⟨⟨0⟩, .unit⟩⟩

/-- `W'` extends `W` when `W` is a *prefix* of `W'`, i.e. `W'` appends new invariants at the end.
Appending rather than consing keeps world indices stable under extension, so the index at which a
reference's invariant sits remains valid in every future world. -/
def worldExt (W W' : World) : Prop := ∃ Wn, W' = W ++ Wn

/-- A semantic type: a step-indexed, world-indexed value predicate closed under the properties the
logical relation needs — it only relates closed values, and it is downward closed in the step index
and upward closed in the world. -/
structure SemType where
  rel : Nat → World → Val → Prop
  closed_val : ∀ k W v, rel k W v → SystemFMuState.closed [] v.toExpr
  mono : ∀ k k' W v, rel k W v → k' ≤ k → rel k' W v
  mono_world : ∀ k W W' v, rel k W v → worldExt W W' → rel k W' v

/-- A heap is bounded when it allocates nothing from some location onwards. Heaps here are total
functions `Loc → Option Val` rather than finite maps, so finiteness has to be stated explicitly.
It is what guarantees `new` can always find a fresh location. -/
def Heap.bounded (h : Heap) : Prop := ∃ n : Int, ∀ l : Loc, n ≤ l.loc → h l = none

/-- The empty heap is bounded. -/
theorem Heap.bounded_empty : Heap.bounded Heap.empty := ⟨0, fun _ _ => rfl⟩

/-- A bounded heap has a free location: the bound itself is one. -/
theorem Heap.bounded_fresh {h : Heap} (hb : Heap.bounded h) : ∃ l, h l = none := by
  obtain ⟨n, hn⟩ := hb
  exact ⟨⟨n⟩, hn ⟨n⟩ (Int.le_refl n)⟩

/-- Writing to a heap keeps it bounded; the bound is pushed past `l` when the write happened at or
above it. -/
theorem Heap.bounded_insert {h : Heap} {l : Loc} {v : Val} (hb : Heap.bounded h) :
    Heap.bounded (Heap.insert h l v) := by
  obtain ⟨n, hn⟩ := hb
  refine ⟨if n ≤ l.loc then l.loc + 1 else n, fun l' hl' => ?_⟩
  have hne : l' ≠ l := by
    intro heq
    subst heq
    split at hl' <;> omega
  have hbound : n ≤ l'.loc := by split at hl' <;> omega
  simp only [Heap.insert, if_neg hne]
  exact hn l' hbound

/-- World satisfaction: the heap is bounded, every invariant recorded in `W` is met by it, and
distinct invariants govern distinct locations.

The explicit disjointness conjunct is what makes a store through one invariant unable to disturb
another: it forces the invariant governing a location to be unique. -/
def wsat (W : World) (h : Heap) : Prop :=
  Heap.bounded h ∧
  (∀ INV ∈ W, ∃ v, h INV.loc = some v ∧ foValRel INV.ty v) ∧
  (∀ INV₁ ∈ W, ∀ INV₂ ∈ W, INV₁.loc = INV₂.loc → INV₁ = INV₂)

/-! ## The logical relation -/

/-- Interprets the type variables in scope, mapping each De Bruijn index to a semantic type. -/
abbrev TyVarInterp := Nat → SemType

/-- A size measure on types. Unrolling a `mu` grows the syntax, so `mu` is charged an extra `2` and
the step index carries the recursion; the remaining constructors decrease this measure, which is
what makes `valRel` well founded. -/
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

/-! ### Termination helpers

`valRel` and `exprRel` recurse on the lexicographic triple `(k, A.size, case_bit)`, where the
`case_bit` distinguishes `valRel` (`0`) from `exprRel` (`1`) so the two can call each other at the
same step index and type. -/

/-- A step that does not raise the index and shrinks the type is a lexicographic decrease. -/
private theorem lex_decr {k₁ k₂ s₁ s₂ c₁ c₂ : Nat} (hk : k₁ ≤ k₂) (hs : s₁ < s₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s₁, c₁) (k₂, s₂, c₂) := by
  obtain hlt | heq := Nat.lt_or_eq_of_le hk
  · exact Prod.Lex.left _ _ hlt
  · subst heq
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hs)

/-- The `exprRel`-to-`valRel` call at the same type: only the case bit decreases. -/
private theorem lex_decr_case {k₁ k₂ s : Nat} (hk : k₁ ≤ k₂) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (k₁, s, 0) (k₂, s, 1) := by
  obtain hlt | heq := Nat.lt_or_eq_of_le hk
  · exact Prod.Lex.left _ _ hlt
  · subst heq
    exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

mutual
  /-- `valRel δ A k W v` says the value `v` belongs to type `A` for `k` more steps in world `W`,
  with type variables interpreted by `δ`.

  The function and universal cases quantify over an arbitrary further index decrement `kd` and an
  arbitrary future world, so they are usable at every later point of the execution. The `mu` case
  spends one step index on each unrolling; at index `0` all that survives is closedness. The `ref`
  case merely records that the world governs the location — the pointee is constrained by `wsat`,
  not here. -/
  def valRel (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) : Prop :=
    match A, k, v with
    | .int, _, .litV (.litInt _) => True
    | .int, _, _ => False
    | .bool, _, .litV (.litBool _) => True
    | .bool, _, _ => False
    | .unit, _, .litV .litUnit => True
    | .unit, _, _ => False
    | .tVar n, k, v => (δ n).rel k W v
    | .prod A B, k, .pairV v₁ v₂ => valRel δ A k W v₁ ∧ valRel δ B k W v₂
    | .prod _ _, _, _ => False
    | .sum A _, k, .injLV v => valRel δ A k W v
    | .sum _ B, k, .injRV v => valRel δ B k W v
    | .sum _ _, _, _ => False
    | .fn A B, k, .lamV x e =>
        SystemFMuState.closed (x :b: []) e ∧
        ∀ v' kd W', worldExt W W' →
          valRel δ A (k - kd) W' v' →
          exprRel δ B (k - kd) W' (subst' x v'.toExpr e)
    | .fn _ _, _, _ => False
    | .all A, k, .tLamV e =>
        SystemFMuState.closed [] e ∧
        ∀ τ : SemType, exprRel (fun n => match n with | 0 => τ | n+1 => δ n) A k W e
    | .all _, _, _ => False
    | .exist A, k, .packV v =>
        ∃ τ : SemType, valRel (fun n => match n with | 0 => τ | n+1 => δ n) A k W v
    | .exist _, _, _ => False
    | .mu _, 0, .rollV v => SystemFMuState.closed [] v.toExpr
    | .mu A, k+1, .rollV v =>
        SystemFMuState.closed [] v.toExpr ∧
        ∀ kd, valRel δ (Ty.subst1 A (.mu A)) (k - kd) W v
    | .mu _, _, _ => False
    | .ref a, _, .litV (.litLoc l) => ⟨l, a⟩ ∈ W
    | .ref _, _, _ => False
  termination_by (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]; omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | exact lex_decr (Nat.sub_le _ _) (by simp [Ty.size]; omega)
      | exact Prod.Lex.left _ _ (by omega)
      | exact lex_decr Nat.le.refl (by simp [Ty.size])

  /-- `exprRel δ A k W e` says every complete reduction of `e` taking fewer than `k` steps from a
  heap satisfying some future world of `W` ends in a value of type `A`, in a further extended world
  the resulting heap satisfies. The remaining budget after `n` steps is `k - n`. -/
  def exprRel (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (e : Expr) : Prop :=
    ∀ e' h h' n W', worldExt W W' → wsat W' h → n < k →
      redNsteps n e h e' h' →
      ∃ v W'', e'.toVal? = some v ∧
        worldExt W' W'' ∧ wsat W'' h' ∧ valRel δ A (k - n) W'' v
  termination_by (k, A.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals exact lex_decr_case (Nat.sub_le _ _)
end

/-- `semCtxRel δ Γ W k θ` says the substitution `θ` provides, for every variable typed by `Γ`, a
closed value in the relation at that type. -/
def semCtxRel (δ : TyVarInterp) (Γ : TypingContext) (W : World) (k : Nat) (θ : SubstMap) : Prop :=
  (∀ x A, get? (M := TyMapStr) Γ x = some A →
    ∃ v, get? (M := MapStr) θ x = some v.toExpr ∧ valRel δ A k W v) ∧
  substIsClosed [] θ

/-- Semantic typing: closing `e` with any substitution satisfying the context puts it in the
expression relation, at every interpretation, world and step index. -/
def semTyped (Γ : TypingContext) (e : Expr) (A : Ty) : Prop :=
  ∀ δ W k θ, semCtxRel δ Γ W k θ → exprRel δ A k W (substMap θ e)

/-! ## World extension -/

/-- World extension is reflexive. -/
theorem worldExt_refl (W : World) : worldExt W W := ⟨[], (List.append_nil W).symm⟩

/-- World extension is transitive. -/
theorem worldExt_trans {W W' W'' : World} : worldExt W W' → worldExt W' W'' → worldExt W W'' := by
  intro ⟨Wn₁, h₁⟩ ⟨Wn₂, h₂⟩
  exact ⟨Wn₁ ++ Wn₂, by rw [h₂, h₁, List.append_assoc]⟩

/-- Extending a world never shortens it. -/
theorem worldExt_length {W W' : World} (h : worldExt W W') : W.length ≤ W'.length := by
  obtain ⟨Wn, heq⟩ := h
  rw [heq, List.length_append]
  omega

/-- Invariants are never dropped by world extension: this is what keeps a reference's typing valid
in all future worlds. -/
theorem worldExt_mem {W W' : World} {INV : HeapInv} (hext : worldExt W W')
    (hmem : INV ∈ W) : INV ∈ W' := by
  obtain ⟨Wn, heq⟩ := hext
  rw [heq]
  exact List.mem_append_left _ hmem

/-! ## Values and reduction -/

/-- Reading a value back off its own expression succeeds. -/
theorem toVal?_toExpr : ∀ (v : Val), v.toExpr.toVal? = some v
  | .litV _ => rfl
  | .lamV _ _ => rfl
  | .tLamV _ => rfl
  | .packV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v, Option.map]
  | .pairV v₁ v₂ => by
    simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v₁, toVal?_toExpr v₂, Option.bind]
  | .injLV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v, Option.map]
  | .injRV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v, Option.map]
  | .rollV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v, Option.map]

/-- A value takes no step in any heap. -/
theorem val_irreducible (v : Val) (h : Heap) : irreducible v.toExpr h := by
  intro ⟨e', h', hstep⟩
  obtain ⟨K, e₁, e₂, hfill, _, hbase⟩ := contextual_step_inv hstep
  have hval : Expr.isVal (fill K e₁) := hfill ▸ val_isVal v
  exact fill_val_base_step_absurd K e₁ e₂ h h' hval hbase

/-- A complete reduction starting from a value takes no steps and changes nothing. -/
theorem nsteps_val_inv (v : Val) (n : Nat) (h : Heap) (e' : Expr) (h' : Heap) :
    redNsteps n v.toExpr h e' h' → n = 0 ∧ e' = v.toExpr ∧ h' = h := by
  intro ⟨hsteps, hirred⟩
  cases hsteps with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | step hstep _ =>
    exfalso
    exact val_irreducible v h ⟨_, _, hstep⟩

/-! ## Monotonicity

The value relation is downward closed in the step index and upward closed in the world. The index
version has to be proved simultaneously with its `exprRel` counterpart, since the two relations call
each other at the function and universal types. -/

mutual
  /-- The value relation is downward closed in the step index. -/
  theorem valRel_mono_idx (δ : TyVarInterp) (A : Ty) (k k' : Nat) (W : World) (v : Val) :
      k' ≤ k → valRel δ A k W v → valRel δ A k' W v := by
    intro hle
    match A, v with
    | .int, .litV (.litInt _) => simp [valRel]
    | .int, .litV (.litBool _) => simp [valRel]
    | .int, .litV .litUnit => simp [valRel]
    | .int, .litV (.litLoc _) => simp [valRel]
    | .int, .lamV _ _ => simp [valRel]
    | .int, .tLamV _ => simp [valRel]
    | .int, .packV _ => simp [valRel]
    | .int, .pairV _ _ => simp [valRel]
    | .int, .injLV _ => simp [valRel]
    | .int, .injRV _ => simp [valRel]
    | .int, .rollV _ => simp [valRel]
    | .bool, .litV (.litBool _) => simp [valRel]
    | .bool, .litV (.litInt _) => simp [valRel]
    | .bool, .litV .litUnit => simp [valRel]
    | .bool, .litV (.litLoc _) => simp [valRel]
    | .bool, .lamV _ _ => simp [valRel]
    | .bool, .tLamV _ => simp [valRel]
    | .bool, .packV _ => simp [valRel]
    | .bool, .pairV _ _ => simp [valRel]
    | .bool, .injLV _ => simp [valRel]
    | .bool, .injRV _ => simp [valRel]
    | .bool, .rollV _ => simp [valRel]
    | .unit, .litV .litUnit => simp [valRel]
    | .unit, .litV (.litInt _) => simp [valRel]
    | .unit, .litV (.litBool _) => simp [valRel]
    | .unit, .litV (.litLoc _) => simp [valRel]
    | .unit, .lamV _ _ => simp [valRel]
    | .unit, .tLamV _ => simp [valRel]
    | .unit, .packV _ => simp [valRel]
    | .unit, .pairV _ _ => simp [valRel]
    | .unit, .injLV _ => simp [valRel]
    | .unit, .injRV _ => simp [valRel]
    | .unit, .rollV _ => simp [valRel]
    | .tVar n, v =>
      simp only [valRel]
      intro hv
      exact (δ n).mono k k' W v hv hle
    | .prod A B, .pairV v₁ v₂ =>
      simp only [valRel]
      intro ⟨h₁, h₂⟩
      exact ⟨valRel_mono_idx δ A k k' W v₁ hle h₁, valRel_mono_idx δ B k k' W v₂ hle h₂⟩
    | .prod _ _, .litV _ => simp [valRel]
    | .prod _ _, .lamV _ _ => simp [valRel]
    | .prod _ _, .tLamV _ => simp [valRel]
    | .prod _ _, .packV _ => simp [valRel]
    | .prod _ _, .injLV _ => simp [valRel]
    | .prod _ _, .injRV _ => simp [valRel]
    | .prod _ _, .rollV _ => simp [valRel]
    | .sum A _, .injLV v =>
      simp only [valRel]
      exact valRel_mono_idx δ A k k' W v hle
    | .sum _ B, .injRV v =>
      simp only [valRel]
      exact valRel_mono_idx δ B k k' W v hle
    | .sum _ _, .litV _ => simp [valRel]
    | .sum _ _, .lamV _ _ => simp [valRel]
    | .sum _ _, .tLamV _ => simp [valRel]
    | .sum _ _, .packV _ => simp [valRel]
    | .sum _ _, .pairV _ _ => simp [valRel]
    | .sum _ _, .rollV _ => simp [valRel]
    | .fn A B, .lamV x e =>
      simp only [valRel]
      intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      -- Spending `kd + (k - k')` of the larger budget leaves exactly `k' - kd`.
      have h : k - (kd + (k - k')) = k' - kd := by omega
      rw [← h] at hv'
      have hexpr := hbody v' (kd + (k - k')) W' hext hv'
      rwa [h] at hexpr
    | .fn _ _, .litV _ => simp [valRel]
    | .fn _ _, .tLamV _ => simp [valRel]
    | .fn _ _, .packV _ => simp [valRel]
    | .fn _ _, .pairV _ _ => simp [valRel]
    | .fn _ _, .injLV _ => simp [valRel]
    | .fn _ _, .injRV _ => simp [valRel]
    | .fn _ _, .rollV _ => simp [valRel]
    | .all A, .tLamV e =>
      simp only [valRel]
      intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ
      exact exprRel_mono_idx (fun n => match n with | 0 => τ | n+1 => δ n) A k k' W e hle (hbody τ)
    | .all _, .litV _ => simp [valRel]
    | .all _, .lamV _ _ => simp [valRel]
    | .all _, .packV _ => simp [valRel]
    | .all _, .pairV _ _ => simp [valRel]
    | .all _, .injLV _ => simp [valRel]
    | .all _, .injRV _ => simp [valRel]
    | .all _, .rollV _ => simp [valRel]
    | .exist A, .packV v =>
      simp only [valRel]
      intro ⟨τ, hτ⟩
      exact ⟨τ, valRel_mono_idx (fun n => match n with | 0 => τ | n+1 => δ n) A k k' W v hle hτ⟩
    | .exist _, .litV _ => simp [valRel]
    | .exist _, .lamV _ _ => simp [valRel]
    | .exist _, .tLamV _ => simp [valRel]
    | .exist _, .pairV _ _ => simp [valRel]
    | .exist _, .injLV _ => simp [valRel]
    | .exist _, .injRV _ => simp [valRel]
    | .exist _, .rollV _ => simp [valRel]
    | .mu A', .rollV v =>
      intro hv
      match k, k', hle, hv with
      | 0, 0, _, hv =>
        simp only [valRel] at *
        exact hv
      | k+1, 0, _, hv =>
        simp only [valRel] at *
        exact hv.1
      | k+1, k''+1, hle, hv =>
        simp only [valRel] at *
        refine ⟨hv.1, ?_⟩
        intro kd
        have hle' : k'' - kd ≤ k - kd := by omega
        exact valRel_mono_idx δ (Ty.subst1 A' (.mu A')) (k - kd) (k'' - kd) W v hle' (hv.2 kd)
    | .mu _, .litV _ => simp [valRel]
    | .mu _, .lamV _ _ => simp [valRel]
    | .mu _, .tLamV _ => simp [valRel]
    | .mu _, .packV _ => simp [valRel]
    | .mu _, .pairV _ _ => simp [valRel]
    | .mu _, .injLV _ => simp [valRel]
    | .mu _, .injRV _ => simp [valRel]
    | .ref _, .litV (.litLoc _) =>
      simp only [valRel]
      exact id
    | .ref _, .litV (.litInt _) => simp [valRel]
    | .ref _, .litV (.litBool _) => simp [valRel]
    | .ref _, .litV .litUnit => simp [valRel]
    | .ref _, .lamV _ _ => simp [valRel]
    | .ref _, .tLamV _ => simp [valRel]
    | .ref _, .packV _ => simp [valRel]
    | .ref _, .pairV _ _ => simp [valRel]
    | .ref _, .injLV _ => simp [valRel]
    | .ref _, .injRV _ => simp [valRel]
    | .ref _, .rollV _ => simp [valRel]
  termination_by (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]; omega))
      | exact Prod.Lex.left _ _ (by omega)
      | exact lex_decr (Nat.sub_le _ _) (by simp [Ty.size]; omega)
      | exact lex_decr Nat.le.refl (by simp [Ty.size]; omega)
      | exact lex_decr_case (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]))

  /-- The expression relation is downward closed in the step index. -/
  theorem exprRel_mono_idx (δ : TyVarInterp) (A : Ty) (k k' : Nat) (W : World) (e : Expr) :
      k' ≤ k → exprRel δ A k W e → exprRel δ A k' W e := by
    intro hk hexpr
    unfold exprRel at *
    intro e' h h' n W' hext hwsat hn hred
    have hn' : n < k := Nat.lt_of_lt_of_le hn hk
    obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := hexpr e' h h' n W' hext hwsat hn' hred
    exact ⟨v, W'', hval, hext', hwsat', valRel_mono_idx δ A (k - n) (k' - n) W'' v (by omega) hv⟩
  termination_by (k, A.size, 1)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact lex_decr_case (Nat.sub_le _ _)
      | exact lex_decr_case (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

  /-- The value relation is preserved by world extension. -/
  theorem valRel_mono_world (δ : TyVarInterp) (A : Ty) (k : Nat) (W W' : World) (v : Val) :
      worldExt W W' → valRel δ A k W v → valRel δ A k W' v := by
    intro hext
    match A, v with
    | .int, .litV (.litInt _) => simp [valRel]
    | .int, .litV (.litBool _) => simp [valRel]
    | .int, .litV .litUnit => simp [valRel]
    | .int, .litV (.litLoc _) => simp [valRel]
    | .int, .lamV _ _ => simp [valRel]
    | .int, .tLamV _ => simp [valRel]
    | .int, .packV _ => simp [valRel]
    | .int, .pairV _ _ => simp [valRel]
    | .int, .injLV _ => simp [valRel]
    | .int, .injRV _ => simp [valRel]
    | .int, .rollV _ => simp [valRel]
    | .bool, .litV (.litBool _) => simp [valRel]
    | .bool, .litV (.litInt _) => simp [valRel]
    | .bool, .litV .litUnit => simp [valRel]
    | .bool, .litV (.litLoc _) => simp [valRel]
    | .bool, .lamV _ _ => simp [valRel]
    | .bool, .tLamV _ => simp [valRel]
    | .bool, .packV _ => simp [valRel]
    | .bool, .pairV _ _ => simp [valRel]
    | .bool, .injLV _ => simp [valRel]
    | .bool, .injRV _ => simp [valRel]
    | .bool, .rollV _ => simp [valRel]
    | .unit, .litV .litUnit => simp [valRel]
    | .unit, .litV (.litInt _) => simp [valRel]
    | .unit, .litV (.litBool _) => simp [valRel]
    | .unit, .litV (.litLoc _) => simp [valRel]
    | .unit, .lamV _ _ => simp [valRel]
    | .unit, .tLamV _ => simp [valRel]
    | .unit, .packV _ => simp [valRel]
    | .unit, .pairV _ _ => simp [valRel]
    | .unit, .injLV _ => simp [valRel]
    | .unit, .injRV _ => simp [valRel]
    | .unit, .rollV _ => simp [valRel]
    | .tVar n, v =>
      simp only [valRel]
      intro hv
      exact (δ n).mono_world k W W' v hv hext
    | .prod A B, .pairV v₁ v₂ =>
      simp only [valRel]
      intro ⟨h₁, h₂⟩
      exact ⟨valRel_mono_world δ A k W W' v₁ hext h₁, valRel_mono_world δ B k W W' v₂ hext h₂⟩
    | .prod _ _, .litV _ => simp [valRel]
    | .prod _ _, .lamV _ _ => simp [valRel]
    | .prod _ _, .tLamV _ => simp [valRel]
    | .prod _ _, .packV _ => simp [valRel]
    | .prod _ _, .injLV _ => simp [valRel]
    | .prod _ _, .injRV _ => simp [valRel]
    | .prod _ _, .rollV _ => simp [valRel]
    | .sum A _, .injLV v =>
      simp only [valRel]
      exact valRel_mono_world δ A k W W' v hext
    | .sum _ B, .injRV v =>
      simp only [valRel]
      exact valRel_mono_world δ B k W W' v hext
    | .sum _ _, .litV _ => simp [valRel]
    | .sum _ _, .lamV _ _ => simp [valRel]
    | .sum _ _, .tLamV _ => simp [valRel]
    | .sum _ _, .packV _ => simp [valRel]
    | .sum _ _, .pairV _ _ => simp [valRel]
    | .sum _ _, .rollV _ => simp [valRel]
    | .fn A B, .lamV x e =>
      simp only [valRel]
      intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W'' hext' hv'
      exact hbody v' kd W'' (worldExt_trans hext hext') hv'
    | .fn _ _, .litV _ => simp [valRel]
    | .fn _ _, .tLamV _ => simp [valRel]
    | .fn _ _, .packV _ => simp [valRel]
    | .fn _ _, .pairV _ _ => simp [valRel]
    | .fn _ _, .injLV _ => simp [valRel]
    | .fn _ _, .injRV _ => simp [valRel]
    | .fn _ _, .rollV _ => simp [valRel]
    | .all A, .tLamV e =>
      simp only [valRel]
      intro ⟨hcl, hbody⟩
      refine ⟨hcl, fun τ => ?_⟩
      -- `exprRel_mono_world` is only in scope after this block, so unfold `exprRel` by hand.
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      exact hbody τ e' h h' n W'' (worldExt_trans hext hext') hwsat hn hred
    | .all _, .litV _ => simp [valRel]
    | .all _, .lamV _ _ => simp [valRel]
    | .all _, .packV _ => simp [valRel]
    | .all _, .pairV _ _ => simp [valRel]
    | .all _, .injLV _ => simp [valRel]
    | .all _, .injRV _ => simp [valRel]
    | .all _, .rollV _ => simp [valRel]
    | .exist A, .packV v =>
      simp only [valRel]
      intro ⟨τ, hτ⟩
      exact ⟨τ, valRel_mono_world (fun n => match n with | 0 => τ | n+1 => δ n) A k W W' v hext hτ⟩
    | .exist _, .litV _ => simp [valRel]
    | .exist _, .lamV _ _ => simp [valRel]
    | .exist _, .tLamV _ => simp [valRel]
    | .exist _, .pairV _ _ => simp [valRel]
    | .exist _, .injLV _ => simp [valRel]
    | .exist _, .injRV _ => simp [valRel]
    | .exist _, .rollV _ => simp [valRel]
    | .mu A', .rollV v =>
      match k with
      | 0 =>
        simp only [valRel]
        exact id
      | k+1 =>
        simp only [valRel]
        intro ⟨hcl, hbody⟩
        refine ⟨hcl, ?_⟩
        intro kd
        exact valRel_mono_world δ (Ty.subst1 A' (.mu A')) (k - kd) W W' v hext (hbody kd)
    | .mu _, .litV _ => simp [valRel]
    | .mu _, .lamV _ _ => simp [valRel]
    | .mu _, .tLamV _ => simp [valRel]
    | .mu _, .packV _ => simp [valRel]
    | .mu _, .pairV _ _ => simp [valRel]
    | .mu _, .injLV _ => simp [valRel]
    | .mu _, .injRV _ => simp [valRel]
    | .ref _, .litV (.litLoc _) =>
      simp only [valRel]
      exact worldExt_mem hext
    | .ref _, .litV (.litInt _) => simp [valRel]
    | .ref _, .litV (.litBool _) => simp [valRel]
    | .ref _, .litV .litUnit => simp [valRel]
    | .ref _, .lamV _ _ => simp [valRel]
    | .ref _, .tLamV _ => simp [valRel]
    | .ref _, .packV _ => simp [valRel]
    | .ref _, .pairV _ _ => simp [valRel]
    | .ref _, .injLV _ => simp [valRel]
    | .ref _, .injRV _ => simp [valRel]
    | .ref _, .rollV _ => simp [valRel]
  termination_by (k, A.size, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]; omega))
      | exact Prod.Lex.left _ _ (by omega)
      | exact lex_decr (Nat.sub_le _ _) (by simp [Ty.size]; omega)
      | exact lex_decr Nat.le.refl (by simp [Ty.size]; omega)
      | exact lex_decr_case (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]))
end

/-- The expression relation is preserved by world extension. Unlike its value counterpart this needs
no recursion: `exprRel` only quantifies over future worlds, and `worldExt` is transitive. -/
theorem exprRel_mono_world (δ : TyVarInterp) (A : Ty) (k : Nat) (W W' : World) (e : Expr) :
    worldExt W W' → exprRel δ A k W e → exprRel δ A k W' e := by
  intro hext hexpr
  unfold exprRel at *
  intro e' h h' n W'' hext' hwsat hn hred
  exact hexpr e' h h' n W'' (worldExt_trans hext hext') hwsat hn hred

/-- Related values are closed terms. -/
theorem valRel_closed (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) :
    valRel δ A k W v → closed [] v.toExpr := by
  match A, v with
  | .int, .litV (.litInt _) => simp [valRel, closed, Val.toExpr, Expr.isClosed]
  | .int, .litV (.litBool _) => simp [valRel]
  | .int, .litV .litUnit => simp [valRel]
  | .int, .litV (.litLoc _) => simp [valRel]
  | .int, .lamV _ _ => simp [valRel]
  | .int, .tLamV _ => simp [valRel]
  | .int, .packV _ => simp [valRel]
  | .int, .pairV _ _ => simp [valRel]
  | .int, .injLV _ => simp [valRel]
  | .int, .injRV _ => simp [valRel]
  | .int, .rollV _ => simp [valRel]
  | .bool, .litV (.litBool _) => simp [valRel, closed, Val.toExpr, Expr.isClosed]
  | .bool, .litV (.litInt _) => simp [valRel]
  | .bool, .litV .litUnit => simp [valRel]
  | .bool, .litV (.litLoc _) => simp [valRel]
  | .bool, .lamV _ _ => simp [valRel]
  | .bool, .tLamV _ => simp [valRel]
  | .bool, .packV _ => simp [valRel]
  | .bool, .pairV _ _ => simp [valRel]
  | .bool, .injLV _ => simp [valRel]
  | .bool, .injRV _ => simp [valRel]
  | .bool, .rollV _ => simp [valRel]
  | .unit, .litV .litUnit => simp [valRel, closed, Val.toExpr, Expr.isClosed]
  | .unit, .litV (.litInt _) => simp [valRel]
  | .unit, .litV (.litBool _) => simp [valRel]
  | .unit, .litV (.litLoc _) => simp [valRel]
  | .unit, .lamV _ _ => simp [valRel]
  | .unit, .tLamV _ => simp [valRel]
  | .unit, .packV _ => simp [valRel]
  | .unit, .pairV _ _ => simp [valRel]
  | .unit, .injLV _ => simp [valRel]
  | .unit, .injRV _ => simp [valRel]
  | .unit, .rollV _ => simp [valRel]
  | .tVar n, v =>
    simp only [valRel]
    intro hv
    exact (δ n).closed_val k W v hv
  | .prod A B, .pairV v₁ v₂ =>
    simp only [valRel]
    intro ⟨h₁, h₂⟩
    show closed [] (.pair v₁.toExpr v₂.toExpr)
    simp only [closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨valRel_closed δ A k W v₁ h₁, valRel_closed δ B k W v₂ h₂⟩
  | .prod _ _, .litV _ => simp [valRel]
  | .prod _ _, .lamV _ _ => simp [valRel]
  | .prod _ _, .tLamV _ => simp [valRel]
  | .prod _ _, .packV _ => simp [valRel]
  | .prod _ _, .injLV _ => simp [valRel]
  | .prod _ _, .injRV _ => simp [valRel]
  | .prod _ _, .rollV _ => simp [valRel]
  | .sum A _, .injLV v =>
    simp only [valRel]
    intro hv
    show closed [] (.injL v.toExpr)
    simp only [closed, Expr.isClosed]
    exact valRel_closed δ A k W v hv
  | .sum _ B, .injRV v =>
    simp only [valRel]
    intro hv
    show closed [] (.injR v.toExpr)
    simp only [closed, Expr.isClosed]
    exact valRel_closed δ B k W v hv
  | .sum _ _, .litV _ => simp [valRel]
  | .sum _ _, .lamV _ _ => simp [valRel]
  | .sum _ _, .tLamV _ => simp [valRel]
  | .sum _ _, .packV _ => simp [valRel]
  | .sum _ _, .pairV _ _ => simp [valRel]
  | .sum _ _, .rollV _ => simp [valRel]
  | .fn A B, .lamV x e =>
    simp only [valRel]
    intro ⟨hcl, _⟩
    show closed [] (.lam x e)
    simp only [closed, Expr.isClosed]
    exact hcl
  | .fn _ _, .litV _ => simp [valRel]
  | .fn _ _, .tLamV _ => simp [valRel]
  | .fn _ _, .packV _ => simp [valRel]
  | .fn _ _, .pairV _ _ => simp [valRel]
  | .fn _ _, .injLV _ => simp [valRel]
  | .fn _ _, .injRV _ => simp [valRel]
  | .fn _ _, .rollV _ => simp [valRel]
  | .all A, .tLamV e =>
    simp only [valRel]
    intro ⟨hcl, _⟩
    show closed [] (.tLam e)
    simp only [closed, Expr.isClosed]
    exact hcl
  | .all _, .litV _ => simp [valRel]
  | .all _, .lamV _ _ => simp [valRel]
  | .all _, .packV _ => simp [valRel]
  | .all _, .pairV _ _ => simp [valRel]
  | .all _, .injLV _ => simp [valRel]
  | .all _, .injRV _ => simp [valRel]
  | .all _, .rollV _ => simp [valRel]
  | .exist A, .packV v =>
    simp only [valRel]
    intro ⟨τ, hτ⟩
    show closed [] (.pack v.toExpr)
    simp only [closed, Expr.isClosed]
    exact valRel_closed (fun n => match n with | 0 => τ | n+1 => δ n) A k W v hτ
  | .exist _, .litV _ => simp [valRel]
  | .exist _, .lamV _ _ => simp [valRel]
  | .exist _, .tLamV _ => simp [valRel]
  | .exist _, .pairV _ _ => simp [valRel]
  | .exist _, .injLV _ => simp [valRel]
  | .exist _, .injRV _ => simp [valRel]
  | .exist _, .rollV _ => simp [valRel]
  | .mu _, .rollV v =>
    intro hv
    show closed [] (.roll v.toExpr)
    simp only [closed, Expr.isClosed]
    match k with
    | 0 =>
      simp only [valRel] at hv
      exact hv
    | k+1 =>
      simp only [valRel] at hv
      exact hv.1
  | .mu _, .litV _ => simp [valRel]
  | .mu _, .lamV _ _ => simp [valRel]
  | .mu _, .tLamV _ => simp [valRel]
  | .mu _, .packV _ => simp [valRel]
  | .mu _, .pairV _ _ => simp [valRel]
  | .mu _, .injLV _ => simp [valRel]
  | .mu _, .injRV _ => simp [valRel]
  | .ref _, .litV (.litLoc _) => simp [valRel, closed, Val.toExpr, Expr.isClosed]
  | .ref _, .litV (.litInt _) => simp [valRel]
  | .ref _, .litV (.litBool _) => simp [valRel]
  | .ref _, .litV .litUnit => simp [valRel]
  | .ref _, .lamV _ _ => simp [valRel]
  | .ref _, .tLamV _ => simp [valRel]
  | .ref _, .packV _ => simp [valRel]
  | .ref _, .pairV _ _ => simp [valRel]
  | .ref _, .injLV _ => simp [valRel]
  | .ref _, .injRV _ => simp [valRel]
  | .ref _, .rollV _ => simp [valRel]
termination_by (k, A.size, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]; omega))
    | exact Prod.Lex.left _ _ (by omega)
    | exact lex_decr (Nat.sub_le _ _) (by simp [Ty.size]; omega)
    | exact lex_decr Nat.le.refl (by simp [Ty.size]; omega)
    | exact lex_decr_case (by omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp [Ty.size]))

/-- Combined monotonicity for the value relation: down in the index, up in the world. -/
theorem valRel_mono (δ : TyVarInterp) (A : Ty) (k k' : Nat) (W W' : World) (v : Val) :
    k' ≤ k → worldExt W W' → valRel δ A k W v → valRel δ A k' W' v :=
  fun hk hw hv => valRel_mono_world δ A k' W W' v hw (valRel_mono_idx δ A k k' W v hk hv)

/-- Combined monotonicity for the expression relation: down in the index, up in the world. -/
theorem exprRel_mono (δ : TyVarInterp) (A : Ty) (k k' : Nat) (W W' : World) (e : Expr) :
    k' ≤ k → worldExt W W' → exprRel δ A k W e → exprRel δ A k' W' e :=
  fun hk hw he => exprRel_mono_idx δ A k k' W' e hk (exprRel_mono_world δ A k W W' e hw he)

/-- Value inclusion: a related value is a related expression. It reduces in zero steps, so the whole
step budget survives. -/
theorem sem_val_expr_rel (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) :
    valRel δ A k W v → exprRel δ A k W v.toExpr := by
  intro hv
  unfold exprRel
  intro e' h h' n W' hext hwsat hn hred
  obtain ⟨rfl, rfl, rfl⟩ := nsteps_val_inv v n h e' h' hred
  refine ⟨v, W', toVal?_toExpr v, worldExt_refl W', hwsat, ?_⟩
  rw [Nat.sub_zero]
  exact valRel_mono_world δ A k W W' v hext hv

/-- The expression relation is vacuous at index `0`: no reduction can take fewer than zero steps. -/
theorem expr_rel_zero (δ : TyVarInterp) (A : Ty) (W : World) (e : Expr) :
    exprRel δ A 0 W e := by
  unfold exprRel
  intro e' h h' n W' _ _ hn _
  exact absurd hn (Nat.not_lt_zero n)

/-- The expression relation is closed under taking a deterministic step backwards; the step costs
one unit of the budget. -/
theorem expr_det_step_closure (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (e e' : Expr) :
    DetStep e e' → exprRel δ A (k - 1) W e' → exprRel δ A k W e := by
  intro hdet hexpr
  unfold exprRel
  intro e'' h h' n W' hext hwsat hn hred
  unfold exprRel at hexpr
  obtain ⟨hle, hred'⟩ := det_step_red hdet hred
  have hn' : n - 1 < k - 1 := by omega
  obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := hexpr e'' h h' (n - 1) W' hext hwsat hn' hred'
  refine ⟨v, W'', hval, hext', hwsat', ?_⟩
  have heq : k - n = k - 1 - (n - 1) := by omega
  rwa [heq]

/-! ## Bind lemma

Reduction of `fillItem Ki e` splits into the reduction of `e` to a value followed by the reduction
of the frame applied to that value. `bind_item` turns that split into a compositionality principle
for `exprRel`. -/

/-- A contextual step lifts through a single evaluation frame. -/
theorem fillItem_contextual_step {Ki : EctxItem} {e₁ e₂ : Expr} {h₁ h₂ : Heap} :
    ContextualStep (e₁, h₁) (e₂, h₂) →
    ContextualStep (fillItem Ki e₁, h₁) (fillItem Ki e₂, h₂) := by
  intro hstep
  have heq₁ : fillItem Ki e₁ = fill [Ki] e₁ := by simp [fill, List.foldl]
  have heq₂ : fillItem Ki e₂ = fill [Ki] e₂ := by simp [fill, List.foldl]
  rw [heq₁, heq₂]
  exact fill_contextual_step hstep

/-- Reducibility lifts through a single evaluation frame. -/
theorem fillItem_reducible {Ki : EctxItem} {e : Expr} {h : Heap} :
    reducible e h → reducible (fillItem Ki e) h := by
  intro ⟨e', h', hstep⟩
  exact ⟨fillItem Ki e', h', fillItem_contextual_step hstep⟩

/-- If a framed expression is stuck then so is the expression in the hole. -/
theorem fillItem_irreducible {Ki : EctxItem} {e : Expr} {h : Heap} :
    irreducible (fillItem Ki e) h → irreducible e h :=
  fun hirr hred => hirr (fillItem_reducible hred)

/-- A frame around a non-value is never itself a redex: every redex shape demands a value in the
position the frame leaves open. -/
private theorem base_step_fillItem_absurd (Ki : EctxItem) (e e₂ : Expr) (h h' : Heap)
    (hnval : ¬ Expr.isVal e) (hbase : BaseStep (fillItem Ki e, h) (e₂, h')) : False := by
  cases Ki with
  | appLCtx v =>
    simp [fillItem] at hbase
    cases hbase with
    | betaS x _ _ _ hval => exact hnval (by simp [Expr.isVal])
  | appRCtx f =>
    simp [fillItem] at hbase
    cases hbase with
    | betaS _ _ _ _ hval => exact hnval hval
  | unOpCtx op =>
    simp [fillItem] at hbase
    cases hbase with
    | unOpS _ _ v _ _ htv _ =>
      exact hnval (toVal?_isVal htv)
  | binOpLCtx op v =>
    simp [fillItem] at hbase
    cases hbase with
    | binOpS _ _ _ v₁ _ _ _ htv₁ _ _ =>
      exact hnval (toVal?_isVal htv₁)
  | binOpRCtx op f =>
    simp [fillItem] at hbase
    cases hbase with
    | binOpS _ _ _ _ v₂ _ _ _ htv₂ _ =>
      exact hnval (toVal?_isVal htv₂)
  | ifCtx e₁ e₂' =>
    simp [fillItem] at hbase
    cases hbase with
    | ifTrueS _ _ _ => exact hnval (by simp [Expr.isVal])
    | ifFalseS _ _ _ => exact hnval (by simp [Expr.isVal])
  | tAppCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | tBetaS _ _ => exact hnval (by simp [Expr.isVal])
  | packCtx =>
    simp [fillItem] at hbase
    cases hbase
  | unpackCtx x e₂' =>
    simp [fillItem] at hbase
    cases hbase with
    | unpackS _ e₁ _ _ hval₁ =>
      exact hnval (by simp [Expr.isVal]; exact hval₁)
  | pairLCtx v =>
    simp [fillItem] at hbase
    cases hbase
  | pairRCtx f =>
    simp [fillItem] at hbase
    cases hbase
  | fstCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | fstS e₁ e₂' _ hv₁ hv₂ =>
      exact hnval (by simp [Expr.isVal]; exact ⟨hv₁, hv₂⟩)
  | sndCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | sndS e₁ e₂' _ hv₁ hv₂ =>
      exact hnval (by simp [Expr.isVal]; exact ⟨hv₁, hv₂⟩)
  | injLCtx =>
    simp [fillItem] at hbase
    cases hbase
  | injRCtx =>
    simp [fillItem] at hbase
    cases hbase
  | caseCtx e₁ e₂' =>
    simp [fillItem] at hbase
    cases hbase with
    | caseLS ev _ _ _ hval => exact hnval (by simp [Expr.isVal]; exact hval)
    | caseRS ev _ _ _ hval => exact hnval (by simp [Expr.isVal]; exact hval)
  | rollCtx =>
    simp [fillItem] at hbase
    cases hbase
  | unrollCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | unrollS ev _ hval => exact hnval (by simp [Expr.isVal]; exact hval)
  | loadCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | loadS _ _ _ _ => exact hnval (by simp [Expr.isVal])
  | storeLCtx v =>
    simp [fillItem] at hbase
    cases hbase with
    | storeS _ _ _ _ _ _ => exact hnval (by simp [Expr.isVal])
  | storeRCtx f =>
    simp [fillItem] at hbase
    cases hbase with
    | storeS _ v' _ _ _ htv =>
      exact hnval (toVal?_isVal htv)
  | newCtx =>
    simp [fillItem] at hbase
    cases hbase with
    | newS _ v' _ _ htv _ =>
      exact hnval (toVal?_isVal htv)

/-- A step of a framed non-value happens strictly inside the frame: the frame is untouched and the
hole steps. This is the key decomposition behind the bind lemma. -/
theorem contextual_step_fillItem_inv (Ki : EctxItem) (e : Expr) (h : Heap)
    (e' : Expr) (h' : Heap) (hnval : ¬ Expr.isVal e) :
    ContextualStep (fillItem Ki e, h) (e', h') →
    ∃ e_step, e' = fillItem Ki e_step ∧ ContextualStep (e, h) (e_step, h') := by
  intro hstep
  obtain ⟨K, e₁, e₂, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
  cases hK : K with
  | nil =>
    subst hK
    simp [fill] at hfill₁
    exact absurd (hfill₁ ▸ hbase) fun hb => base_step_fillItem_absurd Ki e e₂ h h' hnval hb
  | cons ki K' =>
    subst hK
    obtain ⟨init, last, hKsplit⟩ := list_last_split (ki :: K') (List.cons_ne_nil _ _)
    rw [hKsplit, fill_last] at hfill₁
    rw [hKsplit, fill_last] at hfill₂
    -- Injectivity of `fillItem` on the outermost frame forces `last` and `Ki` to agree, hence
    -- `fill init e₁ = e`; the two arms where they disagree put a value in the hole, contradicting
    -- either `hnval` or `hbase`.
    cases last with
    | appLCtx v₁ =>
      cases Ki with
      | appLCtx v₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨rfl, h2⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h2]
      | appRCtx f =>
        simp [fillItem] at hfill₁
        exact absurd (hfill₁.2 ▸ val_isVal v₁) hnval
      | _ => simp [fillItem] at hfill₁
    | appRCtx f₁ =>
      cases Ki with
      | appRCtx f₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1]
      | appLCtx v₂ =>
        simp [fillItem] at hfill₁
        have hval₁ : Expr.isVal (fill init e₁) := by rw [hfill₁.2]; exact val_isVal v₂
        exact absurd hbase (val_no_base_step (fill_isVal_imp init e₁ hval₁))
      | _ => simp [fillItem] at hfill₁
    | unOpCtx op₁ =>
      cases Ki with
      | unOpCtx op₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1]
      | _ => simp [fillItem] at hfill₁
    | binOpLCtx op₁ v₁ =>
      cases Ki with
      | binOpLCtx op₂ v₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl, h3⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1, h3]
      | binOpRCtx op₂ f₂ =>
        simp [fillItem] at hfill₁
        exact absurd (hfill₁.2.2 ▸ val_isVal v₁) hnval
      | _ => simp [fillItem] at hfill₁
    | binOpRCtx op₁ f₁ =>
      cases Ki with
      | binOpRCtx op₂ f₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, h2, rfl⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1, h2]
      | binOpLCtx op₂ v₂ =>
        simp [fillItem] at hfill₁
        have hval₁ : Expr.isVal (fill init e₁) := by rw [hfill₁.2.2]; exact val_isVal v₂
        exact absurd hbase (val_no_base_step (fill_isVal_imp init e₁ hval₁))
      | _ => simp [fillItem] at hfill₁
    | ifCtx e₁' e₂' =>
      cases Ki with
      | ifCtx e₁'' e₂'' =>
        simp [fillItem] at hfill₁
        obtain ⟨rfl, h2, h3⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h2, h3]
      | _ => simp [fillItem] at hfill₁
    | tAppCtx =>
      cases Ki with
      | tAppCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | packCtx =>
      cases Ki with
      | packCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | unpackCtx x₁ body₁ =>
      cases Ki with
      | unpackCtx x₂ body₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl, h3⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1, h3]
      | _ => simp [fillItem] at hfill₁
    | pairLCtx v₁ =>
      cases Ki with
      | pairLCtx v₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨rfl, h2⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h2]
      | pairRCtx f₂ =>
        simp [fillItem] at hfill₁
        exact absurd (hfill₁.2 ▸ val_isVal v₁) hnval
      | _ => simp [fillItem] at hfill₁
    | pairRCtx f₁ =>
      cases Ki with
      | pairRCtx f₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1]
      | pairLCtx v₂ =>
        simp [fillItem] at hfill₁
        have hval₁ : Expr.isVal (fill init e₁) := by rw [hfill₁.2]; exact val_isVal v₂
        exact absurd hbase (val_no_base_step (fill_isVal_imp init e₁ hval₁))
      | _ => simp [fillItem] at hfill₁
    | fstCtx =>
      cases Ki with
      | fstCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | sndCtx =>
      cases Ki with
      | sndCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | injLCtx =>
      cases Ki with
      | injLCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | injRCtx =>
      cases Ki with
      | injRCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | caseCtx e₁' e₂' =>
      cases Ki with
      | caseCtx e₁'' e₂'' =>
        simp [fillItem] at hfill₁
        obtain ⟨rfl, h2, h3⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h2, h3]
      | _ => simp [fillItem] at hfill₁
    | rollCtx =>
      cases Ki with
      | rollCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | unrollCtx =>
      cases Ki with
      | unrollCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | loadCtx =>
      cases Ki with
      | loadCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁
    | storeLCtx v₁ =>
      cases Ki with
      | storeLCtx v₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨rfl, h2⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h2]
      | storeRCtx f₂ =>
        simp [fillItem] at hfill₁
        exact absurd (hfill₁.2 ▸ val_isVal v₁) hnval
      | _ => simp [fillItem] at hfill₁
    | storeRCtx f₁ =>
      cases Ki with
      | storeRCtx f₂ =>
        simp [fillItem] at hfill₁
        obtain ⟨h1, rfl⟩ := hfill₁
        refine ⟨fill init e₂, ?_, .ectxStep init e₁ e₂ h h' hbase⟩
        rw [← hfill₂]
        simp [fillItem, h1]
      | storeLCtx v₂ =>
        simp [fillItem] at hfill₁
        have hval₁ : Expr.isVal (fill init e₁) := by rw [hfill₁.2]; exact val_isVal v₂
        exact absurd hbase (val_no_base_step (fill_isVal_imp init e₁ hval₁))
      | _ => simp [fillItem] at hfill₁
    | newCtx =>
      cases Ki with
      | newCtx =>
        replace hfill₁ : fill init e₁ = e := by simpa [fillItem] using hfill₁
        subst hfill₁
        exact ⟨fill init e₂, hfill₂.symm, .ectxStep init e₁ e₂ h h' hbase⟩
      | _ => simp [fillItem] at hfill₁

/-- Every value expression reads back as a `Val`. -/
private theorem isVal_toVal? {e : Expr} (hval : Expr.isVal e) : ∃ v : Val, e.toVal? = some v := by
  induction e with
  | lit l => exact ⟨.litV l, rfl⟩
  | lam x body => exact ⟨.lamV x body, rfl⟩
  | tLam body => exact ⟨.tLamV body, rfl⟩
  | pack e ih =>
    simp [Expr.isVal] at hval
    obtain ⟨v, hv⟩ := ih hval
    exact ⟨.packV v, by simp [Expr.toVal?, hv, Option.map]⟩
  | pair e₁ e₂ ih₁ ih₂ =>
    simp [Expr.isVal] at hval
    obtain ⟨v₁, hv₁⟩ := ih₁ hval.1
    obtain ⟨v₂, hv₂⟩ := ih₂ hval.2
    exact ⟨.pairV v₁ v₂, by simp [Expr.toVal?, hv₁, hv₂, Option.bind]⟩
  | injL e ih =>
    simp [Expr.isVal] at hval
    obtain ⟨v, hv⟩ := ih hval
    exact ⟨.injLV v, by simp [Expr.toVal?, hv, Option.map]⟩
  | injR e ih =>
    simp [Expr.isVal] at hval
    obtain ⟨v, hv⟩ := ih hval
    exact ⟨.injRV v, by simp [Expr.toVal?, hv, Option.map]⟩
  | roll e ih =>
    simp [Expr.isVal] at hval
    obtain ⟨v, hv⟩ := ih hval
    exact ⟨.rollV v, by simp [Expr.toVal?, hv, Option.map]⟩
  | _ => simp [Expr.isVal] at hval

/-- Value expressions are stuck. -/
private theorem isVal_irreducible {e : Expr} {h : Heap} (hval : Expr.isVal e) :
    irreducible e h := by
  obtain ⟨v, hv⟩ := isVal_toVal? hval
  rw [toVal?_eq hv]
  exact val_irreducible v h

/-- A reduction out of a value expression takes no steps and changes nothing. -/
private theorem nsteps_isVal_inv {e : Expr} {h : Heap} {e' : Expr} {h' : Heap} {n : Nat}
    (hval : Expr.isVal e) (hn : Nsteps n (e, h) (e', h')) :
    n = 0 ∧ e' = e ∧ h' = h := by
  cases hn with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | step hstep _ => exact absurd ⟨_, _, hstep⟩ (isVal_irreducible hval)

/-- Splits a reduction of a framed expression: the hole runs for `j` steps until it gets stuck, and
the frame around the result continues for the remaining `n - j`. -/
theorem red_nsteps_fill_item (Ki : EctxItem) (e e' : Expr) (h h' : Heap) (n : Nat) :
    Nsteps n (fillItem Ki e, h) (e', h') → irreducible e' h' →
    ∃ j e_mid h_mid, j ≤ n ∧
      Nsteps j (e, h) (e_mid, h_mid) ∧ irreducible e_mid h_mid ∧
      Nsteps (n - j) (fillItem Ki e_mid, h_mid) (e', h') := by
  revert e h
  induction n with
  | zero =>
    intro e hp hsteps hirred
    have hirred_e : irreducible e hp := fillItem_irreducible (by cases hsteps; exact hirred)
    exact ⟨0, e, hp, Nat.le.refl, Nsteps.zero, hirred_e, by cases hsteps; exact Nsteps.zero⟩
  | succ m ih =>
    intro e h hsteps hirred
    by_cases hval : Expr.isVal e
    · exact ⟨0, e, h, Nat.zero_le _, Nsteps.zero, isVal_irreducible hval, hsteps⟩
    · obtain ⟨e_next, h_next, hstep_inner, hrest⟩ :
          ∃ e_next h_next,
            ContextualStep (e, h) (e_next, h_next) ∧
            Nsteps m (fillItem Ki e_next, h_next) (e', h') := by
        match hsteps with
        | .step (s₂ := s₂) hstep hrest_s =>
          obtain ⟨e_step, heq_fst, hstep_e⟩ :=
            contextual_step_fillItem_inv Ki e h s₂.1 s₂.2 hval
              (show ContextualStep (fillItem Ki e, h) (s₂.1, s₂.2) by
                cases s₂; exact hstep)
          refine ⟨e_step, s₂.2, hstep_e, ?_⟩
          cases s₂ with | mk fst snd =>
          simp at heq_fst
          subst heq_fst
          exact hrest_s
      obtain ⟨j, e_mid, h_mid, hle_j, hsteps_inner, hirred_mid, hrest_tail⟩ :=
        ih e_next h_next hrest hirred
      exact ⟨j + 1, e_mid, h_mid, by omega,
             Nsteps.step hstep_inner hsteps_inner, hirred_mid,
             (show m + 1 - (j + 1) = m - j by omega) ▸ hrest_tail⟩

/-- Bind for a single evaluation frame: if `e` is related at `A` and plugging any value related at
`A` into `Ki` is related at `B`, then `fillItem Ki e` is related at `B`. The continuation gets the
budget that survives the reduction of `e`. -/
theorem bind_item (δ : TyVarInterp) (A B : Ty) (k : Nat) (W : World)
    (Ki : EctxItem) (e : Expr) :
    exprRel δ A k W e →
    (∀ v j W', j < k → worldExt W W' →
      valRel δ A (k - j) W' v →
      exprRel δ B (k - j) W' (fillItem Ki v.toExpr)) →
    exprRel δ B k W (fillItem Ki e) := by
  intro hexpr hcont
  unfold exprRel
  intro e' h h' n W' hext hwsat hn hred
  obtain ⟨hsteps, hirred⟩ := hred
  obtain ⟨j, e_mid, h_mid, hle, hsteps_e, hirred_mid, hsteps_rest⟩ :=
    red_nsteps_fill_item Ki e e' h h' n hsteps hirred
  have hj_lt_k : j < k := Nat.lt_of_le_of_lt hle hn
  unfold exprRel at hexpr
  obtain ⟨v, W'', hval, hext', hwsat', hv⟩ :=
    hexpr e_mid h h_mid j W' hext hwsat hj_lt_k ⟨hsteps_e, hirred_mid⟩
  have heq_mid := toVal?_eq hval
  subst heq_mid
  have hcont_app := hcont v j W'' hj_lt_k (worldExt_trans hext hext') hv
  unfold exprRel at hcont_app
  have hn_j : n - j < k - j := by omega
  obtain ⟨v_final, W_final, hval_final, hext_final, hwsat_final, hv_final⟩ :=
    hcont_app e' h_mid h' (n - j) W'' (worldExt_refl W'') hwsat' hn_j ⟨hsteps_rest, hirred⟩
  refine ⟨v_final, W_final, hval_final, worldExt_trans hext' hext_final, hwsat_final, ?_⟩
  -- The two reductions spend `j` and `n - j`, together exactly `n`.
  have heq : k - j - (n - j) = k - n := by omega
  rwa [heq] at hv_final

/-! ## Closedness of substitutions -/

/-- Every value a satisfying substitution provides is closed. -/
theorem semCtxRel_substIsClosed (δ : TyVarInterp) (Γ : TypingContext) (W : World) (k : Nat)
    (θ : SubstMap) : semCtxRel δ Γ W k θ → substIsClosed [] θ :=
  fun h => h.2

/-- A satisfying substitution is defined on every variable the context types. This is the side
condition the `hscoped` premises of the binder rules expect. -/
theorem semCtxRel_covers (δ : TyVarInterp) (Γ : TypingContext) (W : World) (k : Nat) (θ : SubstMap)
    (hctx : semCtxRel δ Γ W k θ) :
    ∀ y, get? (M := TyMapStr) Γ y ≠ none → get? (M := MapStr) θ y ≠ none := by
  intro y hΓ
  obtain ⟨A, hA⟩ : ∃ A, get? (M := TyMapStr) Γ y = some A := by
    cases h : get? (M := TyMapStr) Γ y with
    | some A => exact ⟨A, rfl⟩
    | none => exact absurd h hΓ
  obtain ⟨v, hv, _⟩ := hctx.1 y A hA
  rw [hv]
  simp

/-- Closing an expression with a satisfying substitution that covers its free variables yields a
closed expression. -/
theorem substMap_closed_from_semCtxRel (δ : TyVarInterp) (Γ : TypingContext) (W : World) (k : Nat)
    (θ : SubstMap) (e : Expr) (hcov : closedModulo θ [] e) :
    semCtxRel δ Γ W k θ → closed [] (substMap θ e) :=
  fun hctx => substMap_closed_of_closedModulo θ [] e hctx.2 hcov

/-- Under a binder: dropping `x` from a closed substitution leaves the body closed except for `x`
itself, which the binder then binds. -/
theorem substMap_closed_binder (θ : SubstMap) (x : String) (e : Expr)
    (hcov : closedModulo (Iris.Std.delete (M := MapStr) θ x) ((.bNamed x) :b: []) e) :
    substIsClosed [] θ →
    closed ((.bNamed x) :b: []) (substMap (Iris.Std.delete (M := MapStr) θ x) e) := by
  intro hclosed
  have hcl : substIsClosed ((.bNamed x) :b: []) (Iris.Std.delete (M := MapStr) θ x) :=
    substIsClosed_binderDelete (.bNamed x) θ [] hclosed
  exact substMap_closed_of_closedModulo _ _ e hcl hcov

/-! ## Type variable interpretations -/

/-- The value relation only looks at the type variables the type actually mentions: interpretations
agreeing below the well-formedness level `m` are interchangeable. Both weakening and strengthening
of the interpretation follow from this. -/
theorem valRel_tyvar_irrelevance (δ₁ δ₂ : TyVarInterp) (m : Nat) (A : Ty) (k : Nat) (W : World)
    (v : Val) (hagree : ∀ n, n < m → δ₁ n = δ₂ n) (hwf : TypeWf m A) :
    valRel δ₁ A k W v ↔ valRel δ₂ A k W v := by
  match A, v with
  | .int, .litV (.litInt _) => simp [valRel]
  | .int, .litV (.litBool _) => simp [valRel]
  | .int, .litV .litUnit => simp [valRel]
  | .int, .litV (.litLoc _) => simp [valRel]
  | .int, .lamV _ _ => simp [valRel]
  | .int, .tLamV _ => simp [valRel]
  | .int, .packV _ => simp [valRel]
  | .int, .pairV _ _ => simp [valRel]
  | .int, .injLV _ => simp [valRel]
  | .int, .injRV _ => simp [valRel]
  | .int, .rollV _ => simp [valRel]
  | .bool, .litV (.litBool _) => simp [valRel]
  | .bool, .litV (.litInt _) => simp [valRel]
  | .bool, .litV .litUnit => simp [valRel]
  | .bool, .litV (.litLoc _) => simp [valRel]
  | .bool, .lamV _ _ => simp [valRel]
  | .bool, .tLamV _ => simp [valRel]
  | .bool, .packV _ => simp [valRel]
  | .bool, .pairV _ _ => simp [valRel]
  | .bool, .injLV _ => simp [valRel]
  | .bool, .injRV _ => simp [valRel]
  | .bool, .rollV _ => simp [valRel]
  | .unit, .litV .litUnit => simp [valRel]
  | .unit, .litV (.litInt _) => simp [valRel]
  | .unit, .litV (.litBool _) => simp [valRel]
  | .unit, .litV (.litLoc _) => simp [valRel]
  | .unit, .lamV _ _ => simp [valRel]
  | .unit, .tLamV _ => simp [valRel]
  | .unit, .packV _ => simp [valRel]
  | .unit, .pairV _ _ => simp [valRel]
  | .unit, .injLV _ => simp [valRel]
  | .unit, .injRV _ => simp [valRel]
  | .unit, .rollV _ => simp [valRel]
  | .tVar n, v =>
    simp only [valRel]
    have hn : n < m := by cases hwf; assumption
    rw [hagree n hn]
  | .prod A B, .pairV v₁ v₂ =>
    simp only [valRel]
    obtain ⟨hwfA, hwfB⟩ : TypeWf m A ∧ TypeWf m B := by
      cases hwf with | prod_wf h1 h2 => exact ⟨h1, h2⟩
    constructor
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_tyvar_irrelevance δ₁ δ₂ m A k W v₁ hagree hwfA).mp h₁,
             (valRel_tyvar_irrelevance δ₁ δ₂ m B k W v₂ hagree hwfB).mp h₂⟩
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_tyvar_irrelevance δ₁ δ₂ m A k W v₁ hagree hwfA).mpr h₁,
             (valRel_tyvar_irrelevance δ₁ δ₂ m B k W v₂ hagree hwfB).mpr h₂⟩
  | .prod _ _, .litV _ => simp [valRel]
  | .prod _ _, .lamV _ _ => simp [valRel]
  | .prod _ _, .tLamV _ => simp [valRel]
  | .prod _ _, .packV _ => simp [valRel]
  | .prod _ _, .injLV _ => simp [valRel]
  | .prod _ _, .injRV _ => simp [valRel]
  | .prod _ _, .rollV _ => simp [valRel]
  | .sum A _, .injLV v =>
    simp only [valRel]
    have hwfA : TypeWf m A := by cases hwf with | sum_wf h1 _ => exact h1
    exact valRel_tyvar_irrelevance δ₁ δ₂ m A k W v hagree hwfA
  | .sum _ B, .injRV v =>
    simp only [valRel]
    have hwfB : TypeWf m B := by cases hwf with | sum_wf _ h2 => exact h2
    exact valRel_tyvar_irrelevance δ₁ δ₂ m B k W v hagree hwfB
  | .sum _ _, .litV _ => simp [valRel]
  | .sum _ _, .lamV _ _ => simp [valRel]
  | .sum _ _, .tLamV _ => simp [valRel]
  | .sum _ _, .packV _ => simp [valRel]
  | .sum _ _, .pairV _ _ => simp [valRel]
  | .sum _ _, .rollV _ => simp [valRel]
  | .fn A B, .lamV x e =>
    simp only [valRel]
    obtain ⟨hwfA, hwfB⟩ : TypeWf m A ∧ TypeWf m B := by
      cases hwf with | fn_wf h1 h2 => exact ⟨h1, h2⟩
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hv'₁ : valRel δ₁ A (k - kd) W' v' :=
        (valRel_tyvar_irrelevance δ₁ δ₂ m A (k - kd) W' v' hagree hwfA).mpr hv'
      have hexpr := hbody v' kd W' hext hv'₁
      -- The `exprRel` transfer at `B` is the same argument; the recursion cannot call it, so it is
      -- inlined by unfolding `exprRel`.
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_tyvar_irrelevance δ₁ δ₂ m B (k - kd - n) W''' vr hagree hwfB).mp hvr⟩
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hv'₂ : valRel δ₂ A (k - kd) W' v' :=
        (valRel_tyvar_irrelevance δ₁ δ₂ m A (k - kd) W' v' hagree hwfA).mp hv'
      have hexpr := hbody v' kd W' hext hv'₂
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_tyvar_irrelevance δ₁ δ₂ m B (k - kd - n) W''' vr hagree hwfB).mpr hvr⟩
  | .fn _ _, .litV _ => simp [valRel]
  | .fn _ _, .tLamV _ => simp [valRel]
  | .fn _ _, .packV _ => simp [valRel]
  | .fn _ _, .pairV _ _ => simp [valRel]
  | .fn _ _, .injLV _ => simp [valRel]
  | .fn _ _, .injRV _ => simp [valRel]
  | .fn _ _, .rollV _ => simp [valRel]
  | .all A, .tLamV e =>
    simp only [valRel]
    have hwfA : TypeWf (m + 1) A := by cases hwf with | all_wf h => exact h
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hagree' : ∀ n, n < m + 1 →
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n) n =
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n) n := by
        intro n hn
        match n with
        | 0 => rfl
        | n+1 =>
          simp
          exact hagree n (by omega)
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody τ' e' h h' n W' hext hwsat hn hred
      exact ⟨vr, W'', hval, hext', hwsat',
        (valRel_tyvar_irrelevance
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n)
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n)
          (m + 1) A (k - n) W'' vr hagree' hwfA).mp hvr⟩
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hagree' : ∀ n, n < m + 1 →
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n) n =
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n) n := by
        intro n hn
        match n with
        | 0 => rfl
        | n+1 =>
          simp
          exact hagree n (by omega)
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody τ' e' h h' n W' hext hwsat hn hred
      exact ⟨vr, W'', hval, hext', hwsat',
        (valRel_tyvar_irrelevance
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n)
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n)
          (m + 1) A (k - n) W'' vr hagree' hwfA).mpr hvr⟩
  | .all _, .litV _ => simp [valRel]
  | .all _, .lamV _ _ => simp [valRel]
  | .all _, .packV _ => simp [valRel]
  | .all _, .pairV _ _ => simp [valRel]
  | .all _, .injLV _ => simp [valRel]
  | .all _, .injRV _ => simp [valRel]
  | .all _, .rollV _ => simp [valRel]
  | .exist A, .packV v =>
    simp only [valRel]
    have hwfA : TypeWf (m + 1) A := by cases hwf with | exist_wf h => exact h
    constructor
    · intro ⟨τ', hτ⟩
      have hagree' : ∀ n, n < m + 1 →
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n) n =
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n) n := by
        intro n hn
        match n with
        | 0 => rfl
        | n+1 =>
          simp
          exact hagree n (by omega)
      exact ⟨τ', (valRel_tyvar_irrelevance
        (fun n => match n with | 0 => τ' | n+1 => δ₁ n)
        (fun n => match n with | 0 => τ' | n+1 => δ₂ n)
        (m + 1) A k W v hagree' hwfA).mp hτ⟩
    · intro ⟨τ', hτ⟩
      have hagree' : ∀ n, n < m + 1 →
          (fun n => match n with | 0 => τ' | n+1 => δ₁ n) n =
          (fun n => match n with | 0 => τ' | n+1 => δ₂ n) n := by
        intro n hn
        match n with
        | 0 => rfl
        | n+1 =>
          simp
          exact hagree n (by omega)
      exact ⟨τ', (valRel_tyvar_irrelevance
        (fun n => match n with | 0 => τ' | n+1 => δ₁ n)
        (fun n => match n with | 0 => τ' | n+1 => δ₂ n)
        (m + 1) A k W v hagree' hwfA).mpr hτ⟩
  | .exist _, .litV _ => simp [valRel]
  | .exist _, .lamV _ _ => simp [valRel]
  | .exist _, .tLamV _ => simp [valRel]
  | .exist _, .pairV _ _ => simp [valRel]
  | .exist _, .injLV _ => simp [valRel]
  | .exist _, .injRV _ => simp [valRel]
  | .exist _, .rollV _ => simp [valRel]
  | .mu A', .rollV v =>
    have hwfA' : TypeWf (m + 1) A' := by cases hwf with | mu_wf h => exact h
    have hwfSubst : TypeWf m (Ty.subst1 A' (.mu A')) := TypeWf.subst1_mu A' m hwf
    match k with
    | 0 =>
      simp [valRel]
    | k+1 =>
      simp only [valRel]
      constructor
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        exact (valRel_tyvar_irrelevance δ₁ δ₂ m (Ty.subst1 A' (.mu A')) (k - kd) W v hagree
          hwfSubst).mp (hbody kd)
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        exact (valRel_tyvar_irrelevance δ₁ δ₂ m (Ty.subst1 A' (.mu A')) (k - kd) W v hagree
          hwfSubst).mpr (hbody kd)
  | .mu _, .litV _ => simp [valRel]
  | .mu _, .lamV _ _ => simp [valRel]
  | .mu _, .tLamV _ => simp [valRel]
  | .mu _, .packV _ => simp [valRel]
  | .mu _, .pairV _ _ => simp [valRel]
  | .mu _, .injLV _ => simp [valRel]
  | .mu _, .injRV _ => simp [valRel]
  | .ref _, .litV (.litLoc _) => simp [valRel]
  | .ref _, .litV (.litInt _) => simp [valRel]
  | .ref _, .litV (.litBool _) => simp [valRel]
  | .ref _, .litV .litUnit => simp [valRel]
  | .ref _, .lamV _ _ => simp [valRel]
  | .ref _, .tLamV _ => simp [valRel]
  | .ref _, .packV _ => simp [valRel]
  | .ref _, .pairV _ _ => simp [valRel]
  | .ref _, .injLV _ => simp [valRel]
  | .ref _, .injRV _ => simp [valRel]
  | .ref _, .rollV _ => simp [valRel]
termination_by (k, A.size, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact lex_decr (by omega) (by simp only [Ty.size]; omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Ty.size]; omega))

/-- A type well-formed at level `0` mentions no type variables, so adding an interpretation for a
fresh variable leaves the value relation unchanged. -/
theorem valRel_weaken_tyvar (δ : TyVarInterp) (τ : SemType) (A : Ty) (k : Nat) (W : World) (v : Val)
    (hwf : TypeWf 0 A) :
    valRel δ A k W v →
    valRel (fun n => match n with | 0 => τ | n+1 => δ n) A k W v :=
  (valRel_tyvar_irrelevance δ (fun n => match n with | 0 => τ | n+1 => δ n) 0 A k W v
    (fun n hn => absurd hn (Nat.not_lt_zero n)) hwf).mp

/-- Renaming type variables does not change the size measure. -/
theorem Ty.rename_size (A : Ty) (f : Nat → Nat) : (A.rename f).size = A.size := by
  induction A generalizing f with
  | tVar _ => simp [Ty.rename, Ty.size]
  | int => simp [Ty.rename, Ty.size]
  | bool => simp [Ty.rename, Ty.size]
  | unit => simp [Ty.rename, Ty.size]
  | fn A B ihA ihB => simp [Ty.rename, Ty.size, ihA, ihB]
  | all A ih => simp [Ty.rename, Ty.size, ih]
  | exist A ih => simp [Ty.rename, Ty.size, ih]
  | prod A B ihA ihB => simp [Ty.rename, Ty.size, ihA, ihB]
  | sum A B ihA ihB => simp [Ty.rename, Ty.size, ihA, ihB]
  | mu A ih => simp [Ty.rename, Ty.size, ih]
  | ref A => simp [Ty.rename, Ty.size]

/-- Transports the value relation along an equality of type variable interpretations. Needed to
reconcile `(τ .: δ) ∘ lift f` with `τ .: (δ ∘ f)`, which are pointwise but not syntactically
equal. -/
private theorem valRel_interp_congr {δ₁ δ₂ : TyVarInterp} (h : δ₁ = δ₂) {A k W v} :
    valRel δ₁ A k W v → valRel δ₂ A k W v := fun hv => h ▸ hv

/-- Transports the value relation along an equality of types. Used instead of `rw` where both sides
mention the lifted renaming, whose `match` elaborates to distinct auxiliary definitions in the lemma
statement and in `Ty.rename`'s body, so `rw` cannot match even though the terms are definitionally
equal. -/
private theorem valRel_ty_congr {A B : Ty} (h : A = B) {δ k W v} :
    valRel δ A k W v → valRel δ B k W v := fun hv => h ▸ hv

/-- Renaming commutes with interpretation: relating at a renamed type under `δ` is relating at the
original type under `δ ∘ f`. This is the renaming half of the semantic type substitution lemma. -/
theorem valRel_rename (f : Nat → Nat) (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) :
    valRel δ (A.rename f) k W v ↔ valRel (fun n => δ (f n)) A k W v := by
  match A, v with
  | .int, .litV (.litInt _) => simp [Ty.rename, valRel]
  | .int, .litV (.litBool _) => simp [Ty.rename, valRel]
  | .int, .litV .litUnit => simp [Ty.rename, valRel]
  | .int, .litV (.litLoc _) => simp [Ty.rename, valRel]
  | .int, .lamV _ _ => simp [Ty.rename, valRel]
  | .int, .tLamV _ => simp [Ty.rename, valRel]
  | .int, .packV _ => simp [Ty.rename, valRel]
  | .int, .pairV _ _ => simp [Ty.rename, valRel]
  | .int, .injLV _ => simp [Ty.rename, valRel]
  | .int, .injRV _ => simp [Ty.rename, valRel]
  | .int, .rollV _ => simp [Ty.rename, valRel]
  | .bool, .litV (.litBool _) => simp [Ty.rename, valRel]
  | .bool, .litV (.litInt _) => simp [Ty.rename, valRel]
  | .bool, .litV .litUnit => simp [Ty.rename, valRel]
  | .bool, .litV (.litLoc _) => simp [Ty.rename, valRel]
  | .bool, .lamV _ _ => simp [Ty.rename, valRel]
  | .bool, .tLamV _ => simp [Ty.rename, valRel]
  | .bool, .packV _ => simp [Ty.rename, valRel]
  | .bool, .pairV _ _ => simp [Ty.rename, valRel]
  | .bool, .injLV _ => simp [Ty.rename, valRel]
  | .bool, .injRV _ => simp [Ty.rename, valRel]
  | .bool, .rollV _ => simp [Ty.rename, valRel]
  | .unit, .litV .litUnit => simp [Ty.rename, valRel]
  | .unit, .litV (.litInt _) => simp [Ty.rename, valRel]
  | .unit, .litV (.litBool _) => simp [Ty.rename, valRel]
  | .unit, .litV (.litLoc _) => simp [Ty.rename, valRel]
  | .unit, .lamV _ _ => simp [Ty.rename, valRel]
  | .unit, .tLamV _ => simp [Ty.rename, valRel]
  | .unit, .packV _ => simp [Ty.rename, valRel]
  | .unit, .pairV _ _ => simp [Ty.rename, valRel]
  | .unit, .injLV _ => simp [Ty.rename, valRel]
  | .unit, .injRV _ => simp [Ty.rename, valRel]
  | .unit, .rollV _ => simp [Ty.rename, valRel]
  | .tVar n, v =>
    simp only [Ty.rename, valRel]
  | .prod A B, .pairV v₁ v₂ =>
    simp only [Ty.rename, valRel]
    constructor
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_rename f δ A k W v₁).mp h₁,
             (valRel_rename f δ B k W v₂).mp h₂⟩
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_rename f δ A k W v₁).mpr h₁,
             (valRel_rename f δ B k W v₂).mpr h₂⟩
  | .prod _ _, .litV _ => simp [Ty.rename, valRel]
  | .prod _ _, .lamV _ _ => simp [Ty.rename, valRel]
  | .prod _ _, .tLamV _ => simp [Ty.rename, valRel]
  | .prod _ _, .packV _ => simp [Ty.rename, valRel]
  | .prod _ _, .injLV _ => simp [Ty.rename, valRel]
  | .prod _ _, .injRV _ => simp [Ty.rename, valRel]
  | .prod _ _, .rollV _ => simp [Ty.rename, valRel]
  | .sum A _, .injLV v =>
    simp only [Ty.rename, valRel]
    exact valRel_rename f δ A k W v
  | .sum _ B, .injRV v =>
    simp only [Ty.rename, valRel]
    exact valRel_rename f δ B k W v
  | .sum _ _, .litV _ => simp [Ty.rename, valRel]
  | .sum _ _, .lamV _ _ => simp [Ty.rename, valRel]
  | .sum _ _, .tLamV _ => simp [Ty.rename, valRel]
  | .sum _ _, .packV _ => simp [Ty.rename, valRel]
  | .sum _ _, .pairV _ _ => simp [Ty.rename, valRel]
  | .sum _ _, .rollV _ => simp [Ty.rename, valRel]
  | .fn A B, .lamV x e =>
    simp only [Ty.rename, valRel]
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hv'₁ : valRel δ (A.rename f) (k - kd) W' v' :=
        (valRel_rename f δ A (k - kd) W' v').mpr hv'
      have hexpr := hbody v' kd W' hext hv'₁
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_rename f δ B (k - kd - n) W''' vr).mp hvr⟩
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hv'₂ : valRel (fun n => δ (f n)) A (k - kd) W' v' :=
        (valRel_rename f δ A (k - kd) W' v').mp hv'
      have hexpr := hbody v' kd W' hext hv'₂
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_rename f δ B (k - kd - n) W''' vr).mpr hvr⟩
  | .fn _ _, .litV _ => simp [Ty.rename, valRel]
  | .fn _ _, .tLamV _ => simp [Ty.rename, valRel]
  | .fn _ _, .packV _ => simp [Ty.rename, valRel]
  | .fn _ _, .pairV _ _ => simp [Ty.rename, valRel]
  | .fn _ _, .injLV _ => simp [Ty.rename, valRel]
  | .fn _ _, .injRV _ => simp [Ty.rename, valRel]
  | .fn _ _, .rollV _ => simp [Ty.rename, valRel]
  | .all A, .tLamV e =>
    simp only [Ty.rename, valRel]
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hbody' := hbody τ'
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody' e' h h' n W' hext hwsat hn hred
      refine ⟨vr, W'', hval, hext', hwsat', ?_⟩
      -- The recursive call renames under the binder, so it produces the interpretation
      -- `fun n => (τ' .: δ) (lift f n)`; that is pointwise equal to `τ' .: (δ ∘ f)`, but not
      -- syntactically, hence `valRel_interp_congr`.
      refine valRel_interp_congr ?_
        ((valRel_rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1)
          (fun n => match n with | 0 => τ' | n+1 => δ n) A (k - n) W'' vr).mp hvr)
      funext m
      match m with
      | 0 => rfl
      | m+1 => rfl
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hbody' := hbody τ'
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody' e' h h' n W' hext hwsat hn hred
      refine ⟨vr, W'', hval, hext', hwsat', ?_⟩
      refine (valRel_rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1)
        (fun n => match n with | 0 => τ' | n+1 => δ n) A (k - n) W'' vr).mpr
        (valRel_interp_congr ?_ hvr)
      funext m
      match m with
      | 0 => rfl
      | m+1 => rfl
  | .all _, .litV _ => simp [Ty.rename, valRel]
  | .all _, .lamV _ _ => simp [Ty.rename, valRel]
  | .all _, .packV _ => simp [Ty.rename, valRel]
  | .all _, .pairV _ _ => simp [Ty.rename, valRel]
  | .all _, .injLV _ => simp [Ty.rename, valRel]
  | .all _, .injRV _ => simp [Ty.rename, valRel]
  | .all _, .rollV _ => simp [Ty.rename, valRel]
  | .exist A, .packV v =>
    simp only [Ty.rename, valRel]
    constructor
    · intro ⟨τ', hτ⟩
      refine ⟨τ', valRel_interp_congr ?_
        ((valRel_rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1)
          (fun n => match n with | 0 => τ' | n+1 => δ n) A k W v).mp hτ)⟩
      funext m
      match m with
      | 0 => rfl
      | m+1 => rfl
    · intro ⟨τ', hτ⟩
      refine ⟨τ', (valRel_rename (fun n => match n with | 0 => 0 | n+1 => (f n) + 1)
        (fun n => match n with | 0 => τ' | n+1 => δ n) A k W v).mpr
        (valRel_interp_congr ?_ hτ)⟩
      funext m
      match m with
      | 0 => rfl
      | m+1 => rfl
  | .exist _, .litV _ => simp [Ty.rename, valRel]
  | .exist _, .lamV _ _ => simp [Ty.rename, valRel]
  | .exist _, .tLamV _ => simp [Ty.rename, valRel]
  | .exist _, .pairV _ _ => simp [Ty.rename, valRel]
  | .exist _, .injLV _ => simp [Ty.rename, valRel]
  | .exist _, .injRV _ => simp [Ty.rename, valRel]
  | .exist _, .rollV _ => simp [Ty.rename, valRel]
  | .mu A', .rollV v =>
    match k with
    | 0 =>
      simp [Ty.rename, valRel]
    | k+1 =>
      simp only [Ty.rename, valRel]
      constructor
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        -- Unrolling under a lifted renaming is the same as renaming the unrolling
        -- (`Ty.subst1_mu_rename_comm`), after which the recursive call applies.
        exact (valRel_rename f δ (Ty.subst1 A' (.mu A')) (k - kd) W v).mp
          (valRel_ty_congr (Ty.subst1_mu_rename_comm A' f) (hbody kd))
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        exact valRel_ty_congr (Ty.subst1_mu_rename_comm A' f).symm
          ((valRel_rename f δ (Ty.subst1 A' (.mu A')) (k - kd) W v).mpr (hbody kd))
  | .mu _, .litV _ => simp [Ty.rename, valRel]
  | .mu _, .lamV _ _ => simp [Ty.rename, valRel]
  | .mu _, .tLamV _ => simp [Ty.rename, valRel]
  | .mu _, .packV _ => simp [Ty.rename, valRel]
  | .mu _, .pairV _ _ => simp [Ty.rename, valRel]
  | .mu _, .injLV _ => simp [Ty.rename, valRel]
  | .mu _, .injRV _ => simp [Ty.rename, valRel]
  | .ref _, .litV (.litLoc _) => simp [Ty.rename, valRel]
  | .ref _, .litV (.litInt _) => simp [Ty.rename, valRel]
  | .ref _, .litV (.litBool _) => simp [Ty.rename, valRel]
  | .ref _, .litV .litUnit => simp [Ty.rename, valRel]
  | .ref _, .lamV _ _ => simp [Ty.rename, valRel]
  | .ref _, .tLamV _ => simp [Ty.rename, valRel]
  | .ref _, .packV _ => simp [Ty.rename, valRel]
  | .ref _, .pairV _ _ => simp [Ty.rename, valRel]
  | .ref _, .injLV _ => simp [Ty.rename, valRel]
  | .ref _, .injRV _ => simp [Ty.rename, valRel]
  | .ref _, .rollV _ => simp [Ty.rename, valRel]
termination_by (k, A.size, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact lex_decr (by omega) (by simp only [Ty.size]; omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Ty.size, Ty.rename_size]; omega))

/-! ## Semantic type substitution -/

/-- Turns a syntactic type into a semantic type by interpreting it under `δ`; the closure properties
of `SemType` are exactly the value relation's monotonicity and closedness lemmas. -/
def interp_type (B : Ty) (δ : TyVarInterp) : SemType where
  rel := fun k W v => valRel δ B k W v
  closed_val := fun k W v hv => valRel_closed δ B k W v hv
  mono := fun k k' W v hv hle => valRel_mono_idx δ B k k' W v hle hv
  mono_world := fun k W W' v hv hext => valRel_mono_world δ B k W W' v hext hv

/-- Semantic types are determined by their value predicate: the remaining fields are proofs of
`Prop`s, so proof irrelevance makes them equal automatically. -/
private theorem SemType.ext {τ₁ τ₂ : SemType} (h : τ₁.rel = τ₂.rel) : τ₁ = τ₂ := by
  cases τ₁
  cases τ₂
  cases h
  rfl

/-- Interpreting a substitution lifted under a binder: `up σ` interpreted in `τ .: δ` agrees with
`τ .: (σ interpreted in δ)`. This is the semantic counterpart of `Ty.up_substTy_comm` and is what
lets the `∀`/`∃` cases of `valRel_substTy` go through. -/
private theorem interp_up_eq (σ : Nat → Ty) (δ : TyVarInterp) (τ : SemType) :
    (fun n => interp_type
        ((fun n => match n with | 0 => Ty.tVar 0 | n+1 => (σ n).rename (· + 1)) n)
        (fun m => match m with | 0 => τ | m+1 => δ m))
    = (fun n => match n with | 0 => τ | n+1 => interp_type (σ n) δ) := by
  funext n
  refine SemType.ext ?_
  cases n with
  | zero =>
    funext k W v
    show valRel (fun m => match m with | 0 => τ | m+1 => δ m) (Ty.tVar 0) k W v = τ.rel k W v
    simp only [valRel]
  | succ m =>
    funext k W v
    show valRel (fun m => match m with | 0 => τ | m+1 => δ m) ((σ m).rename (· + 1)) k W v
      = valRel δ (σ m) k W v
    exact propext (valRel_rename (· + 1) (fun m => match m with | 0 => τ | m+1 => δ m) (σ m) k W v)

/-- Substitution commutes with interpretation: relating at a substituted type under `δ` is relating
at the original type under the interpreted substitution. Proved by well-founded recursion on
`(k, A.size)`, mirroring `valRel_rename`. -/
theorem valRel_substTy (σ : Nat → Ty) (δ : TyVarInterp) (A : Ty) (k : Nat) (W : World) (v : Val) :
    valRel (fun n => interp_type (σ n) δ) A k W v ↔ valRel δ (A.substTy σ) k W v := by
  match A, v with
  | .int, .litV (.litInt _) => simp [Ty.substTy, valRel]
  | .int, .litV (.litBool _) => simp [Ty.substTy, valRel]
  | .int, .litV .litUnit => simp [Ty.substTy, valRel]
  | .int, .litV (.litLoc _) => simp [Ty.substTy, valRel]
  | .int, .lamV _ _ => simp [Ty.substTy, valRel]
  | .int, .tLamV _ => simp [Ty.substTy, valRel]
  | .int, .packV _ => simp [Ty.substTy, valRel]
  | .int, .pairV _ _ => simp [Ty.substTy, valRel]
  | .int, .injLV _ => simp [Ty.substTy, valRel]
  | .int, .injRV _ => simp [Ty.substTy, valRel]
  | .int, .rollV _ => simp [Ty.substTy, valRel]
  | .bool, .litV (.litBool _) => simp [Ty.substTy, valRel]
  | .bool, .litV (.litInt _) => simp [Ty.substTy, valRel]
  | .bool, .litV .litUnit => simp [Ty.substTy, valRel]
  | .bool, .litV (.litLoc _) => simp [Ty.substTy, valRel]
  | .bool, .lamV _ _ => simp [Ty.substTy, valRel]
  | .bool, .tLamV _ => simp [Ty.substTy, valRel]
  | .bool, .packV _ => simp [Ty.substTy, valRel]
  | .bool, .pairV _ _ => simp [Ty.substTy, valRel]
  | .bool, .injLV _ => simp [Ty.substTy, valRel]
  | .bool, .injRV _ => simp [Ty.substTy, valRel]
  | .bool, .rollV _ => simp [Ty.substTy, valRel]
  | .unit, .litV .litUnit => simp [Ty.substTy, valRel]
  | .unit, .litV (.litInt _) => simp [Ty.substTy, valRel]
  | .unit, .litV (.litBool _) => simp [Ty.substTy, valRel]
  | .unit, .litV (.litLoc _) => simp [Ty.substTy, valRel]
  | .unit, .lamV _ _ => simp [Ty.substTy, valRel]
  | .unit, .tLamV _ => simp [Ty.substTy, valRel]
  | .unit, .packV _ => simp [Ty.substTy, valRel]
  | .unit, .pairV _ _ => simp [Ty.substTy, valRel]
  | .unit, .injLV _ => simp [Ty.substTy, valRel]
  | .unit, .injRV _ => simp [Ty.substTy, valRel]
  | .unit, .rollV _ => simp [Ty.substTy, valRel]
  | .tVar n, v => simp only [Ty.substTy, valRel, interp_type]
  | .prod A B, .pairV v₁ v₂ =>
    simp only [Ty.substTy, valRel]
    constructor
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_substTy σ δ A k W v₁).mp h₁, (valRel_substTy σ δ B k W v₂).mp h₂⟩
    · intro ⟨h₁, h₂⟩
      exact ⟨(valRel_substTy σ δ A k W v₁).mpr h₁, (valRel_substTy σ δ B k W v₂).mpr h₂⟩
  | .prod _ _, .litV _ => simp [Ty.substTy, valRel]
  | .prod _ _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .prod _ _, .tLamV _ => simp [Ty.substTy, valRel]
  | .prod _ _, .packV _ => simp [Ty.substTy, valRel]
  | .prod _ _, .injLV _ => simp [Ty.substTy, valRel]
  | .prod _ _, .injRV _ => simp [Ty.substTy, valRel]
  | .prod _ _, .rollV _ => simp [Ty.substTy, valRel]
  | .sum A _, .injLV v =>
    simp only [Ty.substTy, valRel]
    exact valRel_substTy σ δ A k W v
  | .sum _ B, .injRV v =>
    simp only [Ty.substTy, valRel]
    exact valRel_substTy σ δ B k W v
  | .sum _ _, .litV _ => simp [Ty.substTy, valRel]
  | .sum _ _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .sum _ _, .tLamV _ => simp [Ty.substTy, valRel]
  | .sum _ _, .packV _ => simp [Ty.substTy, valRel]
  | .sum _ _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .sum _ _, .rollV _ => simp [Ty.substTy, valRel]
  | .fn A B, .lamV x e =>
    simp only [Ty.substTy, valRel]
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hexpr := hbody v' kd W' hext ((valRel_substTy σ δ A (k - kd) W' v').mpr hv')
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_substTy σ δ B (k - kd - n) W''' vr).mp hvr⟩
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro v' kd W' hext hv'
      have hexpr := hbody v' kd W' hext ((valRel_substTy σ δ A (k - kd) W' v').mp hv')
      unfold exprRel at *
      intro e' h h' n W'' hext' hwsat hn hred
      obtain ⟨vr, W''', hval, hext'', hwsat'', hvr⟩ := hexpr e' h h' n W'' hext' hwsat hn hred
      exact ⟨vr, W''', hval, hext'', hwsat'',
        (valRel_substTy σ δ B (k - kd - n) W''' vr).mpr hvr⟩
  | .fn _ _, .litV _ => simp [Ty.substTy, valRel]
  | .fn _ _, .tLamV _ => simp [Ty.substTy, valRel]
  | .fn _ _, .packV _ => simp [Ty.substTy, valRel]
  | .fn _ _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .fn _ _, .injLV _ => simp [Ty.substTy, valRel]
  | .fn _ _, .injRV _ => simp [Ty.substTy, valRel]
  | .fn _ _, .rollV _ => simp [Ty.substTy, valRel]
  | .all A, .tLamV e =>
    simp only [Ty.substTy, valRel]
    constructor
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hbody' := hbody τ'
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody' e' h h' n W' hext hwsat hn hred
      refine ⟨vr, W'', hval, hext', hwsat', ?_⟩
      refine (valRel_substTy _ (fun m => match m with | 0 => τ' | m+1 => δ m) A (k - n)
        W'' vr).mp ?_
      exact valRel_interp_congr (interp_up_eq σ δ τ').symm hvr
    · intro ⟨hcl, hbody⟩
      refine ⟨hcl, ?_⟩
      intro τ'
      have hbody' := hbody τ'
      unfold exprRel at *
      intro e' h h' n W' hext hwsat hn hred
      obtain ⟨vr, W'', hval, hext', hwsat', hvr⟩ := hbody' e' h h' n W' hext hwsat hn hred
      refine ⟨vr, W'', hval, hext', hwsat', ?_⟩
      refine valRel_interp_congr (interp_up_eq σ δ τ') ?_
      exact (valRel_substTy _ (fun m => match m with | 0 => τ' | m+1 => δ m) A (k - n)
        W'' vr).mpr hvr
  | .all _, .litV _ => simp [Ty.substTy, valRel]
  | .all _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .all _, .packV _ => simp [Ty.substTy, valRel]
  | .all _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .all _, .injLV _ => simp [Ty.substTy, valRel]
  | .all _, .injRV _ => simp [Ty.substTy, valRel]
  | .all _, .rollV _ => simp [Ty.substTy, valRel]
  | .exist A, .packV v =>
    simp only [Ty.substTy, valRel]
    constructor
    · intro ⟨τ', hτ⟩
      refine ⟨τ', (valRel_substTy _ (fun m => match m with | 0 => τ' | m+1 => δ m) A k W v).mp ?_⟩
      exact valRel_interp_congr (interp_up_eq σ δ τ').symm hτ
    · intro ⟨τ', hτ⟩
      refine ⟨τ', valRel_interp_congr (interp_up_eq σ δ τ') ?_⟩
      exact (valRel_substTy _ (fun m => match m with | 0 => τ' | m+1 => δ m) A k W v).mpr hτ
  | .exist _, .litV _ => simp [Ty.substTy, valRel]
  | .exist _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .exist _, .tLamV _ => simp [Ty.substTy, valRel]
  | .exist _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .exist _, .injLV _ => simp [Ty.substTy, valRel]
  | .exist _, .injRV _ => simp [Ty.substTy, valRel]
  | .exist _, .rollV _ => simp [Ty.substTy, valRel]
  | .mu A', .rollV v =>
    match k with
    | 0 => simp [Ty.substTy, valRel]
    | k+1 =>
      simp only [Ty.substTy, valRel]
      constructor
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        -- Unrolling then substituting is substituting then unrolling.
        exact valRel_ty_congr (Ty.subst1_mu_substTy_comm A' σ).symm
          ((valRel_substTy σ δ (Ty.subst1 A' (.mu A')) (k - kd) W v).mp (hbody kd))
      · intro ⟨hcl, hbody⟩
        refine ⟨hcl, fun kd => ?_⟩
        exact (valRel_substTy σ δ (Ty.subst1 A' (.mu A')) (k - kd) W v).mpr
          (valRel_ty_congr (Ty.subst1_mu_substTy_comm A' σ) (hbody kd))
  | .mu _, .litV _ => simp [Ty.substTy, valRel]
  | .mu _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .mu _, .tLamV _ => simp [Ty.substTy, valRel]
  | .mu _, .packV _ => simp [Ty.substTy, valRel]
  | .mu _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .mu _, .injLV _ => simp [Ty.substTy, valRel]
  | .mu _, .injRV _ => simp [Ty.substTy, valRel]
  -- The reference case ignores the pointee type entirely (the invariant lives in the world), so
  -- substitution is irrelevant here.
  | .ref _, .litV (.litLoc _) => simp [Ty.substTy, valRel]
  | .ref _, .litV (.litInt _) => simp [Ty.substTy, valRel]
  | .ref _, .litV (.litBool _) => simp [Ty.substTy, valRel]
  | .ref _, .litV .litUnit => simp [Ty.substTy, valRel]
  | .ref _, .lamV _ _ => simp [Ty.substTy, valRel]
  | .ref _, .tLamV _ => simp [Ty.substTy, valRel]
  | .ref _, .packV _ => simp [Ty.substTy, valRel]
  | .ref _, .pairV _ _ => simp [Ty.substTy, valRel]
  | .ref _, .injLV _ => simp [Ty.substTy, valRel]
  | .ref _, .injRV _ => simp [Ty.substTy, valRel]
  | .ref _, .rollV _ => simp [Ty.substTy, valRel]
termination_by (k, A.size, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact lex_decr (by omega) (by simp only [Ty.size]; omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp only [Ty.size]; omega))

/-- Semantic type substitution, single-variable form: instantiating variable `0` with `B` is the
same as extending the interpretation with `B`'s interpretation. -/
theorem valRel_subst_ty (δ : TyVarInterp) (A B : Ty) (k : Nat) (W : World) (v : Val) :
    valRel δ (A.subst1 B) k W v ↔
    valRel (fun n => match n with | 0 => interp_type B δ | n+1 => δ n) A k W v := by
  have hσ : (fun n => interp_type ((fun n => match n with | 0 => B | n+1 => Ty.tVar n) n) δ)
      = (fun n => match n with | 0 => interp_type B δ | n+1 => δ n) := by
    funext n
    refine SemType.ext ?_
    cases n with
    | zero => rfl
    | succ m =>
      funext k W v
      simp only [interp_type, valRel]
  calc valRel δ (A.subst1 B) k W v
    _ ↔ valRel (fun n => interp_type ((fun n => match n with | 0 => B | n+1 => Ty.tVar n) n) δ)
          A k W v :=
      (valRel_substTy (fun n => match n with | 0 => B | n+1 => Ty.tVar n) δ A k W v).symm
    _ ↔ valRel (fun n => match n with | 0 => interp_type B δ | n+1 => δ n) A k W v := by rw [hσ]

/-- Semantic type substitution for the expression relation. -/
theorem exprRel_subst_ty (δ : TyVarInterp) (A B : Ty) (k : Nat) (W : World) (e : Expr) :
    exprRel (fun n => match n with | 0 => interp_type B δ | n+1 => δ n) A k W e →
    exprRel δ (A.subst1 B) k W e := by
  intro he
  unfold exprRel at *
  intro e' h h' n W' hext hwsat hn hred
  obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := he e' h h' n W' hext hwsat hn hred
  exact ⟨v, W'', hval, hext', hwsat', (valRel_subst_ty δ A B (k - n) W'' v).mpr hv⟩

/-- Converse of `valRel_weaken_tyvar`: a type well-formed at level `0` mentions no type variables,
so the interpretation of the fresh variable can be discarded. -/
theorem valRel_strengthen_tyvar (δ : TyVarInterp) (τ : SemType) (B : Ty) (k : Nat) (W : World)
    (v : Val) (hwf : TypeWf 0 B) :
    valRel (fun n => match n with | 0 => τ | n+1 => δ n) B k W v →
    valRel δ B k W v :=
  (valRel_tyvar_irrelevance (fun n => match n with | 0 => τ | n+1 => δ n) δ 0 B k W v
    (fun n hn => absurd hn (Nat.not_lt_zero n)) hwf).mp

/-- Strengthening the interpretation for the expression relation. -/
theorem exprRel_strengthen_tyvar (δ : TyVarInterp) (τ : SemType) (B : Ty) (k : Nat) (W : World)
    (e : Expr) (hwf : TypeWf 0 B) :
    exprRel (fun n => match n with | 0 => τ | n+1 => δ n) B k W e →
    exprRel δ B k W e := by
  intro he
  unfold exprRel at *
  intro e' h h' n W' hext hwsat hn hred
  obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := he e' h h' n W' hext hwsat hn hred
  exact ⟨v, W'', hval, hext', hwsat', valRel_strengthen_tyvar δ τ B (k - n) W'' v hwf hv⟩

/-! ### Shifting under a type binder -/

/-- Shifting a type by one variable is undone by extending the interpretation: the shifted type
never mentions variable `0`, so `τ` is irrelevant to it.

This is what the context shift `shiftCtx Γ` buys us. Unlike `valRel_weaken_tyvar`, it needs no
well-formedness side condition — the shift is visible in the type, so nothing has to be assumed
about it. -/
theorem valRel_shift (δ : TyVarInterp) (τ : SemType) (A : Ty) (k : Nat) (W : World) (v : Val) :
    valRel δ A k W v ↔
    valRel (fun n => match n with | 0 => τ | n+1 => δ n) (A.rename (· + 1)) k W v := by
  rw [valRel_rename (· + 1) (fun n => match n with | 0 => τ | n+1 => δ n) A k W v]

/-- Shifting for the expression relation. -/
theorem exprRel_shift (δ : TyVarInterp) (τ : SemType) (A : Ty) (k : Nat) (W : World) (e : Expr) :
    exprRel δ A k W e ↔
    exprRel (fun n => match n with | 0 => τ | n+1 => δ n) (A.rename (· + 1)) k W e := by
  unfold exprRel
  constructor
  · intro he e' h h' n W' hext hwsat hn hred
    obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := he e' h h' n W' hext hwsat hn hred
    exact ⟨v, W'', hval, hext', hwsat', (valRel_shift δ τ A (k - n) W'' v).mp hv⟩
  · intro he e' h h' n W' hext hwsat hn hred
    obtain ⟨v, W'', hval, hext', hwsat', hv⟩ := he e' h h' n W' hext hwsat hn hred
    exact ⟨v, W'', hval, hext', hwsat', (valRel_shift δ τ A (k - n) W'' v).mpr hv⟩

/-- A satisfying substitution for `Γ` also satisfies `shiftCtx Γ` under any extension of the
interpretation. This is what lets the type-abstraction rule pass the same substitution through the
type binder. -/
theorem semCtxRel_shift (δ : TyVarInterp) (τ : SemType) (Γ : TypingContext)
    (W : World) (k : Nat) (θ : SubstMap) :
    semCtxRel δ Γ W k θ →
    semCtxRel (fun n => match n with | 0 => τ | n+1 => δ n) (shiftCtx Γ) W k θ := by
  intro hctx
  refine ⟨?_, hctx.2⟩
  intro x A hlook
  rw [shiftCtx_get?] at hlook
  obtain ⟨A', hA', heq⟩ := Option.map_eq_some_iff.mp hlook
  obtain ⟨v, hv_get, hv_rel⟩ := hctx.1 x A' hA'
  subst heq
  exact ⟨v, hv_get, (valRel_shift δ τ A' k W v).mp hv_rel⟩

/-! ## Compatibility lemmas

One lemma per typing rule, each showing that `semTyped` is closed under that rule. Every lemma for a
compound expression follows the same shape: `bind_item` reduces the subterms to values in evaluation
order, the resulting value relation pins down their shape, and `expr_det_step_closure` consumes the
redex step. -/

/-- Integer literals. -/
theorem compat_int (Γ : TypingContext) (z : Int) : semTyped Γ (.lit (.litInt z)) .int := by
  intro δ W k θ hctx
  show exprRel δ .int k W (Val.litV (.litInt z)).toExpr
  apply sem_val_expr_rel
  simp [valRel]

/-- Boolean literals. -/
theorem compat_bool (Γ : TypingContext) (b : Bool) : semTyped Γ (.lit (.litBool b)) .bool := by
  intro δ W k θ hctx
  show exprRel δ .bool k W (Val.litV (.litBool b)).toExpr
  apply sem_val_expr_rel
  simp [valRel]

/-- The unit literal. -/
theorem compat_unit (Γ : TypingContext) : semTyped Γ (.lit .litUnit) .unit := by
  intro δ W k θ hctx
  show exprRel δ .unit k W (Val.litV .litUnit).toExpr
  apply sem_val_expr_rel
  simp [valRel]

/-- Variables. The substitution supplies a value already in the relation at `A`. -/
theorem compat_var (Γ : TypingContext) (x : String) (A : Ty) :
    get? (M := TyMapStr) Γ x = some A → semTyped Γ (.var x) A := by
  intro hlookup δ W k θ hctx
  obtain ⟨v, hθ, hv⟩ := hctx.1 x A hlookup
  show exprRel δ A k W (substMap θ (.var x))
  simp only [substMap, hθ]
  exact sem_val_expr_rel δ A k W v hv

/-- Term abstraction. The `hscoped` premise says that whenever `θ` covers the domain of `Γ`,
substituting all of it except `x` leaves at most `x` free in `e`; the value relation at `.fn`
demands that the lambda body be closed under its own binder, and `semTyped` alone does not give
this. -/
theorem compat_lam (Γ : TypingContext) (x : String) (e : Expr) (A B : Ty)
    (hscoped : ∀ θ : SubstMap,
      (∀ y, get? (M := TyMapStr) Γ y ≠ none → get? (M := MapStr) θ y ≠ none) →
      closedModulo (Iris.Std.delete (M := MapStr) θ x) ((.bNamed x) :b: []) e) :
    semTyped (insert (M := TyMapStr) Γ x A) e B → semTyped Γ (.lam (.bNamed x) e) (.fn A B) := by
  intro hbody δ W k θ hctx
  show exprRel δ (.fn A B) k W (substMap θ (.lam (.bNamed x) e))
  change
    exprRel δ (.fn A B) k W (Val.lamV (.bNamed x) (substMap (binderDelete (.bNamed x) θ) e)).toExpr
  apply sem_val_expr_rel
  show valRel δ (.fn A B) k W (Val.lamV (.bNamed x) (substMap (binderDelete (.bNamed x) θ) e))
  simp only [valRel, binderDelete]
  constructor
  · exact substMap_closed_binder θ x e (hscoped θ (semCtxRel_covers δ Γ W k θ hctx))
      (semCtxRel_substIsClosed δ Γ W k θ hctx)
  · intro v' kd W' hext' hv'
    -- Substituting the argument after `θ` is the same as extending `θ` with it, because every
    -- value in `θ` is closed and so cannot capture `x`.
    have hrw : subst' (.bNamed x) v'.toExpr (substMap (Iris.Std.delete (M := MapStr) θ x) e) =
               substMap (Iris.Std.insert (M := MapStr) θ x v'.toExpr) e := by
      have h := subst'_substMap (.bNamed x) v'.toExpr θ e (semCtxRel_substIsClosed δ Γ W k θ hctx)
      simpa [binderDelete] using h
    rw [hrw]
    apply hbody δ W' (k - kd) (Iris.Std.insert (M := MapStr) θ x v'.toExpr)
    constructor
    · intro y B' hlook
      by_cases hxy : x = y
      · subst hxy
        rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at hlook
        injection hlook with hlook; subst hlook
        exact ⟨v', LawfulPartialMap.get?_insert_eq (M := MapStr) rfl, hv'⟩
      · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hlook
        obtain ⟨v'', hv''_lookup, hv''_rel⟩ := hctx.1 y B' hlook
        exact ⟨v'', by rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]; exact hv''_lookup,
             valRel_mono δ B' k (k - kd) W W' v'' (by omega) hext' hv''_rel⟩
    · intro y ey hget
      by_cases hxy : x = y
      · subst hxy
        rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hget
        injection hget with hget; subst hget
        exact valRel_closed δ A (k - kd) W' v' hv'
      · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hget
        exact hctx.2 y ey hget

/-- Application. Arguments are evaluated before functions, so `e₂` is bound first. -/
theorem compat_app (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ (.fn A B) → semTyped Γ e₂ A → semTyped Γ (.app e₁ e₂) B := by
  intro he₁ he₂ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ B k W (.app (substMap θ e₁) (substMap θ e₂))
  change exprRel δ B k W (fillItem (.appRCtx (substMap θ e₁)) (substMap θ e₂))
  apply bind_item δ A B k W (.appRCtx (substMap θ e₁)) (substMap θ e₂) hexpr₂
  intro v₂ j₂ W₂ hj₂ hext₂ hv₂
  show exprRel δ B (k - j₂) W₂ (.app (substMap θ e₁) v₂.toExpr)
  change exprRel δ B (k - j₂) W₂ (fillItem (.appLCtx v₂) (substMap θ e₁))
  have hexpr₁' : exprRel δ (.fn A B) (k - j₂) W₂ (substMap θ e₁) :=
    exprRel_mono δ (.fn A B) k (k - j₂) W W₂ (substMap θ e₁) (by omega) hext₂ hexpr₁
  apply bind_item δ (.fn A B) B (k - j₂) W₂ (.appLCtx v₂) (substMap θ e₁) hexpr₁'
  intro v₁ j₁ W₃ hj₁ hext₃ hv₁
  cases v₁ with
  | lamV x body =>
    simp only [valRel] at hv₁
    obtain ⟨_, hbody⟩ := hv₁
    show exprRel δ B (k - j₂ - j₁) W₃ (.app (.lam x body) v₂.toExpr)
    apply expr_det_step_closure
    · exact det_step_beta x body v₂.toExpr (val_isVal v₂)
    · -- The beta step itself costs one index, which is exactly the offset `kd = 1` at which the
      -- value relation at `.fn` guarantees the body.
      have hv₂' : valRel δ A (k - j₂ - j₁ - 1) W₃ v₂ :=
        valRel_mono δ A (k - j₂) (k - j₂ - j₁ - 1) W₂ W₃ v₂ (by omega) hext₃ hv₂
      exact hbody v₂ 1 W₃ (worldExt_refl W₃) hv₂'
  | _ => simp [valRel] at hv₁

/-- Type abstraction. Since types are erased at runtime the body is entered with an arbitrary
interpretation `τ` for the new variable, which `semCtxRel_shift` transports the context relation
across. As in `compat_lam`, `hscoped` supplies the closedness the value relation demands. -/
theorem compat_tLam (Γ : TypingContext) (e : Expr) (A : Ty)
    (hscoped : ∀ θ : SubstMap,
      (∀ y, get? (M := TyMapStr) Γ y ≠ none → get? (M := MapStr) θ y ≠ none) →
      closedModulo θ [] e) :
    semTyped (shiftCtx Γ) e A → semTyped Γ (.tLam e) (.all A) := by
  intro hbody δ W k θ hctx
  show exprRel δ (.all A) k W (substMap θ (.tLam e))
  simp only [substMap]
  change exprRel δ (.all A) k W (Val.tLamV (substMap θ e)).toExpr
  apply sem_val_expr_rel
  show valRel δ (.all A) k W (Val.tLamV (substMap θ e))
  simp only [valRel]
  refine ⟨substMap_closed_from_semCtxRel δ Γ W k θ e
    (hscoped θ (semCtxRel_covers δ Γ W k θ hctx)) hctx, fun τ => ?_⟩
  exact hbody (fun n => match n with | 0 => τ | n+1 => δ n) W k θ
    (semCtxRel_shift δ τ Γ W k θ hctx)

/-- Type application. The instantiated type is recovered by `exprRel_subst_ty`, which identifies
`A.subst1 B` under `δ` with `A` under `δ` extended by `interp_type B δ`. -/
theorem compat_tApp (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.all A) → semTyped Γ (.tApp e) (A.subst1 B) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (A.subst1 B) k W (.tApp (substMap θ e))
  change exprRel δ (A.subst1 B) k W (fillItem .tAppCtx (substMap θ e))
  apply bind_item δ (.all A) (A.subst1 B) k W .tAppCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  cases v with
  | tLamV body =>
    simp only [valRel] at hv
    obtain ⟨_, hbody⟩ := hv
    show exprRel δ (A.subst1 B) (k - j) W' (.tApp (.tLam body))
    apply expr_det_step_closure
    · exact det_step_tBeta body
    · have hbody_mono :=
        exprRel_mono_idx _ A (k - j) (k - j - 1) W' body (by omega) (hbody (interp_type B δ))
      exact exprRel_subst_ty δ A B (k - j - 1) W' body hbody_mono
  | _ => simp [valRel] at hv

/-- Existential introduction. The witness type is turned into the semantic witness that the value
relation at `.exist` asks for by `valRel_subst_ty`. -/
theorem compat_pack (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (A.subst1 B) → semTyped Γ (.pack e) (.exist A) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (.exist A) k W (.pack (substMap θ e))
  change exprRel δ (.exist A) k W (fillItem .packCtx (substMap θ e))
  apply bind_item δ (A.subst1 B) (.exist A) k W .packCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ (.exist A) (k - j) W' (.pack v.toExpr)
  change exprRel δ (.exist A) (k - j) W' (Val.packV v).toExpr
  apply sem_val_expr_rel
  show valRel δ (.exist A) (k - j) W' (.packV v)
  simp only [valRel]
  exact ⟨interp_type B δ, (valRel_subst_ty δ A B (k - j) W' v).mp hv⟩

/-- Existential elimination. The result type `B` is shifted in the premise so that it cannot mention
the unpacked type variable; `exprRel_shift` undoes the shift once the body has been entered. -/
theorem compat_unpack (Γ : TypingContext) (x : String) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ (.exist A) →
    semTyped (insert (M := TyMapStr) (shiftCtx Γ) x A) e₂ (B.rename (· + 1)) →
    semTyped Γ (.unpack (.bNamed x) e₁ e₂) B := by
  intro he₁ he₂ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  show exprRel δ B k W
    (.unpack (.bNamed x) (substMap θ e₁) (substMap (Iris.Std.delete (M := MapStr) θ x) e₂))
  change exprRel δ B k W
    (fillItem (.unpackCtx (.bNamed x) (substMap (Iris.Std.delete (M := MapStr) θ x) e₂))
      (substMap θ e₁))
  apply bind_item δ (.exist A) B k W
    (.unpackCtx (.bNamed x) (substMap (Iris.Std.delete (M := MapStr) θ x) e₂)) (substMap θ e₁)
    hexpr₁
  intro v j W' hj hext hv
  cases v with
  | packV v' =>
    simp only [valRel] at hv
    obtain ⟨τ, hτ⟩ := hv
    show exprRel δ B (k - j) W'
      (.unpack (.bNamed x) (.pack v'.toExpr) (substMap (Iris.Std.delete (M := MapStr) θ x) e₂))
    apply expr_det_step_closure
    · exact det_step_unpack (.bNamed x) v'.toExpr
        (substMap (Iris.Std.delete (M := MapStr) θ x) e₂) (val_isVal v')
    · -- As in `compat_lam`: substituting the unpacked value after `θ` is the same as extending `θ`.
      have hrw : subst' (.bNamed x) v'.toExpr (substMap (Iris.Std.delete (M := MapStr) θ x) e₂) =
                 substMap (Iris.Std.insert (M := MapStr) θ x v'.toExpr) e₂ := by
        have h :=
          subst'_substMap (.bNamed x) v'.toExpr θ e₂ (semCtxRel_substIsClosed δ Γ W k θ hctx)
        simpa [binderDelete] using h
      rw [hrw]
      -- Because `B` was shifted, undoing the shift on the result type needs no
      -- well-formedness side condition: the shifted `B` cannot mention `τ`.
      rw [exprRel_shift δ τ B (k - j - 1) W']
      apply he₂ (fun n => match n with | 0 => τ | n+1 => δ n) W' (k - j - 1)
                (Iris.Std.insert (M := MapStr) θ x v'.toExpr)
      constructor
      · intro y C hlook
        by_cases hxy : x = y
        · subst hxy
          rw [LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl] at hlook
          injection hlook with hlook; subst hlook
          refine ⟨v', LawfulPartialMap.get?_insert_eq (M := MapStr) rfl, ?_⟩
          exact valRel_mono_idx _ A (k - j) (k - j - 1) W' v' (by omega) hτ
        · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hlook
          rw [shiftCtx_get?] at hlook
          obtain ⟨C', hC', hCeq⟩ := Option.map_eq_some_iff.mp hlook
          subst hCeq
          obtain ⟨v'', hv''_lookup, hv''_rel⟩ := hctx.1 y C' hC'
          refine ⟨v'', ?_, ?_⟩
          · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy]; exact hv''_lookup
          · exact (valRel_shift δ τ C' (k - j - 1) W' v'').mp
              (valRel_mono δ C' k (k - j - 1) W W' v'' (by omega) hext hv''_rel)
      · intro y ey hget
        by_cases hxy : x = y
        · subst hxy
          rw [LawfulPartialMap.get?_insert_eq (M := MapStr) rfl] at hget
          injection hget with hget; subst hget
          exact valRel_closed _ A (k - j) W' v' hτ
        · rw [LawfulPartialMap.get?_insert_ne (M := MapStr) hxy] at hget
          exact hctx.2 y ey hget
  | _ => simp [valRel] at hv

/-- Pair construction. -/
theorem compat_pair (Γ : TypingContext) (e₁ e₂ : Expr) (A B : Ty) :
    semTyped Γ e₁ A → semTyped Γ e₂ B → semTyped Γ (.pair e₁ e₂) (.prod A B) := by
  intro he₁ he₂ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ (.prod A B) k W (.pair (substMap θ e₁) (substMap θ e₂))
  change exprRel δ (.prod A B) k W (fillItem (.pairRCtx (substMap θ e₁)) (substMap θ e₂))
  apply bind_item δ B (.prod A B) k W (.pairRCtx (substMap θ e₁)) (substMap θ e₂) hexpr₂
  intro v₂ j₂ W₂ hj₂ hext₂ hv₂
  show exprRel δ (.prod A B) (k - j₂) W₂ (.pair (substMap θ e₁) v₂.toExpr)
  change exprRel δ (.prod A B) (k - j₂) W₂ (fillItem (.pairLCtx v₂) (substMap θ e₁))
  have hexpr₁' : exprRel δ A (k - j₂) W₂ (substMap θ e₁) :=
    exprRel_mono δ A k (k - j₂) W W₂ (substMap θ e₁) (by omega) hext₂ hexpr₁
  apply bind_item δ A (.prod A B) (k - j₂) W₂ (.pairLCtx v₂) (substMap θ e₁) hexpr₁'
  intro v₁ j₁ W₃ hj₁ hext₃ hv₁
  show exprRel δ (.prod A B) (k - j₂ - j₁) W₃ (.pair v₁.toExpr v₂.toExpr)
  change exprRel δ (.prod A B) (k - j₂ - j₁) W₃ (Val.pairV v₁ v₂).toExpr
  apply sem_val_expr_rel
  show valRel δ (.prod A B) (k - j₂ - j₁) W₃ (.pairV v₁ v₂)
  simp only [valRel]
  exact ⟨hv₁, valRel_mono δ B (k - j₂) (k - j₂ - j₁) W₂ W₃ v₂ (by omega) hext₃ hv₂⟩

/-- First projection. -/
theorem compat_fst (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.prod A B) → semTyped Γ (.fst e) A := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ A k W (.fst (substMap θ e))
  change exprRel δ A k W (fillItem .fstCtx (substMap θ e))
  apply bind_item δ (.prod A B) A k W .fstCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  cases v with
  | pairV v₁ v₂ =>
    simp only [valRel] at hv
    obtain ⟨hv₁, hv₂⟩ := hv
    show exprRel δ A (k - j) W' (.fst (.pair v₁.toExpr v₂.toExpr))
    apply expr_det_step_closure
    · exact det_step_fst v₁.toExpr v₂.toExpr (val_isVal v₁) (val_isVal v₂)
    · exact sem_val_expr_rel δ A (k - j - 1) W' v₁
        (valRel_mono_idx δ A (k - j) (k - j - 1) W' v₁ (by omega) hv₁)
  | _ => simp [valRel] at hv

/-- Second projection. -/
theorem compat_snd (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e (.prod A B) → semTyped Γ (.snd e) B := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ B k W (.snd (substMap θ e))
  change exprRel δ B k W (fillItem .sndCtx (substMap θ e))
  apply bind_item δ (.prod A B) B k W .sndCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  cases v with
  | pairV v₁ v₂ =>
    simp only [valRel] at hv
    obtain ⟨hv₁, hv₂⟩ := hv
    show exprRel δ B (k - j) W' (.snd (.pair v₁.toExpr v₂.toExpr))
    apply expr_det_step_closure
    · exact det_step_snd v₁.toExpr v₂.toExpr (val_isVal v₁) (val_isVal v₂)
    · exact sem_val_expr_rel δ B (k - j - 1) W' v₂
        (valRel_mono_idx δ B (k - j) (k - j - 1) W' v₂ (by omega) hv₂)
  | _ => simp [valRel] at hv

/-- Left injection. -/
theorem compat_injL (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e A → semTyped Γ (.injL e) (.sum A B) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (.sum A B) k W (.injL (substMap θ e))
  change exprRel δ (.sum A B) k W (fillItem .injLCtx (substMap θ e))
  apply bind_item δ A (.sum A B) k W .injLCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ (.sum A B) (k - j) W' (.injL v.toExpr)
  change exprRel δ (.sum A B) (k - j) W' (Val.injLV v).toExpr
  apply sem_val_expr_rel
  show valRel δ (.sum A B) (k - j) W' (.injLV v)
  simp only [valRel]
  exact hv

/-- Right injection. -/
theorem compat_injR (Γ : TypingContext) (e : Expr) (A B : Ty) :
    semTyped Γ e B → semTyped Γ (.injR e) (.sum A B) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (.sum A B) k W (.injR (substMap θ e))
  change exprRel δ (.sum A B) k W (fillItem .injRCtx (substMap θ e))
  apply bind_item δ B (.sum A B) k W .injRCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ (.sum A B) (k - j) W' (.injR v.toExpr)
  change exprRel δ (.sum A B) (k - j) W' (Val.injRV v).toExpr
  apply sem_val_expr_rel
  show valRel δ (.sum A B) (k - j) W' (.injRV v)
  simp only [valRel]
  exact hv

/-- Case analysis. Each branch is a function, so after the `case` step the proof re-enters the
application pattern: bind the branch, then beta-reduce it against the injected value. -/
theorem compat_case (Γ : TypingContext) (e e₁ e₂ : Expr) (A B C : Ty) :
    semTyped Γ e (.sum A B) → semTyped Γ e₁ (.fn A C) → semTyped Γ e₂ (.fn B C) →
    semTyped Γ (.case e e₁ e₂) C := by
  intro he he₁ he₂ δ W k θ hctx
  have hexpr := he δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ C k W (.case (substMap θ e) (substMap θ e₁) (substMap θ e₂))
  change exprRel δ C k W (fillItem (.caseCtx (substMap θ e₁) (substMap θ e₂)) (substMap θ e))
  apply bind_item δ (.sum A B) C k W (.caseCtx (substMap θ e₁) (substMap θ e₂)) (substMap θ e) hexpr
  intro v j W' hj hext hv
  cases v with
  | injLV v' =>
    simp only [valRel] at hv
    show exprRel δ C (k - j) W' (.case (.injL v'.toExpr) (substMap θ e₁) (substMap θ e₂))
    apply expr_det_step_closure
    · exact det_step_caseL v'.toExpr (substMap θ e₁) (substMap θ e₂) (val_isVal v')
    · -- The argument is already a value, so the branch sits in the hole of `.appLCtx v'`.
      change exprRel δ C (k - j - 1) W' (fillItem (.appLCtx v') (substMap θ e₁))
      have hexpr₁' : exprRel δ (.fn A C) (k - j - 1) W' (substMap θ e₁) :=
        exprRel_mono δ (.fn A C) k (k - j - 1) W W' (substMap θ e₁) (by omega) hext hexpr₁
      apply bind_item δ (.fn A C) C (k - j - 1) W' (.appLCtx v') (substMap θ e₁) hexpr₁'
      intro vf jf Wf hjf hextf hvf
      cases vf with
      | lamV x body =>
        simp only [valRel] at hvf
        obtain ⟨_, hbody⟩ := hvf
        show exprRel δ C (k - j - 1 - jf) Wf (.app (.lam x body) v'.toExpr)
        apply expr_det_step_closure
        · exact det_step_beta x body v'.toExpr (val_isVal v')
        · have hv' : valRel δ A (k - j - 1 - jf - 1) Wf v' :=
            valRel_mono δ A (k - j) (k - j - 1 - jf - 1) W' Wf v' (by omega) hextf hv
          exact hbody v' 1 Wf (worldExt_refl Wf) hv'
      | _ => simp [valRel] at hvf
  | injRV v' =>
    simp only [valRel] at hv
    show exprRel δ C (k - j) W' (.case (.injR v'.toExpr) (substMap θ e₁) (substMap θ e₂))
    apply expr_det_step_closure
    · exact det_step_caseR v'.toExpr (substMap θ e₁) (substMap θ e₂) (val_isVal v')
    · change exprRel δ C (k - j - 1) W' (fillItem (.appLCtx v') (substMap θ e₂))
      have hexpr₂' : exprRel δ (.fn B C) (k - j - 1) W' (substMap θ e₂) :=
        exprRel_mono δ (.fn B C) k (k - j - 1) W W' (substMap θ e₂) (by omega) hext hexpr₂
      apply bind_item δ (.fn B C) C (k - j - 1) W' (.appLCtx v') (substMap θ e₂) hexpr₂'
      intro vf jf Wf hjf hextf hvf
      cases vf with
      | lamV x body =>
        simp only [valRel] at hvf
        obtain ⟨_, hbody⟩ := hvf
        show exprRel δ C (k - j - 1 - jf) Wf (.app (.lam x body) v'.toExpr)
        apply expr_det_step_closure
        · exact det_step_beta x body v'.toExpr (val_isVal v')
        · have hv' : valRel δ B (k - j - 1 - jf - 1) Wf v' :=
            valRel_mono δ B (k - j) (k - j - 1 - jf - 1) W' Wf v' (by omega) hextf hv
          exact hbody v' 1 Wf (worldExt_refl Wf) hv'
      | _ => simp [valRel] at hvf
  | _ => simp [valRel] at hv

/-- Rolling into a recursive type. The value relation at `.mu` guards its unfolding behind one
index, so the premise at index `k - j` is more than enough; only closedness and monotonicity are
needed. -/
theorem compat_roll (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e (Ty.subst1 A (.mu A)) → semTyped Γ (.roll e) (.mu A) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (.mu A) k W (.roll (substMap θ e))
  change exprRel δ (.mu A) k W (fillItem .rollCtx (substMap θ e))
  apply bind_item δ (Ty.subst1 A (.mu A)) (.mu A) k W .rollCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ (.mu A) (k - j) W' (.roll v.toExpr)
  change exprRel δ (.mu A) (k - j) W' (Val.rollV v).toExpr
  apply sem_val_expr_rel
  show valRel δ (.mu A) (k - j) W' (.rollV v)
  have hclosed : closed [] v.toExpr := valRel_closed δ (Ty.subst1 A (.mu A)) (k - j) W' v hv
  match h_kj : k - j with
  | 0 =>
    simp only [valRel]
    exact hclosed
  | m + 1 =>
    simp only [valRel]
    refine ⟨hclosed, fun kd => ?_⟩
    exact valRel_mono_idx δ (Ty.subst1 A (.mu A)) (k - j) (m - kd) W' v (by omega) hv

/-- Unrolling a recursive type. -/
theorem compat_unroll (Γ : TypingContext) (e : Expr) (A : Ty) :
    semTyped Γ e (.mu A) → semTyped Γ (.unroll e) (Ty.subst1 A (.mu A)) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (Ty.subst1 A (.mu A)) k W (.unroll (substMap θ e))
  change exprRel δ (Ty.subst1 A (.mu A)) k W (fillItem .unrollCtx (substMap θ e))
  apply bind_item δ (.mu A) (Ty.subst1 A (.mu A)) k W .unrollCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  cases v with
  | rollV v' =>
    show exprRel δ (Ty.subst1 A (.mu A)) (k - j) W' (.unroll (.roll v'.toExpr))
    apply expr_det_step_closure
    · exact det_step_unroll v'.toExpr (val_isVal v')
    · cases h_kj : k - j with
      | zero =>
        -- `exprRel` at index `0` is vacuous, so nothing has to be extracted from `hv`.
        exact expr_rel_zero δ (Ty.subst1 A (.mu A)) W' v'.toExpr
      | succ m =>
        have hv_inner : valRel δ (Ty.subst1 A (.mu A)) m W' v' := by
          simp only [h_kj, valRel] at hv
          exact hv.2 0
        simp only [Nat.add_sub_cancel]
        exact sem_val_expr_rel δ (Ty.subst1 A (.mu A)) m W' v' hv_inner
  | _ => simp [valRel] at hv

/-! ## First-order types

Heap invariants store first-order types, and on those the logical relation collapses: it depends on
neither the step index, the world, nor the type variable interpretation. `foValRel_valRel` is the
bridge that lets the state operations move values between the heap invariant and the relation. -/

/-- On a first-order type the logical relation coincides with `foValRel` at every index, world and
interpretation. -/
theorem foValRel_valRel (a : FoTy) (δ : TyVarInterp) (k : Nat) (W : World) (v : Val) :
    foValRel a v ↔ valRel δ a.toTy k W v := by
  induction a generalizing v with
  | int =>
    cases v with
    | litV l => cases l <;> simp [foValRel, FoTy.toTy, valRel]
    | _ => simp [foValRel, FoTy.toTy, valRel]
  | bool =>
    cases v with
    | litV l => cases l <;> simp [foValRel, FoTy.toTy, valRel]
    | _ => simp [foValRel, FoTy.toTy, valRel]
  | unit =>
    cases v with
    | litV l => cases l <;> simp [foValRel, FoTy.toTy, valRel]
    | _ => simp [foValRel, FoTy.toTy, valRel]
  | prod a b iha ihb =>
    cases v with
    | pairV v₁ v₂ =>
      simp only [foValRel, FoTy.toTy, valRel]
      exact and_congr (iha v₁) (ihb v₂)
    | litV l => cases l <;> simp [foValRel, FoTy.toTy, valRel]
    | _ => simp [foValRel, FoTy.toTy, valRel]
  | sum a b iha ihb =>
    cases v with
    | injLV v' => simp only [foValRel, FoTy.toTy, valRel]; exact iha v'
    | injRV v' => simp only [foValRel, FoTy.toTy, valRel]; exact ihb v'
    | litV l => cases l <;> simp [foValRel, FoTy.toTy, valRel]
    | _ => simp [foValRel, FoTy.toTy, valRel]

/-! ## World satisfaction -/

/-- Reads off the invariant for a location recorded in the world. -/
theorem wsat_lookup {W : World} {h : Heap} {INV : HeapInv}
    (hsat : wsat W h) (hmem : INV ∈ W) :
    ∃ v, h INV.loc = some v ∧ foValRel INV.ty v :=
  hsat.2.1 INV hmem

/-- A location the heap does not define is governed by no invariant. -/
theorem wsat_fresh_not_mem {W : World} {h : Heap} {l : Loc}
    (hsat : wsat W h) (hfresh : h l = none) : ∀ INV ∈ W, INV.loc ≠ l := by
  intro INV hmem heq
  obtain ⟨v', hlook, _⟩ := wsat_lookup hsat hmem
  rw [heq, hfresh] at hlook
  simp at hlook

/-- Allocating a fresh location extends the world with a new invariant. Disjointness is preserved
because the fresh location is governed by no existing invariant. -/
theorem wsat_alloc {W : World} {h : Heap} {l : Loc} {v : Val} {a : FoTy}
    (hsat : wsat W h) (hfresh : h l = none) (hv : foValRel a v) :
    wsat (W ++ [⟨l, a⟩]) (Heap.insert h l v) := by
  have hne : ∀ INV ∈ W, INV.loc ≠ l := wsat_fresh_not_mem hsat hfresh
  refine ⟨Heap.bounded_insert hsat.1, ?_, ?_⟩
  · intro INV hmem
    obtain hmemW | hmemNew := List.mem_append.mp hmem
    · obtain ⟨v', hlook, hrel⟩ := wsat_lookup hsat hmemW
      refine ⟨v', ?_, hrel⟩
      simp only [Heap.insert, if_neg (hne INV hmemW)]
      exact hlook
    · obtain rfl : INV = ⟨l, a⟩ := by simpa using hmemNew
      exact ⟨v, by simp [Heap.insert], hv⟩
  · intro INV₁ hmem₁ INV₂ hmem₂ hloc
    obtain h₁ | h₁ := List.mem_append.mp hmem₁ <;>
      obtain h₂ | h₂ := List.mem_append.mp hmem₂
    · exact hsat.2.2 INV₁ h₁ INV₂ h₂ hloc
    · obtain rfl : INV₂ = ⟨l, a⟩ := by simpa using h₂
      exact absurd hloc (hne INV₁ h₁)
    · obtain rfl : INV₁ = ⟨l, a⟩ := by simpa using h₁
      exact absurd hloc.symm (hne INV₂ h₂)
    · obtain rfl : INV₁ = ⟨l, a⟩ := by simpa using h₁
      obtain rfl : INV₂ = ⟨l, a⟩ := by simpa using h₂
      rfl

/-- Overwriting a location with a value of its recorded type preserves satisfaction. -/
theorem wsat_update {W : World} {h : Heap} {l : Loc} {v : Val} {a : FoTy}
    (hsat : wsat W h) (hmem : (⟨l, a⟩ : HeapInv) ∈ W) (hv : foValRel a v) :
    wsat W (Heap.insert h l v) := by
  refine ⟨Heap.bounded_insert hsat.1, ?_, hsat.2.2⟩
  intro INV hmemINV
  by_cases hloc : INV.loc = l
  · -- By the disjointness clause of `wsat`, an invariant governing `l` must be the
    -- very one we are storing through, so its type is `a`.
    obtain rfl : INV = ⟨l, a⟩ := hsat.2.2 INV hmemINV ⟨l, a⟩ hmem hloc
    exact ⟨v, by simp [Heap.insert], hv⟩
  · obtain ⟨v', hlook, hrel⟩ := wsat_lookup hsat hmemINV
    refine ⟨v', ?_, hrel⟩
    simp only [Heap.insert, if_neg hloc]
    exact hlook

/-! ## Compatibility lemmas for the state operations -/

/-- Allocation. Unlike the other operations this is not a `DetStep`: the location is chosen freely,
so the reduction is inverted with `new_nsteps_inv` instead. -/
theorem compat_new (Γ : TypingContext) (e : Expr) (a : FoTy) :
    semTyped Γ e a.toTy → semTyped Γ (.new e) (.ref a) := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ (.ref a) k W (.new (substMap θ e))
  change exprRel δ (.ref a) k W (fillItem .newCtx (substMap θ e))
  apply bind_item δ a.toTy (.ref a) k W .newCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ (.ref a) (k - j) W' (.new v.toExpr)
  unfold exprRel
  intro e' hp hp' n W'' hext' hwsat hn hred
  -- The heap is finite (a `wsat` obligation), so a fresh location exists.
  obtain ⟨hn1, l, hres, hheap, hfr⟩ :=
    new_nsteps_inv (v := v) (toVal?_toExpr v) (Heap.bounded_fresh hwsat.1) hred
  subst hn1
  refine ⟨.litV (.litLoc l), W'' ++ [⟨l, a⟩], by rw [hres]; rfl,
    ⟨[⟨l, a⟩], rfl⟩, ?_, ?_⟩
  · rw [hheap]
    refine wsat_alloc hwsat hfr ((foValRel_valRel a δ (k - j) W'' v).mpr ?_)
    exact valRel_mono_world δ a.toTy (k - j) W' W'' v hext' hv
  · show valRel δ (.ref a) (k - j - 1) (W'' ++ [⟨l, a⟩]) (.litV (.litLoc l))
    rw [valRel]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A value of reference type is a location whose invariant the world records. -/
private theorem valRel_ref_inv {δ : TyVarInterp} {a : FoTy} {k : Nat} {W : World} {v : Val}
    (hv : valRel δ (.ref a) k W v) :
    ∃ l : Loc, v = .litV (.litLoc l) ∧ (⟨l, a⟩ : HeapInv) ∈ W := by
  match v with
  | .litV (.litLoc l) => exact ⟨l, rfl, by rw [valRel] at hv; exact hv⟩
  | .litV (.litInt _) | .litV (.litBool _) | .litV .litUnit
  | .lamV _ _ | .tLamV _ | .packV _ | .pairV _ _
  | .injLV _ | .injRV _ | .rollV _ => simp [valRel] at hv

/-- Dereference. The stored value satisfies `foValRel`, which transfers to the logical relation at
any index and world by `foValRel_valRel`. -/
theorem compat_load (Γ : TypingContext) (e : Expr) (a : FoTy) :
    semTyped Γ e (.ref a) → semTyped Γ (.load e) a.toTy := by
  intro he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ a.toTy k W (.load (substMap θ e))
  change exprRel δ a.toTy k W (fillItem .loadCtx (substMap θ e))
  apply bind_item δ (.ref a) a.toTy k W .loadCtx (substMap θ e) hexpr
  intro v j W' hj hext hv
  obtain ⟨l, hveq, hmem⟩ := valRel_ref_inv hv
  subst hveq
  show exprRel δ a.toTy (k - j) W' (.load (.lit (.litLoc l)))
  unfold exprRel
  intro e' hp hp' n W'' hext' hwsat hn hred
  obtain ⟨vr, hlook, hvr⟩ := wsat_lookup hwsat (worldExt_mem hext' hmem)
  obtain ⟨hn1, hres, hheap⟩ := load_nsteps_inv (l := l) (v' := vr) rfl hlook hred
  subst hn1
  refine ⟨vr, W'', by rw [hres]; exact toVal?_toExpr vr, worldExt_refl W'',
    by rw [hheap]; exact hwsat, ?_⟩
  exact (foValRel_valRel a δ (k - j - 1) W'' vr).mp hvr

/-- Assignment. Overwriting through a recorded invariant preserves satisfaction, because the value
stored has the invariant's first-order type. -/
theorem compat_store (Γ : TypingContext) (e₁ e₂ : Expr) (a : FoTy) :
    semTyped Γ e₁ (.ref a) → semTyped Γ e₂ a.toTy →
    semTyped Γ (.store e₁ e₂) .unit := by
  intro he₁ he₂ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ .unit k W (.store (substMap θ e₁) (substMap θ e₂))
  -- Right-to-left evaluation: reduce `e₂` first, then `e₁`.
  change exprRel δ .unit k W (fillItem (.storeRCtx (substMap θ e₁)) (substMap θ e₂))
  apply bind_item δ a.toTy .unit k W (.storeRCtx (substMap θ e₁)) (substMap θ e₂) hexpr₂
  intro v₂ j₂ W₂ hj₂ hext₂ hv₂
  show exprRel δ .unit (k - j₂) W₂ (.store (substMap θ e₁) v₂.toExpr)
  change exprRel δ .unit (k - j₂) W₂ (fillItem (.storeLCtx v₂) (substMap θ e₁))
  have hexpr₁' : exprRel δ (.ref a) (k - j₂) W₂ (substMap θ e₁) :=
    exprRel_mono δ (.ref a) k (k - j₂) W W₂ (substMap θ e₁) (by omega) hext₂ hexpr₁
  apply bind_item δ (.ref a) .unit (k - j₂) W₂ (.storeLCtx v₂) (substMap θ e₁) hexpr₁'
  intro v₁ j₁ W₃ hj₁ hext₃ hv₁
  obtain ⟨l, hveq, hmem⟩ := valRel_ref_inv hv₁
  subst hveq
  show exprRel δ .unit (k - j₂ - j₁) W₃ (.store (.lit (.litLoc l)) v₂.toExpr)
  unfold exprRel
  intro e' hp hp' n W₄ hext₄ hwsat hn hred
  obtain ⟨v₀, hlook, _⟩ := wsat_lookup hwsat (worldExt_mem hext₄ hmem)
  obtain ⟨hn1, hres, hheap⟩ :=
    store_nsteps_inv (l := l) (v := v₂) (v₀ := v₀) rfl (toVal?_toExpr v₂) hlook hred
  subst hn1
  have hv₂' : foValRel a v₂ := (foValRel_valRel a δ (k - j₂) W₂ v₂).mpr hv₂
  refine ⟨.litV .litUnit, W₄, by rw [hres]; rfl, worldExt_refl W₄, ?_, ?_⟩
  · rw [hheap]
    exact wsat_update hwsat (worldExt_mem hext₄ hmem) hv₂'
  · show valRel δ .unit (k - j₂ - j₁ - 1) W₄ (.litV .litUnit)
    rw [valRel]
    trivial

/-! ## Operators and conditionals

The operand types of an operator are always `.int` or `.bool`, so the value relation pins the
operands down to literals and the operator's evaluation function computes the result outright. -/

/-- A value in the relation at `.int` is an integer literal. -/
private theorem valRel_int_inv {δ : TyVarInterp} {k : Nat} {W : World} {v : Val}
    (hv : valRel δ .int k W v) : ∃ z : Int, v = .litV (.litInt z) := by
  match v with
  | .litV (.litInt z) => exact ⟨z, rfl⟩
  | .litV (.litBool _) | .litV (.litLoc _) | .litV .litUnit
  | .lamV _ _ | .tLamV _ | .packV _ | .pairV _ _
  | .injLV _ | .injRV _ | .rollV _ => simp [valRel] at hv

/-- A value in the relation at `.bool` is a boolean literal. -/
private theorem valRel_bool_inv {δ : TyVarInterp} {k : Nat} {W : World} {v : Val}
    (hv : valRel δ .bool k W v) : ∃ b : Bool, v = .litV (.litBool b) := by
  match v with
  | .litV (.litBool b) => exact ⟨b, rfl⟩
  | .litV (.litInt _) | .litV (.litLoc _) | .litV .litUnit
  | .lamV _ _ | .tLamV _ | .packV _ | .pairV _ _
  | .injLV _ | .injRV _ | .rollV _ => simp [valRel] at hv

/-- Closes a unary-operator case: the operator step costs one index, and the result value has to be
in the relation at that reduced index. -/
private theorem unOp_step_exprRel {δ : TyVarInterp} {B : Ty} {k : Nat} {W : World} {op : UnOp}
    {v v' : Val} (hev : unOpEval op v = some v') (hv' : valRel δ B (k - 1) W v') :
    exprRel δ B k W (.unOp op v.toExpr) :=
  expr_det_step_closure δ B k W _ _ (det_step_unOp op v.toExpr v v' (toVal?_toExpr v) hev)
    (sem_val_expr_rel δ B (k - 1) W v' hv')

/-- Closes a binary-operator case; the analogue of `unOp_step_exprRel`. -/
private theorem binOp_step_exprRel {δ : TyVarInterp} {C : Ty} {k : Nat} {W : World} {op : BinOp}
    {v₁ v₂ v' : Val} (hev : binOpEval op v₁ v₂ = some v') (hv' : valRel δ C (k - 1) W v') :
    exprRel δ C k W (.binOp op v₁.toExpr v₂.toExpr) :=
  expr_det_step_closure δ C k W _ _
    (det_step_binOp op v₁.toExpr v₂.toExpr v₁ v₂ v' (toVal?_toExpr v₁) (toVal?_toExpr v₂) hev)
    (sem_val_expr_rel δ C (k - 1) W v' hv')

/-- Unary operators. -/
theorem compat_unOp (Γ : TypingContext) (op : UnOp) (e : Expr) (A B : Ty) :
    UnOpTyped op A B → semTyped Γ e A → semTyped Γ (.unOp op e) B := by
  intro hop he δ W k θ hctx
  have hexpr := he δ W k θ hctx
  show exprRel δ B k W (.unOp op (substMap θ e))
  change exprRel δ B k W (fillItem (.unOpCtx op) (substMap θ e))
  apply bind_item δ A B k W (.unOpCtx op) (substMap θ e) hexpr
  intro v j W' hj hext hv
  show exprRel δ B (k - j) W' (.unOp op v.toExpr)
  cases hop with
  | neg_typed =>
    obtain ⟨b, rfl⟩ := valRel_bool_inv hv
    exact unOp_step_exprRel (v' := .litV (.litBool (!b))) rfl (by simp [valRel])
  | minus_typed =>
    obtain ⟨z, rfl⟩ := valRel_int_inv hv
    exact unOp_step_exprRel (v' := .litV (.litInt (-z))) rfl (by simp [valRel])

/-- Binary operators. -/
theorem compat_binOp (Γ : TypingContext) (op : BinOp) (e₁ e₂ : Expr) (A B C : Ty) :
    BinOpTyped op A B C → semTyped Γ e₁ A → semTyped Γ e₂ B → semTyped Γ (.binOp op e₁ e₂) C := by
  intro hop he₁ he₂ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ C k W (.binOp op (substMap θ e₁) (substMap θ e₂))
  change exprRel δ C k W (fillItem (.binOpRCtx op (substMap θ e₁)) (substMap θ e₂))
  apply bind_item δ B C k W (.binOpRCtx op (substMap θ e₁)) (substMap θ e₂) hexpr₂
  intro v₂ j₂ W₂ hj₂ hext₂ hv₂
  show exprRel δ C (k - j₂) W₂ (.binOp op (substMap θ e₁) v₂.toExpr)
  change exprRel δ C (k - j₂) W₂ (fillItem (.binOpLCtx op v₂) (substMap θ e₁))
  have hexpr₁' : exprRel δ A (k - j₂) W₂ (substMap θ e₁) :=
    exprRel_mono δ A k (k - j₂) W W₂ (substMap θ e₁) (by omega) hext₂ hexpr₁
  apply bind_item δ A C (k - j₂) W₂ (.binOpLCtx op v₂) (substMap θ e₁) hexpr₁'
  intro v₁ j₁ W₃ hj₁ hext₃ hv₁
  obtain ⟨z₁, rfl⟩ : ∃ z : Int, v₁ = .litV (.litInt z) := by
    cases hop <;> exact valRel_int_inv hv₁
  obtain ⟨z₂, rfl⟩ : ∃ z : Int, v₂ = .litV (.litInt z) := by
    cases hop <;> exact valRel_int_inv hv₂
  show exprRel δ C (k - j₂ - j₁) W₃ (.binOp op _ _)
  cases hop with
  | plus_typed => exact binOp_step_exprRel (v' := .litV (.litInt (z₁ + z₂))) rfl (by simp [valRel])
  | minus_typed => exact binOp_step_exprRel (v' := .litV (.litInt (z₁ - z₂))) rfl (by simp [valRel])
  | mult_typed => exact binOp_step_exprRel (v' := .litV (.litInt (z₁ * z₂))) rfl (by simp [valRel])
  | lt_typed => exact binOp_step_exprRel (v' := .litV (.litBool (z₁ < z₂))) rfl (by simp [valRel])
  | le_typed => exact binOp_step_exprRel (v' := .litV (.litBool (z₁ ≤ z₂))) rfl (by simp [valRel])
  | eq_typed => exact binOp_step_exprRel (v' := .litV (.litBool (z₁ = z₂))) rfl (by simp [valRel])

/-- Conditionals. -/
theorem compat_if (Γ : TypingContext) (e₀ e₁ e₂ : Expr) (A : Ty) :
    semTyped Γ e₀ .bool → semTyped Γ e₁ A → semTyped Γ e₂ A → semTyped Γ (.ite e₀ e₁ e₂) A := by
  intro he₀ he₁ he₂ δ W k θ hctx
  have hexpr₀ := he₀ δ W k θ hctx
  have hexpr₁ := he₁ δ W k θ hctx
  have hexpr₂ := he₂ δ W k θ hctx
  show exprRel δ A k W (.ite (substMap θ e₀) (substMap θ e₁) (substMap θ e₂))
  change exprRel δ A k W (fillItem (.ifCtx (substMap θ e₁) (substMap θ e₂)) (substMap θ e₀))
  apply bind_item δ .bool A k W (.ifCtx (substMap θ e₁) (substMap θ e₂)) (substMap θ e₀) hexpr₀
  intro v j W' hj hext hv
  obtain ⟨b, rfl⟩ := valRel_bool_inv hv
  cases b with
  | true =>
    show exprRel δ A (k - j) W' (.ite (.lit (.litBool true)) (substMap θ e₁) (substMap θ e₂))
    apply expr_det_step_closure
    · exact det_step_if_true (substMap θ e₁) (substMap θ e₂)
    · exact exprRel_mono δ A k (k - j - 1) W W' (substMap θ e₁) (by omega) hext hexpr₁
  | false =>
    show exprRel δ A (k - j) W' (.ite (.lit (.litBool false)) (substMap θ e₁) (substMap θ e₂))
    apply expr_det_step_closure
    · exact det_step_if_false (substMap θ e₁) (substMap θ e₂)
    · exact exprRel_mono δ A k (k - j - 1) W W' (substMap θ e₂) (by omega) hext hexpr₂

/-! ## Soundness -/

/-- A well-typed term's free variables all lie in the context domain, so a substitution covering
that domain (up to the extra binders `Y`) leaves nothing else free. The `hscoped` premises of
`compat_lam` and `compat_tLam` are discharged with this. -/
theorem typed_closedModulo {n Γ hctx e A} (hty : SynTyped n Γ hctx e A)
    (θ : SubstMap) (Y : List String)
    (hcov : ∀ y, get? (M := TyMapStr) Γ y ≠ none → y ∈ Y ∨ get? (M := MapStr) θ y ≠ none) :
    closedModulo θ Y e := by
  -- The binder rules extend the exemption list `Y` with the bound name and delete it from `θ`;
  -- every other rule passes both unchanged to its subterms.
  induction hty generalizing θ Y with
  | typed_lit_int _ _ _ _ | typed_lit_bool _ _ _ _ | typed_lit_unit => exact trivial
  | typed_var _ _ _ x _ hlook =>
    simp [closedModulo]
    exact hcov x (by rw [hlook]; simp)
  | typed_lam _ Γ' _ x _ A' _ _ _ ih =>
    simp [closedModulo, binderDelete]
    apply ih (Iris.Std.delete (M := MapStr) θ x) (x :: Y)
    intro y hΓ'
    by_cases hxy : x = y
    · exact Or.inl (by subst hxy; exact List.Mem.head _)
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hΓ'
      obtain hy | hθ := hcov y hΓ'
      · exact Or.inl (List.Mem.tail _ hy)
      · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]
        exact Or.inr hθ
  | typed_tLam _ Γ' _ _ _ _ ih =>
    simp [closedModulo]
    apply ih θ Y
    intro y hΓ'
    exact hcov y ((shiftCtx_get?_ne_none Γ' y).mp hΓ')
  | typed_unpack _ Γ' _ x _ _ A' _ _ _ _ ih₁ ih₂ =>
    simp [closedModulo, binderDelete]
    refine ⟨ih₁ θ Y hcov, ih₂ (Iris.Std.delete (M := MapStr) θ x) (x :: Y) ?_⟩
    intro y hΓ'
    by_cases hxy : x = y
    · exact Or.inl (by subst hxy; exact List.Mem.head _)
    · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hΓ'
      obtain hy | hθ := hcov y ((shiftCtx_get?_ne_none Γ' y).mp hΓ')
      · exact Or.inl (List.Mem.tail _ hy)
      · rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]
        exact Or.inr hθ
  | typed_tApp _ _ _ _ _ _ _ _ ih | typed_pack _ _ _ _ _ _ _ _ _ ih
  | typed_fst _ _ _ _ _ _ _ ih | typed_snd _ _ _ _ _ _ _ ih
  | typed_injL _ _ _ _ _ _ _ _ ih | typed_injR _ _ _ _ _ _ _ _ ih
  | typed_unOp _ _ _ _ _ _ _ _ _ ih | typed_roll _ _ _ _ _ _ ih
  | typed_unroll _ _ _ _ _ _ ih | typed_new _ _ _ _ _ _ ih
  | typed_load _ _ _ _ _ _ ih =>
    simp [closedModulo]
    exact ih θ Y hcov
  | typed_app _ _ _ _ _ _ _ _ _ ih₁ ih₂ | typed_pair _ _ _ _ _ _ _ _ _ ih₁ ih₂
  | typed_binOp _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ | typed_store _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    simp [closedModulo]
    exact ⟨ih₁ θ Y hcov, ih₂ θ Y hcov⟩
  | typed_case _ _ _ _ _ _ _ _ _ _ _ _ ih ih₁ ih₂
  | typed_if _ _ _ _ _ _ _ _ _ _ ih ih₁ ih₂ =>
    simp [closedModulo]
    exact ⟨ih θ Y hcov, ih₁ θ Y hcov, ih₂ θ Y hcov⟩

/-- The fundamental theorem: syntactic typing implies semantic typing, one `compat_*` lemma per
rule.

No well-formedness side condition on the context is needed. The rules that descend under a type
variable binder (`typed_tLam`, `typed_unpack`) shift the context, so `semCtxRel_shift` moves the
context relation across the binder without any constraint on the context types. -/
theorem sem_soundness {n Γ hctx e A} :
    SynTyped n Γ hctx e A → semTyped Γ e A := by
  intro hty
  induction hty with
  | typed_lit_int _ _ _ z => exact compat_int _ z
  | typed_lit_bool _ _ _ b => exact compat_bool _ b
  | typed_lit_unit => exact compat_unit _
  | typed_var _ _ _ x _ hlook => exact compat_var _ x _ hlook
  | typed_lam _ Γ' _ x e_body A _ _ hbody_deriv ih =>
    refine compat_lam _ x _ A _ (fun θ hcov_θ => ?_) ih
    exact typed_closedModulo hbody_deriv (Iris.Std.delete (M := MapStr) θ x) ((.bNamed x) :b: [])
      (fun y hΓ' => by
        simp [Binder.cons]
        by_cases hxy : x = y
        · exact Or.inl hxy.symm
        · rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) hxy] at hΓ'
          rw [LawfulPartialMap.get?_delete_ne (M := MapStr) hxy]
          exact Or.inr (hcov_θ y hΓ'))
  | typed_app _ _ _ _ _ A _ _ _ ih₁ ih₂ => exact compat_app _ _ _ A _ ih₁ ih₂
  | typed_tLam _ Γ_tl _ e_tl _ hbody_deriv ih =>
    refine compat_tLam _ _ _ (fun θ hcov_θ => ?_) ih
    exact typed_closedModulo hbody_deriv θ []
      (fun y hΓ' => Or.inr (hcov_θ y ((shiftCtx_get?_ne_none Γ_tl y).mp hΓ')))
  | typed_tApp _ _ _ _ _ B _ _ ih => exact compat_tApp _ _ _ B ih
  | typed_pack _ _ _ _ _ B _ _ _ ih => exact compat_pack _ _ _ B ih
  | typed_unpack _ Γ' _ x _ _ A _ _ _ _ ih₁ ih₂ => exact compat_unpack _ x _ _ A _ ih₁ ih₂
  | typed_pair _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact compat_pair _ _ _ _ _ ih₁ ih₂
  | typed_fst _ _ _ _ _ B _ ih => exact compat_fst _ _ _ B ih
  | typed_snd _ _ _ _ A _ _ ih => exact compat_snd _ _ A _ ih
  | typed_injL _ _ _ _ _ B _ _ ih => exact compat_injL _ _ _ B ih
  | typed_injR _ _ _ _ A _ _ _ ih => exact compat_injR _ _ A _ ih
  | typed_case _ _ _ _ _ _ A B _ _ _ _ ih ih₁ ih₂ => exact compat_case _ _ _ _ A B _ ih ih₁ ih₂
  | typed_unOp _ _ _ _ _ A _ hop _ ih => exact compat_unOp _ _ _ A _ hop ih
  | typed_binOp _ _ _ _ _ _ A B _ hop _ _ ih₁ ih₂ => exact compat_binOp _ _ _ _ A B _ hop ih₁ ih₂
  | typed_if _ _ _ _ _ _ _ _ _ _ ih₀ ih₁ ih₂ => exact compat_if _ _ _ _ _ ih₀ ih₁ ih₂
  | typed_roll _ _ _ _ _ _ ih => exact compat_roll _ _ _ ih
  | typed_unroll _ _ _ _ _ _ ih => exact compat_unroll _ _ _ ih
  | typed_new _ _ _ _ _ _ ih => exact compat_new _ _ _ ih
  | typed_load _ _ _ _ _ _ ih => exact compat_load _ _ _ ih
  | typed_store _ _ _ _ _ _ _ _ ih₁ ih₂ => exact compat_store _ _ _ _ ih₁ ih₂

/-! ## Type safety -/

/-- The semantic type containing every closed value. A closed program has no free type variables, so
which semantic type the interpretation supplies is immaterial; this is the cheapest one to build. -/
private def anySemType : SemType where
  rel _ _ v := SystemFMuState.closed [] v.toExpr
  closed_val := by intros; assumption
  mono := by intros; assumption
  mono_world := by intros; assumption

/-- The interpretation used to instantiate `semTyped` for a closed program. -/
private def anyTyVarInterp : TyVarInterp := fun _ => anySemType

/-- Type safety: a well-typed closed program never gets stuck. Any complete reduction from it ends
in a value, since `semTyped` at index `n + 1` covers reductions of length `n`. -/
theorem type_safety {e e' : Expr} {A : Ty} {n h'} :
    SynTyped 0 (PartialMap.empty (M := TyMapStr) (V := Ty)) [] e A →
    redNsteps n e Heap.empty e' h' → Expr.isVal e' := by
  intro hty hred
  have hempty : semCtxRel anyTyVarInterp (PartialMap.empty (M := TyMapStr) (V := Ty)) [] (n + 1)
      (PartialMap.empty (M := MapStr) (V := Expr)) := by
    refine ⟨fun x A' hlook => ?_, fun x e hget => ?_⟩
    · simp [get?, PartialMap.empty] at hlook
    · simp [get?, PartialMap.empty] at hget
  have hexpr := sem_soundness hty anyTyVarInterp [] (n + 1) _ hempty
  rw [substMap_empty e] at hexpr
  unfold exprRel at hexpr
  have hextW : worldExt ([] : World) [] := ⟨[], (List.append_nil []).symm⟩
  have hwsat : wsat ([] : World) Heap.empty :=
    ⟨Heap.bounded_empty,
     fun _ hmem => absurd hmem List.not_mem_nil,
     fun _ hmem => absurd hmem List.not_mem_nil⟩
  obtain ⟨v, _, hval, _, _, _⟩ :=
    hexpr e' Heap.empty h' n [] hextW hwsat (Nat.lt_succ_of_le Nat.le.refl) hred
  exact toVal?_isVal hval

end SystemFMuState
