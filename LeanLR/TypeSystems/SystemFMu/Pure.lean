import LeanLR.TypeSystems.SystemFMu.Lang

/-!
# System F with recursive types: pure execution

Deterministic steps, `n`-step reduction, and the inversion lemmas that pin down the unique way a
reducible expression decomposes into an evaluation context and a redex. This is
`SystemFMuState.Execution` with the heap removed, so every reduction is deterministic and the
state-specific inversion lemmas disappear.
-/

namespace SystemFMu

/-! ## Deterministic steps and `n`-step reduction -/

/-- `DetStep e₁ e₂` says `e₁` is reducible and every reduction of it yields `e₂`. -/
structure DetStep (e₁ e₂ : Expr) : Prop where
  safe : reducible e₁
  det : ∀ e₂', ContextualStep e₁ e₂' → e₂' = e₂

/-- `Nsteps n e e'` chains exactly `n` contextual steps from `e` to `e'`. -/
inductive Nsteps : Nat → Expr → Expr → Prop where
  | zero : Nsteps 0 e e
  | step : ContextualStep e₁ e₂ → Nsteps n e₂ e₃ → Nsteps (n + 1) e₁ e₃

/-- A complete reduction: `n` steps ending in an irreducible expression. -/
def redNsteps (n : Nat) (e : Expr) (e' : Expr) : Prop :=
  Nsteps n e e' ∧ irreducible e'

/-- `DetSteps n e e'` chains exactly `n` deterministic steps. Rocq writes this as
`nsteps det_step n`. -/
inductive DetSteps : Nat → Expr → Expr → Prop where
  | zero : DetSteps 0 e e
  | step : DetStep e₁ e₂ → DetSteps n e₂ e₃ → DetSteps (n + 1) e₁ e₃

/-! ## Contextual steps -/

/-- A redex reduction is a contextual step under the empty context. -/
theorem base_contextual_step {e₁ e₂ : Expr} :
    BaseStep e₁ e₂ → ContextualStep e₁ e₂ :=
  fun hb => .ectxStep [] e₁ e₂ hb

/-- Contextual steps are closed under plugging into a further evaluation context. -/
theorem fill_contextual_step {K : Ectx} {e₁ e₂ : Expr} :
    ContextualStep e₁ e₂ → ContextualStep (fill K e₁) (fill K e₂) := by
  intro ⟨K', e₁', e₂', hb⟩
  have hfl : ∀ (A B : Ectx) (x : Expr), fill (A ++ B) x = fill B (fill A x) := by
    intro A B x
    simp [fill, List.foldl_append]
  rw [← hfl K' K e₁', ← hfl K' K e₂']
  exact .ectxStep (K' ++ K) e₁' e₂' hb

/-- Splits a contextual step into its evaluation context and the underlying redex reduction. -/
theorem contextual_step_inv {expr e' : Expr}
    (hstep : ContextualStep expr e') :
    ∃ (K : Ectx) (e₁ e₂ : Expr),
      fill K e₁ = expr ∧ fill K e₂ = e' ∧ BaseStep e₁ e₂ := by
  cases hstep with
  | ectxStep K e₁ e₂ hb => exact ⟨K, e₁, e₂, rfl, rfl, hb⟩

/-- Values are not redexes. -/
theorem val_no_base_step {e e' : Expr} :
    Expr.isVal e → ¬ BaseStep e e' := by
  intro hval hstep
  cases hstep <;> simp [Expr.isVal] at hval

/-! ## Values and evaluation contexts -/

/-- The expression underlying a value is a value. -/
theorem val_isVal : ∀ v : Val, Expr.isVal v.toExpr
  | .litV _ | .lamV _ _ | .tLamV _ => trivial
  | .packV v | .injLV v | .injRV v | .rollV v => val_isVal v
  | .pairV v₁ v₂ => ⟨val_isVal v₁, val_isVal v₂⟩

/-- An expression that converts to a value is that value's expression. -/
theorem toVal?_eq {e : Expr} {v : Val} (h : Expr.toVal? e = some v) : e = v.toExpr := by
  induction e generalizing v with
  | lit _ | lam _ _ | tLam _ =>
    simp only [Expr.toVal?, Option.some.injEq] at h
    subst h
    rfl
  | pack e ih | injL e ih | injR e ih | roll e ih =>
    simp only [Expr.toVal?, Option.map_eq_some_iff] at h
    obtain ⟨v', hv', rfl⟩ := h
    simp only [Val.toExpr, ih hv']
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.toVal?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h
    simp only [Val.toExpr, ih₁ hv₁, ih₂ hv₂]
  | _ => simp [Expr.toVal?] at h

/-- `Expr.toVal?` only succeeds on values. -/
theorem toVal?_isVal {e : Expr} {v : Val} (h : Expr.toVal? e = some v) : Expr.isVal e :=
  toVal?_eq h ▸ val_isVal v

/-- Plugging into a frame never creates a value out of a non-value. -/
theorem fillItem_isVal_imp (ki : EctxItem) (e : Expr)
    (hval : Expr.isVal (fillItem ki e)) : Expr.isVal e := by
  cases ki <;> simp [fillItem, Expr.isVal] at hval <;>
    first | exact hval | exact hval.1 | exact hval.2

/-- Plugging into a context never creates a value out of a non-value. -/
theorem fill_isVal_imp : ∀ (K : Ectx) (e : Expr), Expr.isVal (fill K e) → Expr.isVal e
  | [], _, hval => hval
  | ki :: K', e, hval => by
    have h : fill (ki :: K') e = fill K' (fillItem ki e) := by simp [fill, List.foldl]
    rw [h] at hval
    exact fillItem_isVal_imp ki e (fill_isVal_imp K' _ hval)

/-- No redex sits inside a value. -/
theorem fill_val_base_step_absurd (K : Ectx) (e₁ e₂ : Expr)
    (hval : Expr.isVal (fill K e₁)) (hbase : BaseStep e₁ e₂) : False :=
  val_no_base_step (fill_isVal_imp K e₁ hval) hbase

/-- A value expression cannot start a contextual step. -/
private theorem val_no_contextual_step {v : Val} {e' : Expr} :
    ¬ ContextualStep v.toExpr e' := fun hstep => by
  obtain ⟨K, ea, eb, hfill, _, hbase⟩ := contextual_step_inv hstep
  exact fill_val_base_step_absurd K ea eb (hfill ▸ val_isVal v) hbase

/-- Peels the outermost frame off a context. -/
theorem fill_last (init : Ectx) (last : EctxItem) (e : Expr) :
    fill (init ++ [last]) e = fillItem last (fill init e) := by
  simp [fill, List.foldl_append, List.foldl]

/-- Every non-empty context has an outermost frame. -/
theorem list_last_split (l : Ectx) (hne : l ≠ []) :
    ∃ (init : Ectx) (last : EctxItem), l = init ++ [last] :=
  match List.eq_nil_or_concat l with
  | .inl hnil => absurd hnil hne
  | .inr ⟨init, last, heq⟩ => ⟨init, last, by simpa using heq⟩

/-! ## Unique decomposition -/

/-- Unique decomposition, in the form every redex shape needs it. If each way of writing `redex`
as a frame around a subterm forces that subterm to be a value — `hsub`, the "sub-redexes are
values" side condition — then `redex` admits no decomposition other than the trivial one: any
context whose hole reduces must be empty, and the hole must be `redex` itself.

The argument is by contradiction on `K ≠ []`. Peeling the outermost frame off `K` exhibits
`fill init ea` as a subterm of `redex` in evaluation position, so `hsub` makes it a value; but
`ea` reduces, and values are not redexes. -/
private theorem unique_decomp_of_subredexes_val {K : Ectx} {ea eb redex : Expr}
    (hsub : ∀ Ki e, fillItem Ki e = redex → Expr.isVal e)
    (hfill : fill K ea = redex) (hbase : BaseStep ea eb) :
    K = [] ∧ ea = redex := by
  suffices hK : K = [] by
    subst hK
    exact ⟨rfl, by simpa [fill] using hfill⟩
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨init, last, hKsplit⟩ := list_last_split K hne
  rw [hKsplit, fill_last] at hfill
  exact val_no_base_step (fill_isVal_imp init ea (hsub last _ hfill)) hbase

/-! ## Deterministic steps -/

/-- Builds a `DetStep` from the three facts every deterministic redex satisfies: its sub-redexes
are values (`hsub`), it reduces to `e'` (`hbase`), and that is its only reduction (`hdet`).
Uniqueness of the decomposition then upgrades redex determinism to whole-program determinism. -/
private theorem DetStep.of_base {redex e' : Expr}
    (hsub : ∀ Ki e, fillItem Ki e = redex → Expr.isVal e)
    (hbase : BaseStep redex e')
    (hdet : ∀ e'', BaseStep redex e'' → e'' = e') :
    DetStep redex e' where
  safe := ⟨e', base_contextual_step hbase⟩
  det e'' hcs := by
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hb⟩ := contextual_step_inv hcs
    obtain ⟨rfl, rfl⟩ := unique_decomp_of_subredexes_val hsub hfill₁ hb
    obtain rfl := hdet eb hb
    exact by simpa [fill] using hfill₂.symm

/-- Beta reduction of a term abstraction. -/
theorem det_step_beta (x : Binder) (e e₂ : Expr) (hval : Expr.isVal e₂) :
    DetStep (.app (.lam x e) e₂) (subst' x e₂ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.betaS x e e₂ hval)
    (by intro _ hb; cases hb; exact rfl)

/-- Beta reduction of a type abstraction; types are erased, so the body is returned unchanged. -/
theorem det_step_tBeta (e : Expr) : DetStep (.tApp (.tLam e)) e :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.tBetaS e)
    (by intro _ hb; cases hb; exact rfl)

/-- Unpacking an existential substitutes the packed value into the body. -/
theorem det_step_unpack (x : Binder) (e₁ e₂ : Expr) (hval : Expr.isVal e₁) :
    DetStep (.unpack x (.pack e₁) e₂) (subst' x e₁ e₂) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.unpackS x e₁ e₂ hval)
    (by intro _ hb; cases hb; exact rfl)

/-- `if true then e₁ else e₂` takes the first branch. -/
theorem det_step_if_true (e₁ e₂ : Expr) : DetStep (.ite (.lit (.litBool true)) e₁ e₂) e₁ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.ifTrueS e₁ e₂)
    (by intro _ hb; cases hb; exact rfl)

/-- `if false then e₁ else e₂` takes the second branch. -/
theorem det_step_if_false (e₁ e₂ : Expr) : DetStep (.ite (.lit (.litBool false)) e₁ e₂) e₂ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.ifFalseS e₁ e₂)
    (by intro _ hb; cases hb; exact rfl)

/-- First projection of a pair of values. -/
theorem det_step_fst (e₁ e₂ : Expr) (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂) :
    DetStep (.fst (.pair e₁ e₂)) e₁ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.fstS e₁ e₂ hv₁ hv₂)
    (by intro _ hb; cases hb; exact rfl)

/-- Second projection of a pair of values. -/
theorem det_step_snd (e₁ e₂ : Expr) (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂) :
    DetStep (.snd (.pair e₁ e₂)) e₂ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.sndS e₁ e₂ hv₁ hv₂)
    (by intro _ hb; cases hb; exact rfl)

/-- A `case` on a left injection applies the left branch. -/
theorem det_step_caseL (e e₁ e₂ : Expr) (hv : Expr.isVal e) :
    DetStep (.case (.injL e) e₁ e₂) (.app e₁ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.caseLS e e₁ e₂ hv)
    (by intro _ hb; cases hb; exact rfl)

/-- A `case` on a right injection applies the right branch. -/
theorem det_step_caseR (e e₁ e₂ : Expr) (hv : Expr.isVal e) :
    DetStep (.case (.injR e) e₁ e₂) (.app e₂ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.caseRS e e₁ e₂ hv)
    (by intro _ hb; cases hb; exact rfl)

/-- `unroll (roll v)` cancels. -/
theorem det_step_unroll (e : Expr) (hv : Expr.isVal e) : DetStep (.unroll (.roll e)) e :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (.unrollS e hv)
    (by intro _ hb; cases hb; exact rfl)

/-- A unary operator applied to a value it accepts. -/
theorem det_step_unOp (op : UnOp) (e : Expr) (v v' : Val)
    (htv : Expr.toVal? e = some v) (hev : unOpEval op v = some v') :
    DetStep (.unOp op e) v'.toExpr :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, toVal?_isVal htv])
    (.unOpS op e v v' htv hev)
    (by
      intro _ hb
      cases hb with
      | unOpS _ _ _ _ htv' hev' =>
        rw [htv] at htv'
        cases htv'
        rw [hev] at hev'
        cases hev'
        exact rfl)

/-- A binary operator applied to values it accepts. -/
theorem det_step_binOp (op : BinOp) (e₁ e₂ : Expr) (v₁ v₂ v' : Val)
    (htv₁ : Expr.toVal? e₁ = some v₁) (htv₂ : Expr.toVal? e₂ = some v₂)
    (hev : binOpEval op v₁ v₂ = some v') :
    DetStep (.binOp op e₁ e₂) v'.toExpr :=
  .of_base
    (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, toVal?_isVal htv₁, toVal?_isVal htv₂])
    (.binOpS op e₁ e₂ v₁ v₂ v' htv₁ htv₂ hev)
    (by
      intro _ hb
      cases hb with
      | binOpS _ _ _ _ _ _ htv₁' htv₂' hev' =>
        rw [htv₁] at htv₁'
        cases htv₁'
        rw [htv₂] at htv₂'
        cases htv₂'
        rw [hev] at hev'
        cases hev'
        exact rfl)

/-! ## `n`-step lemmas -/

/-- Prepends a contextual step to a complete reduction. -/
theorem contextual_step_red_nsteps {n : Nat} {e e' e'' : Expr} :
    ContextualStep e e' → redNsteps n e' e'' → redNsteps (n + 1) e e'' := by
  intro hstep ⟨hn, hi⟩
  exact ⟨.step hstep hn, hi⟩

/-- A complete reduction out of a deterministic redex must begin with that redex's step. -/
theorem det_step_red {e e' e'' : Expr} {n : Nat} :
    DetStep e e' → redNsteps n e e'' → 1 ≤ n ∧ redNsteps (n - 1) e' e'' := by
  intro ⟨hsafe, hdet⟩ ⟨hn, hi⟩
  cases hn with
  | zero => exact absurd hsafe hi
  | step hstep hn' =>
    obtain rfl := hdet _ hstep
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), hn', hi⟩

/-! ## `lang.v` metatheory

The evaluation-context metatheory of `lang.v`: value inversions, the unique-decomposition
apparatus (`step_by_val` and its consequences), and the reducibility vocabulary built on it. -/

@[simp] theorem toVal?_toExpr : ∀ v : Val, v.toExpr.toVal? = some v
  | .litV _ | .lamV _ _ | .tLamV _ => rfl
  | .packV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]
  | .injLV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]
  | .injRV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]
  | .rollV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]
  | .pairV v₁ v₂ => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v₁, toVal?_toExpr v₂]

theorem toExpr_inj {v w : Val} (h : v.toExpr = w.toExpr) : v = w := by
  have hv := toVal?_toExpr v
  rw [h, toVal?_toExpr w] at hv
  exact (Option.some.injEq _ _ ▸ hv).symm

@[simp] theorem toExpr_inj_iff {v w : Val} : v.toExpr = w.toExpr ↔ v = w :=
  ⟨toExpr_inj, fun h => h ▸ rfl⟩

/-- In the form the port uses: a value expression is some `Val`. -/
theorem isVal_exists {e : Expr} (h : Expr.isVal e) : ∃ v : Val, e = v.toExpr := by
  induction e with
  | lit l => exact ⟨.litV l, rfl⟩
  | lam x e => exact ⟨.lamV x e, rfl⟩
  | tLam e => exact ⟨.tLamV e, rfl⟩
  | pack e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.packV v, rfl⟩
  | injL e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.injLV v, rfl⟩
  | injR e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.injRV v, rfl⟩
  | roll e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.rollV v, rfl⟩
  | pair e₁ e₂ ih₁ ih₂ =>
    obtain ⟨v₁, rfl⟩ := ih₁ h.1
    obtain ⟨v₂, rfl⟩ := ih₂ h.2
    exact ⟨.pairV v₁ v₂, rfl⟩
  | _ => exact h.elim

theorem isVal_spec {e : Expr} : Expr.isVal e ↔ ∃ v : Val, e.toVal? = some v := by
  refine ⟨fun h => ?_, fun ⟨_, hv⟩ => toVal?_isVal hv⟩
  obtain ⟨v, rfl⟩ := isVal_exists h
  exact ⟨v, toVal?_toExpr v⟩

/-- `Expr.toVal?` fails exactly on non-values; this is how the port reads Rocq's
`to_val e = None`. -/
theorem toVal?_eq_none_iff {e : Expr} : e.toVal? = none ↔ ¬ Expr.isVal e := by
  refine ⟨fun h hv => ?_, fun h => ?_⟩
  · obtain ⟨v, hv'⟩ := isVal_spec.mp hv
    rw [h] at hv'
    simp at hv'
  · cases hv : e.toVal? with
    | none => rfl
    | some v => exact absurd (toVal?_isVal hv) h

/-! ### Value inversions -/

theorem toExpr_lit_inv {v : Val} {l : BaseLit} (h : v.toExpr = .lit l) : v = .litV l :=
  toExpr_inj (w := .litV l) h

theorem toExpr_pair_inv {v v₁ v₂ : Val} (h : v.toExpr = .pair v₁.toExpr v₂.toExpr) :
    v = .pairV v₁ v₂ :=
  toExpr_inj (w := .pairV v₁ v₂) h

theorem toExpr_injL_inv {v v' : Val} (h : v.toExpr = .injL v'.toExpr) : v = .injLV v' :=
  toExpr_inj (w := .injLV v') h

theorem toExpr_injR_inv {v v' : Val} (h : v.toExpr = .injR v'.toExpr) : v = .injRV v' :=
  toExpr_inj (w := .injRV v') h

/-- A redex is never a value. -/
theorem base_step_not_isVal {e e' : Expr} (h : BaseStep e e') : ¬ Expr.isVal e :=
  fun hv => val_no_base_step hv h

/-! ### Evaluation contexts -/

def emptyEctx : Ectx := []

/-- `compEctx K₁ K₂` plugs `K₂` into the hole of `K₁`. -/
def compEctx (K₁ K₂ : Ectx) : Ectx := K₂ ++ K₁

theorem fill_app (K₁ K₂ : Ectx) (e : Expr) : fill (K₁ ++ K₂) e = fill K₂ (fill K₁ e) := by
  simp [fill, List.foldl_append]

@[simp] theorem fill_empty (e : Expr) : fill emptyEctx e = e := rfl

theorem fill_comp (K₁ K₂ : Ectx) (e : Expr) : fill K₁ (fill K₂ e) = fill (compEctx K₁ K₂) e :=
  (fill_app K₂ K₁ e).symm

/-- Peels the innermost frame off a context. -/
theorem fill_cons (Ki : EctxItem) (K : Ectx) (e : Expr) :
    fill (Ki :: K) e = fill K (fillItem Ki e) := by
  simp [fill, List.foldl]

theorem fillItem_inj (Ki : EctxItem) {e e' : Expr} (h : fillItem Ki e = fillItem Ki e') :
    e = e' := by
  cases Ki <;> simp_all [fillItem]

theorem fill_inj (K : Ectx) {e e' : Expr} (h : fill K e = fill K e') : e = e' := by
  induction K generalizing e e' with
  | nil => exact h
  | cons Ki K ih => exact fillItem_inj Ki (ih (by rwa [fill_cons, fill_cons] at h))

theorem fillItem_isVal (Ki : EctxItem) (e : Expr) (h : Expr.isVal (fillItem Ki e)) :
    Expr.isVal e :=
  fillItem_isVal_imp Ki e h

theorem fill_isVal (K : Ectx) (e : Expr) (h : Expr.isVal (fill K e)) : Expr.isVal e :=
  fill_isVal_imp K e h

theorem fill_not_isVal (K : Ectx) {e : Expr} (h : ¬ Expr.isVal e) : ¬ Expr.isVal (fill K e) :=
  fun hv => h (fill_isVal_imp K e hv)

/-- Whether a redex steps to a value does not depend on which
reduction is taken. -/
theorem base_step_to_isVal {e e₂ e₂' : Expr} (h₁ : BaseStep e e₂) (h₂ : BaseStep e e₂')
    (hval : Expr.isVal e₂) : Expr.isVal e₂' := by
  cases h₁ <;> cases h₂ <;> simp_all [val_isVal] <;> trivial

theorem fillItem_not_isVal (Ki : EctxItem) {e : Expr} (h : ¬ Expr.isVal e) :
    ¬ Expr.isVal (fillItem Ki e) :=
  fun hv => h (fillItem_isVal Ki e hv)

/-! ### Unique decomposition -/

/-- If plugging `e` into a frame yields a redex, `e` is a value. -/
theorem base_ectxi_step_isVal {Ki : EctxItem} {e e₂ : Expr} (h : BaseStep (fillItem Ki e) e₂) :
    Expr.isVal e := by
  cases Ki <;> simp only [fillItem] at h <;> cases h <;>
    first
      | trivial
      | assumption
      | (rename_i hv _ _; exact toVal?_isVal hv)
      | (rename_i hv _; exact toVal?_isVal hv)
      | (rename_i hv; exact toVal?_isVal hv)
      | exact ⟨‹_›, ‹_›⟩

/-- A frame is determined by the term it is plugged into, as long
as the hole is not a value. -/
theorem fillItem_no_isVal_inj {Ki₁ Ki₂ : EctxItem} {e₁ e₂ : Expr}
    (h₁ : ¬ Expr.isVal e₁) (h₂ : ¬ Expr.isVal e₂)
    (heq : fillItem Ki₁ e₁ = fillItem Ki₂ e₂) : Ki₁ = Ki₂ := by
  cases Ki₁ <;> cases Ki₂ <;> simp_all [fillItem] <;> grind [val_isVal]

/-- Reverse (snoc) induction on evaluation contexts, which is how `step_by_val` peels frames. -/
private theorem ectx_rev_induction {motive : Ectx → Prop} (hnil : motive [])
    (hsnoc : ∀ (K : Ectx) (Ki : EctxItem), motive K → motive (K ++ [Ki])) : ∀ K, motive K := by
  intro K
  have h : ∀ L : Ectx, motive L.reverse := by
    intro L
    induction L with
    | nil => exact hnil
    | cons Ki L ih => simpa using hsnoc L.reverse Ki ih
  simpa using h K.reverse

/-- A redex found somewhere in `fill K e`, with `e` not a value, must sit
inside `e`. -/
theorem step_by_val {K Kred : Ectx} {e eRedex e₂ : Expr}
    (hfill : fill K e = fill Kred eRedex) (hnv : ¬ Expr.isVal e)
    (hstep : BaseStep eRedex e₂) : ∃ K', Kred = compEctx K K' := by
  suffices h : ∀ K : Ectx, ∀ Kred : Ectx, fill K e = fill Kred eRedex →
      ∃ K', Kred = compEctx K K' from h K Kred hfill
  intro K
  induction K using ectx_rev_induction with
  | hnil => exact fun Kred _ => ⟨Kred, by simp [compEctx]⟩
  | hsnoc K Ki ih =>
    intro Kred hf
    by_cases hKred : Kred = []
    · subst hKred
      rw [fill_last] at hf
      have hstep' : BaseStep (fillItem Ki (fill K e)) e₂ := by rw [hf]; exact hstep
      exact absurd (fill_isVal_imp K e (base_ectxi_step_isVal hstep')) hnv
    · obtain ⟨Kred₀, Ki', rfl⟩ := list_last_split Kred hKred
      rw [fill_last, fill_last] at hf
      have hKi : Ki = Ki' :=
        fillItem_no_isVal_inj (fill_not_isVal K hnv)
          (fill_not_isVal Kred₀ (base_step_not_isVal hstep)) hf
      subst hKi
      obtain ⟨K'', hK''⟩ := ih Kred₀ (fillItem_inj Ki hf)
      refine ⟨K'', ?_⟩
      simp only [compEctx] at hK'' ⊢
      rw [hK'', List.append_assoc]

/-- Wrapping a non-value in a context creates no new redexes. -/
theorem base_ectx_step_isVal {K : Ectx} {e e₂ : Expr} (h : BaseStep (fill K e) e₂) :
    Expr.isVal e ∨ K = [] := by
  by_cases hK : K = []
  · exact Or.inr hK
  · obtain ⟨init, last, rfl⟩ := list_last_split K hK
    rw [fill_last] at h
    exact Or.inl (fill_isVal_imp init e (base_ectxi_step_isVal h))

/-- A step that preserves a surrounding context happens
entirely inside the hole. -/
theorem contextual_step_ectx_inv {K : Ectx} {e e' : Expr} (hnv : ¬ Expr.isVal e)
    (h : ContextualStep (fill K e) (fill K e')) : ContextualStep e e' := by
  obtain ⟨K₀, ea, eb, hf₁, hf₂, hb⟩ := contextual_step_inv h
  obtain ⟨K'', rfl⟩ := step_by_val hf₁.symm hnv hb
  simp only [compEctx] at hf₁ hf₂
  rw [fill_app] at hf₁ hf₂
  rw [← fill_inj K hf₁, ← fill_inj K hf₂]
  exact .ectxStep K'' ea eb hb

/-! ### Reducibility -/

def baseReducible (e : Expr) : Prop := ∃ e', BaseStep e e'

def baseIrreducible (e : Expr) : Prop := ∀ e', ¬ BaseStep e e'

def baseStuck (e : Expr) : Prop := ¬ Expr.isVal e ∧ baseIrreducible e

def stuck (e : Expr) : Prop := ¬ Expr.isVal e ∧ irreducible e

def notStuck (e : Expr) : Prop := Expr.isVal e ∨ reducible e

theorem base_reducible_contextual_step_ectx {K : Ectx} {e₁ e₂ : Expr}
    (hred : baseReducible e₁) (h : ContextualStep (fill K e₁) e₂) :
    ∃ e₂', e₂ = fill K e₂' ∧ BaseStep e₁ e₂' := by
  obtain ⟨e₂'', hbstep⟩ := hred
  obtain ⟨K', ea, eb, hf₁, hf₂, hb⟩ := contextual_step_inv h
  obtain ⟨K'', rfl⟩ := step_by_val hf₁.symm (base_step_not_isVal hbstep) hb
  simp only [compEctx] at hf₁ hf₂
  rw [fill_app] at hf₁ hf₂
  have h₁ : fill K'' ea = e₁ := fill_inj K hf₁
  rcases base_ectx_step_isVal (K := K'') (h₁ ▸ hbstep) with hval | hnil
  · exact absurd hb (val_no_base_step hval)
  · subst hnil
    exact ⟨eb, hf₂.symm, h₁ ▸ hb⟩

theorem base_reducible_contextual_step {e₁ e₂ : Expr} (hred : baseReducible e₁)
    (h : ContextualStep e₁ e₂) : BaseStep e₁ e₂ := by
  obtain ⟨e₂', heq, hb⟩ := base_reducible_contextual_step_ectx (K := []) hred h
  rw [heq]
  exact hb

theorem base_step_not_stuck {e e' : Expr} (h : BaseStep e e') : notStuck e :=
  Or.inr ⟨e', base_contextual_step h⟩

/-- Only non-values step. -/
theorem val_stuck {e e' : Expr} (h : ContextualStep e e') : ¬ Expr.isVal e := by
  obtain ⟨K, ea, eb, rfl, _, hb⟩ := contextual_step_inv h
  exact fun hv => fill_val_base_step_absurd K ea eb hv hb

theorem not_reducible {e : Expr} : ¬ reducible e ↔ irreducible e := Iff.rfl

theorem reducible_not_isVal {e : Expr} (h : reducible e) : ¬ Expr.isVal e :=
  let ⟨_, hs⟩ := h; val_stuck hs

theorem val_irreducible {e : Expr} (h : Expr.isVal e) : irreducible e :=
  fun ⟨_, hs⟩ => val_stuck hs h

theorem irreducible_fill {K : Ectx} {e : Expr} (h : irreducible (fill K e)) : irreducible e :=
  fun ⟨e', hs⟩ => h ⟨fill K e', fill_contextual_step hs⟩

theorem base_reducible_reducible {e : Expr} (h : baseReducible e) : reducible e :=
  let ⟨e', hb⟩ := h; ⟨e', base_contextual_step hb⟩

/-! ## Lifting reduction through contexts

`pure.v`'s remaining lemmas: the decomposition case analysis for a step under a context, the
`n`-step inversions it feeds, and the congruence lemmas that lift a `DetStep` through a frame. -/

/-- Inversion of `Nsteps` at zero. -/
theorem nsteps_zero_inv {e e' : Expr} (h : Nsteps 0 e e') : e' = e := by
  cases h; rfl

/-- Inversion of `Nsteps` at a successor. -/
theorem nsteps_succ_inv {n : Nat} {e e' : Expr} (h : Nsteps (n + 1) e e') :
    ∃ e₂, ContextualStep e e₂ ∧ Nsteps n e₂ e' := by
  cases h with
  | step h₁ h₂ => exact ⟨_, h₁, h₂⟩

/-- A redex that reduces, and reduces only one way. -/
structure DetBaseStep (e₁ e₂ : Expr) : Prop where
  safe : baseReducible e₁
  det : ∀ e₂', BaseStep e₁ e₂' → e₂' = e₂

/-- Redex determinism upgrades to whole-program determinism,
because a reducible redex can only step at the top. -/
theorem DetBaseStep.detStep {e₁ e₂ : Expr} (h : DetBaseStep e₁ e₂) : DetStep e₁ e₂ where
  safe := base_reducible_reducible h.safe
  det _ hcs := h.det _ (base_reducible_contextual_step h.safe hcs)

/-- A step of `fill K e` either happens inside `e`, or `e` is
already a value and the step happens in `K`. -/
theorem contextual_ectx_step_case {K : Ectx} {e e' : Expr}
    (h : ContextualStep (fill K e) e') :
    (∃ e'', e' = fill K e'' ∧ ContextualStep e e'') ∨ Expr.isVal e := by
  by_cases hv : Expr.isVal e
  · exact Or.inr hv
  refine Or.inl ?_
  obtain ⟨K₀, ea, eb, hf₁, hf₂, hb⟩ := contextual_step_inv h
  obtain ⟨K'', rfl⟩ := step_by_val hf₁.symm hv hb
  simp only [compEctx] at hf₁ hf₂
  rw [fill_app] at hf₁ hf₂
  exact ⟨fill K'' eb, hf₂.symm, fill_inj K hf₁ ▸ .ectxStep K'' ea eb hb⟩

theorem fill_reducible (K : Ectx) {e : Expr} (h : reducible e) : reducible (fill K e) :=
  let ⟨e', hs⟩ := h; ⟨fill K e', fill_contextual_step hs⟩

/-- If the hole is reducible, the step must happen in
it. -/
theorem reducible_contextual_step_case {K : Ectx} {e e' : Expr}
    (h : ContextualStep (fill K e) e') (hred : reducible e) :
    ∃ e'', e' = fill K e'' ∧ ContextualStep e e'' := by
  rcases contextual_ectx_step_case h with hcase | hval
  · exact hcase
  · exact absurd hval (reducible_not_isVal hred)

/-- A value is already fully reduced. -/
theorem nsteps_val_inv {n : Nat} {v : Val} {e' : Expr} (h : redNsteps n v.toExpr e') :
    n = 0 ∧ e' = v.toExpr := by
  obtain ⟨hsteps, _⟩ := h
  cases hsteps with
  | zero => exact ⟨rfl, rfl⟩
  | step hstep _ => exact absurd ⟨_, hstep⟩ (val_irreducible (val_isVal v))

theorem nsteps_val_inv' {n : Nat} {v : Val} {e e' : Expr} (hv : e.toVal? = some v)
    (h : redNsteps n e e') : n = 0 ∧ e' = v.toExpr := by
  rw [toVal?_eq hv] at h
  exact nsteps_val_inv h

/-- A complete reduction of `fill K e` splits into a complete reduction
of the hole followed by a complete reduction of the filled result. -/
theorem red_nsteps_fill {K : Ectx} {k : Nat} {e e' : Expr} (h : redNsteps k (fill K e) e') :
    ∃ j e'', j ≤ k ∧ redNsteps j e e'' ∧ redNsteps (k - j) (fill K e'') e' := by
  obtain ⟨hsteps, hirred⟩ := h
  induction k generalizing e with
  | zero =>
    obtain rfl := nsteps_zero_inv hsteps
    exact ⟨0, e, Nat.le_refl 0, ⟨.zero, irreducible_fill hirred⟩, ⟨.zero, hirred⟩⟩
  | succ k ih =>
    obtain ⟨e₂, hstep, hrest⟩ := nsteps_succ_inv hsteps
    rcases contextual_ectx_step_case hstep with ⟨e'', rfl, hstep'⟩ | hval
    · obtain ⟨j, e₃, hj, hred₁, hred₂⟩ := ih hrest
      exact ⟨j + 1, e₃, by omega, ⟨.step hstep' hred₁.1, hred₁.2⟩, by simpa using hred₂⟩
    · exact ⟨0, e, Nat.zero_le _, ⟨.zero, val_irreducible hval⟩,
        ⟨.step hstep hrest, hirred⟩⟩

def subRedexesAreValues (e : Expr) : Prop :=
  ∀ (K : Ectx) (e' : Expr), e = fill K e' → ¬ Expr.isVal e' → K = []

/-- An expression whose sub-redexes are all values can only
step at the top. -/
theorem contextual_base_reducible {e : Expr} (hred : reducible e)
    (hsub : subRedexesAreValues e) : baseReducible e := by
  obtain ⟨e', hstep⟩ := hred
  obtain ⟨K, ea, eb, hf₁, _, hb⟩ := contextual_step_inv hstep
  obtain rfl := hsub K ea hf₁.symm (base_step_not_isVal hb)
  refine ⟨eb, ?_⟩
  have hea : ea = e := by simpa [fill] using hf₁
  exact hea ▸ hb

/-! ### Congruence lemmas for contextual steps -/

theorem contextual_step_app_l {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂)
    (h : ContextualStep e₁ e₁') : ContextualStep (.app e₁ e₂) (.app e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (K := [.appLCtx v]) h

theorem contextual_step_app_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.app e₁ e₂) (.app e₁ e₂') :=
  fill_contextual_step (K := [.appRCtx e₁]) h

theorem contextual_step_tapp {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.tApp e) (.tApp e') :=
  fill_contextual_step (K := [.tAppCtx]) h

theorem contextual_step_pack {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.pack e) (.pack e') :=
  fill_contextual_step (K := [.packCtx]) h

theorem contextual_step_unpack (x : Binder) (e₂ : Expr) {e e' : Expr}
    (h : ContextualStep e e') : ContextualStep (.unpack x e e₂) (.unpack x e' e₂) :=
  fill_contextual_step (K := [.unpackCtx x e₂]) h

theorem contextual_step_unop (op : UnOp) {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.unOp op e) (.unOp op e') :=
  fill_contextual_step (K := [.unOpCtx op]) h

theorem contextual_step_binop_l (op : BinOp) {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂)
    (h : ContextualStep e₁ e₁') : ContextualStep (.binOp op e₁ e₂) (.binOp op e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (K := [.binOpLCtx op v]) h

theorem contextual_step_binop_r (op : BinOp) (e₁ : Expr) {e₂ e₂' : Expr}
    (h : ContextualStep e₂ e₂') : ContextualStep (.binOp op e₁ e₂) (.binOp op e₁ e₂') :=
  fill_contextual_step (K := [.binOpRCtx op e₁]) h

theorem contextual_step_if (e₁ e₂ : Expr) {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.ite e e₁ e₂) (.ite e' e₁ e₂) :=
  fill_contextual_step (K := [.ifCtx e₁ e₂]) h

theorem contextual_step_pair_l {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂)
    (h : ContextualStep e₁ e₁') : ContextualStep (.pair e₁ e₂) (.pair e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact fill_contextual_step (K := [.pairLCtx v]) h

theorem contextual_step_pair_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.pair e₁ e₂) (.pair e₁ e₂') :=
  fill_contextual_step (K := [.pairRCtx e₁]) h

theorem contextual_step_fst {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.fst e) (.fst e') :=
  fill_contextual_step (K := [.fstCtx]) h

theorem contextual_step_snd {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.snd e) (.snd e') :=
  fill_contextual_step (K := [.sndCtx]) h

theorem contextual_step_injl {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.injL e) (.injL e') :=
  fill_contextual_step (K := [.injLCtx]) h

theorem contextual_step_injr {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.injR e) (.injR e') :=
  fill_contextual_step (K := [.injRCtx]) h

theorem contextual_step_case (e₁ e₂ : Expr) {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.case e e₁ e₂) (.case e' e₁ e₂) :=
  fill_contextual_step (K := [.caseCtx e₁ e₂]) h

theorem contextual_step_roll {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.roll e) (.roll e') :=
  fill_contextual_step (K := [.rollCtx]) h

theorem contextual_step_unroll {e e' : Expr} (h : ContextualStep e e') :
    ContextualStep (.unroll e) (.unroll e') :=
  fill_contextual_step (K := [.unrollCtx]) h

/-! ### The `pure.v` stepping lemmas -/

theorem app_step_r (e₁ : Expr) {e₂ e₂' : Expr} (h : ContextualStep e₂ e₂') :
    ContextualStep (.app e₁ e₂) (.app e₁ e₂') :=
  contextual_step_app_r e₁ h

theorem app_step_l {e₁ e₁' e₂ : Expr} (h : ContextualStep e₁ e₁') (hv : Expr.isVal e₂) :
    ContextualStep (.app e₁ e₂) (.app e₁' e₂) :=
  contextual_step_app_l hv h

/-- The unused `is_closed [x] e` premise is dropped. -/
theorem app_step_beta (x : String) (e e' : Expr) (hv : Expr.isVal e') :
    ContextualStep (.app (.lam (.bNamed x) e) e') (subst x e' e) :=
  base_contextual_step (.betaS (.bNamed x) e e' hv)

theorem unroll_roll_step {e : Expr} (hv : Expr.isVal e) : ContextualStep (.unroll (.roll e)) e :=
  base_contextual_step (.unrollS e hv)

/-! ### Congruence lemmas for deterministic steps -/

/-- A `DetStep` lifts through any evaluation context. -/
theorem DetStep.fill {K : Ectx} {e e' : Expr} (h : DetStep e e') :
    DetStep (SystemFMu.fill K e) (SystemFMu.fill K e') where
  safe := fill_reducible K h.safe
  det _ hcs := by
    obtain ⟨e'', rfl, hstep⟩ := reducible_contextual_step_case hcs h.safe
    rw [h.det e'' hstep]

theorem det_step_pair_r (e₁ : Expr) {e₂ e₂' : Expr} (h : DetStep e₂ e₂') :
    DetStep (.pair e₁ e₂) (.pair e₁ e₂') :=
  h.fill (K := [.pairRCtx e₁])

theorem det_step_pair_l {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂) (h : DetStep e₁ e₁') :
    DetStep (.pair e₁ e₂) (.pair e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact h.fill (K := [.pairLCtx v])

theorem det_step_binop_r (op : BinOp) (e₁ : Expr) {e₂ e₂' : Expr} (h : DetStep e₂ e₂') :
    DetStep (.binOp op e₁ e₂) (.binOp op e₁ e₂') :=
  h.fill (K := [.binOpRCtx op e₁])

theorem det_step_binop_l (op : BinOp) {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂)
    (h : DetStep e₁ e₁') : DetStep (.binOp op e₁ e₂) (.binOp op e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact h.fill (K := [.binOpLCtx op v])

theorem det_step_if (e₁ e₂ : Expr) {e e' : Expr} (h : DetStep e e') :
    DetStep (.ite e e₁ e₂) (.ite e' e₁ e₂) :=
  h.fill (K := [.ifCtx e₁ e₂])

theorem det_step_app_r (e₁ : Expr) {e₂ e₂' : Expr} (h : DetStep e₂ e₂') :
    DetStep (.app e₁ e₂) (.app e₁ e₂') :=
  h.fill (K := [.appRCtx e₁])

theorem det_step_app_l {e₁ e₁' e₂ : Expr} (hv : Expr.isVal e₂) (h : DetStep e₁ e₁') :
    DetStep (.app e₁ e₂) (.app e₁' e₂) := by
  obtain ⟨v, rfl⟩ := isVal_exists hv
  exact h.fill (K := [.appLCtx v])

theorem det_step_snd_lift {e e' : Expr} (h : DetStep e e') : DetStep (.snd e) (.snd e') :=
  h.fill (K := [.sndCtx])

theorem det_step_fst_lift {e e' : Expr} (h : DetStep e e') : DetStep (.fst e) (.fst e') :=
  h.fill (K := [.fstCtx])

end SystemFMu
