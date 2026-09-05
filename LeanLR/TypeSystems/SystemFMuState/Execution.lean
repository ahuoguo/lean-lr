import LeanLR.TypeSystems.SystemFMuState.Lang

/-!
# System F with recursive types and mutable state: execution

Deterministic steps, `n`-step reduction, and the inversion lemmas that pin down the unique way a
reducible expression decomposes into an evaluation context and a redex.
-/

namespace SystemFMuState

/-! ## Deterministic steps and `n`-step reduction -/

/-- `DetStep e₁ e₂` says `e₁` is reducible in every heap and every reduction of it yields `e₂`
leaving the heap untouched. -/
structure DetStep (e₁ e₂ : Expr) : Prop where
  safe : ∀ h, reducible e₁ h
  det : ∀ e₂' h h', ContextualStep (e₁, h) (e₂', h') → e₂' = e₂ ∧ h' = h

/-- `Nsteps n s s'` chains exactly `n` contextual steps from `s` to `s'`. -/
inductive Nsteps : Nat → (Expr × Heap) → (Expr × Heap) → Prop where
  | zero : Nsteps 0 s s
  | step : ContextualStep s₁ s₂ → Nsteps n s₂ s₃ → Nsteps (n + 1) s₁ s₃

/-- A complete reduction: `n` steps ending in an irreducible state. -/
def redNsteps (n : Nat) (e : Expr) (h : Heap) (e' : Expr) (h' : Heap) : Prop :=
  Nsteps n (e, h) (e', h') ∧ irreducible e' h'

/-! ## Contextual steps -/

/-- A redex reduction is a contextual step under the empty context. -/
theorem base_contextual_step {e₁ e₂ : Expr} {h₁ h₂ : Heap} :
    BaseStep (e₁, h₁) (e₂, h₂) → ContextualStep (e₁, h₁) (e₂, h₂) :=
  fun hb => .ectxStep [] e₁ e₂ h₁ h₂ hb

/-- Contextual steps are closed under plugging into a further evaluation context. -/
theorem fill_contextual_step {K : Ectx} {e₁ e₂ : Expr} {h₁ h₂ : Heap} :
    ContextualStep (e₁, h₁) (e₂, h₂) →
    ContextualStep (fill K e₁, h₁) (fill K e₂, h₂) := by
  intro ⟨K', e₁', e₂', _, _, hb⟩
  have hfl : ∀ (A B : Ectx) (x : Expr), fill (A ++ B) x = fill B (fill A x) := by
    intro A B x
    simp [fill, List.foldl_append]
  rw [← hfl K' K e₁', ← hfl K' K e₂']
  exact .ectxStep (K' ++ K) e₁' e₂' _ _ hb

/-- Splits a contextual step into its evaluation context and the underlying redex reduction. -/
theorem contextual_step_inv {expr e' : Expr} {h h' : Heap}
    (hstep : ContextualStep (expr, h) (e', h')) :
    ∃ (K : Ectx) (e₁ e₂ : Expr),
      fill K e₁ = expr ∧ fill K e₂ = e' ∧ BaseStep (e₁, h) (e₂, h') := by
  cases hstep with
  | ectxStep K e₁ e₂ h₁ h₂ hb => exact ⟨K, e₁, e₂, rfl, rfl, hb⟩

/-- Values are not redexes. -/
theorem val_no_base_step {e : Expr} {h : Heap} {e' : Expr} {h' : Heap} :
    Expr.isVal e → ¬ BaseStep (e, h) (e', h') := by
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
private theorem fillItem_isVal_imp (ki : EctxItem) (e : Expr)
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
theorem fill_val_base_step_absurd (K : Ectx) (e₁ e₂ : Expr) (h h' : Heap)
    (hval : Expr.isVal (fill K e₁)) (hbase : BaseStep (e₁, h) (e₂, h')) : False :=
  val_no_base_step (fill_isVal_imp K e₁ hval) hbase

/-- A value expression cannot start a contextual step. -/
private theorem val_no_contextual_step {v : Val} {h h' : Heap} {e' : Expr} :
    ¬ ContextualStep (v.toExpr, h) (e', h') := fun hstep => by
  obtain ⟨K, ea, eb, hfill, _, hbase⟩ := contextual_step_inv hstep
  exact fill_val_base_step_absurd K ea eb _ _ (hfill ▸ val_isVal v) hbase

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
private theorem unique_decomp_of_subredexes_val {K : Ectx} {ea eb redex : Expr} {h h' : Heap}
    (hsub : ∀ Ki e, fillItem Ki e = redex → Expr.isVal e)
    (hfill : fill K ea = redex) (hbase : BaseStep (ea, h) (eb, h')) :
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
are values (`hsub`), it reduces to `e'` in any heap (`hbase`), and that is its only reduction
(`hdet`). Uniqueness of the decomposition then upgrades redex determinism to whole-program
determinism. -/
private theorem DetStep.of_base {redex e' : Expr}
    (hsub : ∀ Ki e, fillItem Ki e = redex → Expr.isVal e)
    (hbase : ∀ h, BaseStep (redex, h) (e', h))
    (hdet : ∀ e'' h h', BaseStep (redex, h) (e'', h') → e'' = e' ∧ h' = h) :
    DetStep redex e' where
  safe h := ⟨e', h, base_contextual_step (hbase h)⟩
  det e'' h h' hcs := by
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hb⟩ := contextual_step_inv hcs
    obtain ⟨rfl, rfl⟩ := unique_decomp_of_subredexes_val hsub hfill₁ hb
    obtain ⟨rfl, rfl⟩ := hdet eb h h' hb
    exact ⟨by simpa [fill] using hfill₂.symm, rfl⟩

/-- Beta reduction of a term abstraction. -/
theorem det_step_beta (x : Binder) (e e₂ : Expr) (hval : Expr.isVal e₂) :
    DetStep (.app (.lam x e) e₂) (subst' x e₂ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .betaS x e e₂ h hval)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- Beta reduction of a type abstraction; types are erased, so the body is returned unchanged. -/
theorem det_step_tBeta (e : Expr) : DetStep (.tApp (.tLam e)) e :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .tBetaS e h)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- Unpacking an existential substitutes the packed value into the body. -/
theorem det_step_unpack (x : Binder) (e₁ e₂ : Expr) (hval : Expr.isVal e₁) :
    DetStep (.unpack x (.pack e₁) e₂) (subst' x e₁ e₂) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .unpackS x e₁ e₂ h hval)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- `if true then e₁ else e₂` takes the first branch. -/
theorem det_step_if_true (e₁ e₂ : Expr) : DetStep (.ite (.lit (.litBool true)) e₁ e₂) e₁ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .ifTrueS e₁ e₂ h)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- `if false then e₁ else e₂` takes the second branch. -/
theorem det_step_if_false (e₁ e₂ : Expr) : DetStep (.ite (.lit (.litBool false)) e₁ e₂) e₂ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .ifFalseS e₁ e₂ h)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- First projection of a pair of values. -/
theorem det_step_fst (e₁ e₂ : Expr) (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂) :
    DetStep (.fst (.pair e₁ e₂)) e₁ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .fstS e₁ e₂ h hv₁ hv₂)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- Second projection of a pair of values. -/
theorem det_step_snd (e₁ e₂ : Expr) (hv₁ : Expr.isVal e₁) (hv₂ : Expr.isVal e₂) :
    DetStep (.snd (.pair e₁ e₂)) e₂ :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .sndS e₁ e₂ h hv₁ hv₂)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- A `case` on a left injection applies the left branch. -/
theorem det_step_caseL (e e₁ e₂ : Expr) (hv : Expr.isVal e) :
    DetStep (.case (.injL e) e₁ e₂) (.app e₁ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .caseLS e e₁ e₂ h hv)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- A `case` on a right injection applies the right branch. -/
theorem det_step_caseR (e e₁ e₂ : Expr) (hv : Expr.isVal e) :
    DetStep (.case (.injR e) e₁ e₂) (.app e₂ e) :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .caseRS e e₁ e₂ h hv)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- `unroll (roll v)` cancels. -/
theorem det_step_unroll (e : Expr) (hv : Expr.isVal e) : DetStep (.unroll (.roll e)) e :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
    (fun h => .unrollS e h hv)
    (by intro _ _ _ hb; cases hb; exact ⟨rfl, rfl⟩)

/-- A unary operator applied to a value it accepts. -/
theorem det_step_unOp (op : UnOp) (e : Expr) (v v' : Val)
    (htv : Expr.toVal? e = some v) (hev : unOpEval op v = some v') :
    DetStep (.unOp op e) v'.toExpr :=
  .of_base (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, toVal?_isVal htv])
    (fun h => .unOpS op e v v' h htv hev)
    (by
      intro _ _ _ hb
      cases hb with
      | unOpS _ _ _ _ _ htv' hev' =>
        rw [htv] at htv'
        cases htv'
        rw [hev] at hev'
        cases hev'
        exact ⟨rfl, rfl⟩)

/-- A binary operator applied to values it accepts. -/
theorem det_step_binOp (op : BinOp) (e₁ e₂ : Expr) (v₁ v₂ v' : Val)
    (htv₁ : Expr.toVal? e₁ = some v₁) (htv₂ : Expr.toVal? e₂ = some v₂)
    (hev : binOpEval op v₁ v₂ = some v') :
    DetStep (.binOp op e₁ e₂) v'.toExpr :=
  .of_base
    (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, toVal?_isVal htv₁, toVal?_isVal htv₂])
    (fun h => .binOpS op e₁ e₂ v₁ v₂ v' h htv₁ htv₂ hev)
    (by
      intro _ _ _ hb
      cases hb with
      | binOpS _ _ _ _ _ _ _ htv₁' htv₂' hev' =>
        rw [htv₁] at htv₁'
        cases htv₁'
        rw [htv₂] at htv₂'
        cases htv₂'
        rw [hev] at hev'
        cases hev'
        exact ⟨rfl, rfl⟩)

/-! ## Heap execution

The state operations are *not* deterministic steps: `new` picks its fresh location freely, so its
reduction is not a function of the source state and `DetStep` — hence `det_step_red` — cannot
express it. Instead each operation gets an inversion lemma reading off what its unique reduction
did, and an `n`-step counterpart pinning `n = 1`. -/

/-- Inversion for `Nsteps 0`, exposing the state as explicit components. Plain `cases` leaves it
as an opaque pair, which blocks rewriting. -/
theorem nsteps_zero_inv {e e' : Expr} {h h' : Heap} :
    Nsteps 0 (e, h) (e', h') → e = e' ∧ h = h' := by
  intro hs
  cases hs
  exact ⟨rfl, rfl⟩

/-- Inversion for `Nsteps (n + 1)`, exposing the intermediate state as explicit components. -/
theorem nsteps_succ_inv {n : Nat} {e e' : Expr} {h h' : Heap} :
    Nsteps (n + 1) (e, h) (e', h') →
    ∃ em hm, ContextualStep (e, h) (em, hm) ∧ Nsteps n (em, hm) (e', h') := by
  intro hs
  cases hs with
  | step hstep hrest => exact ⟨_, _, hstep, hrest⟩

/-- A base step of `new e` allocates a fresh location. -/
theorem new_step_inv {e e' : Expr} {v : Val} {h h' : Heap}
    (hv : Expr.toVal? e = some v) (hstep : BaseStep (.new e, h) (e', h')) :
    ∃ l : Loc, e' = .lit (.litLoc l) ∧ h' = Heap.insert h l v ∧ h l = none := by
  cases hstep with
  | newS e₀ v₀ l h₀ hv₀ hfresh =>
    rw [hv] at hv₀
    cases hv₀
    exact ⟨l, rfl, rfl, hfresh⟩

/-- A base step of `load #l` reads the current contents of `l`. -/
theorem load_step_inv {e e' : Expr} {v : Val} {h h' : Heap}
    (hv : Expr.toVal? e = some v) (hstep : BaseStep (.load e, h) (e', h')) :
    ∃ (l : Loc) (v' : Val), v = .litV (.litLoc l) ∧ h l = some v' ∧
      e' = v'.toExpr ∧ h' = h := by
  cases hstep with
  | loadS l v₀ h₀ hlook =>
    refine ⟨l, v₀, ?_, hlook, rfl, rfl⟩
    simp [Expr.toVal?] at hv
    exact hv.symm

/-- A base step of `#l <- v` overwrites an already-allocated location. -/
theorem store_step_inv {e₁ e₂ e' : Expr} {v₁ v₂ : Val} {h h' : Heap}
    (hv₁ : Expr.toVal? e₁ = some v₁) (hv₂ : Expr.toVal? e₂ = some v₂)
    (hstep : BaseStep (.store e₁ e₂, h) (e', h')) :
    ∃ l : Loc, v₁ = .litV (.litLoc l) ∧ h l ≠ none ∧
      e' = .lit .litUnit ∧ h' = Heap.insert h l v₂ := by
  cases hstep with
  | storeS l v₀ e₂₀ h₀ hlook hv₀ =>
    have hl : v₁ = Val.litV (.litLoc l) := by
      simp [Expr.toVal?] at hv₁
      exact hv₁.symm
    rw [hv₂] at hv₀
    cases hv₀
    exact ⟨l, hl, hlook, rfl, rfl⟩

/-- A redex that is reducible (`hred`), has only values as sub-redexes (`hsub`), and always
reduces to a value (`hres`) reaches an irreducible state in exactly one step, and that step is a
redex reduction. Since the result is a value it admits no further step, which is what forces
`n = 1` rather than merely `1 ≤ n`. -/
private theorem redNsteps_base_inv {n : Nat} {redex e' : Expr} {h h' : Heap}
    (hsub : ∀ Ki e, fillItem Ki e = redex → Expr.isVal e)
    (hred : reducible redex h)
    (hres : ∀ e'' h'', BaseStep (redex, h) (e'', h'') → ∃ w : Val, e'' = w.toExpr)
    (hn : redNsteps n redex h e' h') :
    n = 1 ∧ BaseStep (redex, h) (e', h') := by
  obtain ⟨hsteps, hirred⟩ := hn
  match n with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := nsteps_zero_inv hsteps
    exact absurd hred hirred
  | m + 1 =>
    obtain ⟨em, hm, hstep, hrest⟩ := nsteps_succ_inv hsteps
    obtain ⟨K, ea, eb, hfill₁, hfill₂, hbase⟩ := contextual_step_inv hstep
    obtain ⟨rfl, rfl⟩ := unique_decomp_of_subredexes_val hsub hfill₁ hbase
    simp only [fill, List.foldl] at hfill₁ hfill₂
    obtain ⟨w, rfl⟩ := hres _ _ hbase
    subst hfill₂
    match m with
    | 0 =>
      obtain ⟨rfl, rfl⟩ := nsteps_zero_inv hrest
      exact ⟨rfl, hbase⟩
    | j + 1 =>
      obtain ⟨_, _, hstep', _⟩ := nsteps_succ_inv hrest
      exact absurd hstep' val_no_contextual_step

/-- `new v` allocates in exactly one step, given that some location is free. -/
theorem new_nsteps_inv {n : Nat} {e e' : Expr} {v : Val} {h h' : Heap}
    (hv : Expr.toVal? e = some v) (hfresh : ∃ l, h l = none)
    (hred : redNsteps n (.new e) h e' h') :
    n = 1 ∧ ∃ l, e' = .lit (.litLoc l) ∧ h' = Heap.insert h l v ∧ h l = none := by
  obtain ⟨l, hl⟩ := hfresh
  obtain ⟨rfl, hbase⟩ :=
    redNsteps_base_inv (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, toVal?_isVal hv])
      ⟨_, _, base_contextual_step (.newS e v l h hv hl)⟩
      (fun _ _ hb => by
        obtain ⟨l', rfl, _, _⟩ := new_step_inv hv hb
        exact ⟨.litV (.litLoc l'), rfl⟩)
      hred
  exact ⟨rfl, new_step_inv hv hbase⟩

/-- `load #l` on an allocated location reads it in exactly one step. -/
theorem load_nsteps_inv {n : Nat} {e e' : Expr} {l : Loc} {v' : Val} {h h' : Heap}
    (hv : Expr.toVal? e = some (.litV (.litLoc l))) (hlook : h l = some v')
    (hred : redNsteps n (.load e) h e' h') :
    n = 1 ∧ e' = v'.toExpr ∧ h' = h := by
  have heq : e = Expr.lit (.litLoc l) := toVal?_eq hv
  obtain ⟨rfl, hbase⟩ :=
    redNsteps_base_inv (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal])
      ⟨_, _, base_contextual_step (heq ▸ BaseStep.loadS l v' h hlook)⟩
      (fun _ _ hb => by
        obtain ⟨_, vr, _, _, rfl, _⟩ := load_step_inv hv hb
        exact ⟨vr, rfl⟩)
      hred
  obtain ⟨l₀, vr, hl₀, hlook₀, rfl, rfl⟩ := load_step_inv hv hbase
  cases hl₀
  rw [hlook] at hlook₀
  cases hlook₀
  exact ⟨rfl, rfl, rfl⟩

/-- `#l <- v` on an allocated location writes it in exactly one step. -/
theorem store_nsteps_inv {n : Nat} {e₁ e₂ e' : Expr} {l : Loc} {v v₀ : Val} {h h' : Heap}
    (hv₁ : Expr.toVal? e₁ = some (.litV (.litLoc l))) (hv₂ : Expr.toVal? e₂ = some v)
    (hlook : h l = some v₀) (hred : redNsteps n (.store e₁ e₂) h e' h') :
    n = 1 ∧ e' = .lit .litUnit ∧ h' = Heap.insert h l v := by
  have heq : e₁ = Expr.lit (.litLoc l) := toVal?_eq hv₁
  obtain ⟨rfl, hbase⟩ :=
    redNsteps_base_inv
      (by intro Ki e hKi; cases Ki <;> simp_all [fillItem, Expr.isVal, toVal?_isVal hv₂])
      ⟨_, _, base_contextual_step (heq ▸ BaseStep.storeS l v e₂ h (by simp [hlook]) hv₂)⟩
      (fun _ _ hb => by
        obtain ⟨_, _, _, rfl, _⟩ := store_step_inv hv₁ hv₂ hb
        exact ⟨.litV .litUnit, rfl⟩)
      hred
  obtain ⟨l₀, hl₀, _, rfl, rfl⟩ := store_step_inv hv₁ hv₂ hbase
  cases hl₀
  exact ⟨rfl, rfl, rfl⟩

/-! ## `n`-step lemmas -/

/-- Prepends a contextual step to a complete reduction. -/
theorem contextual_step_red_nsteps {n : Nat} {e e' e'' : Expr} {h h' h'' : Heap} :
    ContextualStep (e, h) (e', h') → redNsteps n e' h' e'' h'' →
    redNsteps (n + 1) e h e'' h'' := by
  intro hstep ⟨hn, hi⟩
  exact ⟨.step hstep hn, hi⟩

/-- A complete reduction out of a deterministic redex must begin with that redex's step. -/
theorem det_step_red {e e' e'' : Expr} {h h'' : Heap} {n : Nat} :
    DetStep e e' → redNsteps n e h e'' h'' →
    1 ≤ n ∧ redNsteps (n - 1) e' h e'' h'' := by
  intro ⟨hsafe, hdet⟩ ⟨hn, hi⟩
  cases hn with
  | zero => exact absurd (hsafe _) hi
  | step hstep hn' =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ _ hstep
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), hn', hi⟩

end SystemFMuState
