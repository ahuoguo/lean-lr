import LeanLR.TypeSystems.SystemFMuState.LogRel
import LeanLR.TypeSystems.SystemFMuState.Notation

/-!
# A mutable bit, proved safe semantically

`systemf_mu_state/mutbit.v`. `mymutbit` hands out a flip and a read function over a single cell;
`mymutbit_instrumented` additionally asserts, at each entry point, that the cell holds `0` or `1`.
Nothing in the type system says so, but the logical relation can: the world gets an invariant
whose predicate is exactly "`0` or `1`", which is stronger than the `Int` its type gives
(`CORRESPONDENCE.md` §5.6b).
-/

open Iris.Std

namespace SystemFMuState

set_option maxHeartbeats 1000000

def mutbit_t : Ty := .prod (.fn .unit .unit) (.fn .unit .bool)

def mymutbit : Expr :=
  let: x := Expr.new (.lit (.litInt 0)) in
    Expr.pair
      (λ: y, Expr.store (.var "x")
        (Expr.binOp .minusOp (.lit (.litInt 1)) (Expr.load (.var "x"))))
      (λ: y, Expr.binOp .ltOp (.lit (.litInt 0)) (Expr.load (.var "x")))

/-- The body of `mymutbit_instrumented`'s `let`. Rocq writes it inline; naming it is what lets
the proof below talk about the substitution the `let` performs. -/
def mutbitBody : Expr :=
  Expr.pair
    (λ: y, seqE
      (assert (Or (Expr.binOp .eqOp (Expr.load (.var "x")) (.lit (.litInt 0)))
        (Expr.binOp .eqOp (Expr.load (.var "x")) (.lit (.litInt 1)))))
      (Expr.store (.var "x")
        (Expr.binOp .minusOp (.lit (.litInt 1)) (Expr.load (.var "x")))))
    (λ: y, seqE
      (assert (Or (Expr.binOp .eqOp (Expr.load (.var "x")) (.lit (.litInt 0)))
        (Expr.binOp .eqOp (Expr.load (.var "x")) (.lit (.litInt 1)))))
      (Expr.binOp .ltOp (.lit (.litInt 0)) (Expr.load (.var "x"))))

def mymutbit_instrumented : Expr :=
  let: x := Expr.new (.lit (.litInt 0)) in mutbitBody

/-- The invariant the proof installs: the cell holds `0` or `1`. -/
def mutbitInv (l : Loc) : HeapInv :=
  ⟨l, fun v => v = .litV (.litInt 0) ∨ v = .litV (.litInt 1)⟩

/-! ## Inverting a complete reduction one step at a time

Rocq's `invert_det_step`; the two heap steps get the same packaging so that the whole reduction
can be peeled off uniformly. -/

theorem red_det_inv {e e₀ e' : Expr} {h h' : Heap} {n : Nat}
    (hd : DetStep e e₀) (hred : redNsteps n e h e' h') :
    ∃ m, n = m + 1 ∧ redNsteps m e₀ h e' h' := by
  obtain ⟨hle, hr⟩ := det_step_red hd hred
  exact ⟨n - 1, by omega, hr⟩

theorem red_load_inv {K : Ectx} {l : Loc} {v : Val} {h h' : Heap} {e' : Expr} {n : Nat}
    (hlook : h l = some v)
    (hred : redNsteps n (fill K (.load (.lit (.litLoc l)))) h e' h') :
    ∃ m, n = m + 1 ∧ redNsteps m (fill K v.toExpr) h e' h' := by
  obtain ⟨j, e'', h'', hj, hred₁, hred₂⟩ := red_nsteps_fill hred
  obtain ⟨rfl, rfl, rfl⟩ := load_nsteps_inv rfl hlook hred₁
  exact ⟨n - 1, by omega, hred₂⟩

theorem red_store_inv {K : Ectx} {l : Loc} {v v₀ : Val} {h h' : Heap} {e' : Expr} {n : Nat}
    (hlook : h l = some v₀)
    (hred : redNsteps n (fill K (.store (.lit (.litLoc l)) v.toExpr)) h e' h') :
    ∃ m, n = m + 1 ∧ redNsteps m (fill K (.lit .litUnit)) (Heap.insert h l v) e' h' := by
  obtain ⟨j, e'', h'', hj, hred₁, hred₂⟩ := red_nsteps_fill hred
  obtain ⟨hj1, heq, hheap⟩ := store_nsteps_inv rfl (toVal?_toExpr v) hlook hred₁
  subst hj1
  subst heq
  subst hheap
  exact ⟨n - 1, by omega, hred₂⟩

/-! ## The two closures

The bodies with the location already substituted in. Rocq keeps them inline; naming them keeps
the evaluation contexts below readable. -/

private def mutbitAssert (l : Loc) : Expr :=
  assert (Or (Expr.binOp .eqOp (Expr.load (.lit (.litLoc l))) (.lit (.litInt 0)))
    (Expr.binOp .eqOp (Expr.load (.lit (.litLoc l))) (.lit (.litInt 1))))

private def flipStore (l : Loc) : Expr :=
  Expr.store (.lit (.litLoc l))
    (Expr.binOp .minusOp (.lit (.litInt 1)) (Expr.load (.lit (.litLoc l))))

private def getTest (l : Loc) : Expr :=
  Expr.binOp .ltOp (.lit (.litInt 0)) (Expr.load (.lit (.litLoc l)))

private def flipBody (l : Loc) : Expr := seqE (mutbitAssert l) (flipStore l)

private def getBody (l : Loc) : Expr := seqE (mutbitAssert l) (getTest l)

/-- The evaluation context of the first `!x` of the assertion, in `flipBody`. -/
private def assertCtx (l : Loc) (rest : Expr) : Ectx :=
  [.binOpLCtx .eqOp (.litV (.litInt 0)),
   .ifCtx (.lit (.litBool true)) (Expr.binOp .eqOp (Expr.load (.lit (.litLoc l)))
     (.lit (.litInt 1))),
   .ifCtx (.lit .litUnit) (Expr.app (.lit (.litInt 0)) (.lit (.litInt 0))),
   .appRCtx (.lam .bAnon rest)]

/-- The evaluation context of the *second* `!x` of the assertion, reached only when the cell
holds `1`. -/
private def assertCtx₁ (rest : Expr) : Ectx :=
  [.binOpLCtx .eqOp (.litV (.litInt 1)),
   .ifCtx (.lit .litUnit) (Expr.app (.lit (.litInt 0)) (.lit (.litInt 0))),
   .appRCtx (.lam .bAnon rest)]

private def assertCtxIf (l : Loc) (rest : Expr) : Ectx :=
  [.ifCtx (.lit (.litBool true))
     (Expr.binOp .eqOp (Expr.load (.lit (.litLoc l))) (.lit (.litInt 1))),
   .ifCtx (.lit .litUnit) (Expr.app (.lit (.litInt 0)) (.lit (.litInt 0))),
   .appRCtx (.lam .bAnon rest)]

private def assertCtxAssert (rest : Expr) : Ectx :=
  [.ifCtx (.lit .litUnit) (Expr.app (.lit (.litInt 0)) (.lit (.litInt 0))),
   .appRCtx (.lam .bAnon rest)]

private def assertCtxSeq (rest : Expr) : Ectx := [.appRCtx (.lam .bAnon rest)]

/-- The context of the `!x` inside `#1 - !x`. -/
private def flipStoreCtx (l : Loc) : Ectx :=
  [.binOpRCtx .minusOp (.lit (.litInt 1)), .storeRCtx (.lit (.litLoc l))]

private theorem flip_body_safe (l : Loc) (k : Nat) (W : World) (hmem : mutbitInv l ∈ W) :
    exprRel anyTyVarInterp .unit k W (flipBody l) := by
  unfold exprRel
  intro e' h h' n W₂ hext hsat hn hred
  have hmem₂ : mutbitInv l ∈ W₂ := worldExt_mem hext hmem
  obtain ⟨c, hlook, hc⟩ := wsat_lookup hsat hmem₂
  obtain ⟨n₁, -, hred⟩ :=
    red_load_inv (K := assertCtx l (flipStore l)) (v := c) hlook hred
  rcases hc with rfl | rfl
  · -- the cell holds `0`: the first disjunct of the assertion fires
    obtain ⟨n₂, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxIf l (flipStore l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 0)) (.litV (.litInt 0))
        (.litV (.litBool true)) rfl rfl rfl)) hred
    obtain ⟨n₃, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (flipStore l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₄, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxSeq (flipStore l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₅, -, hred⟩ := red_det_inv (det_step_beta .bAnon (flipStore l) (.lit .litUnit) trivial) hred
    obtain ⟨n₆, -, hred⟩ :=
      red_load_inv (K := flipStoreCtx l) (v := .litV (.litInt 0)) hlook hred
    obtain ⟨n₇, -, hred⟩ := red_det_inv (DetStep.fill (K := [.storeRCtx (.lit (.litLoc l))])
      (det_step_binOp .minusOp _ _ (.litV (.litInt 1)) (.litV (.litInt 0))
        (.litV (.litInt 1)) rfl rfl rfl)) hred
    obtain ⟨n₈, -, hred⟩ :=
      red_store_inv (K := []) (v := .litV (.litInt 1)) hlook hred
    obtain ⟨-, rfl, rfl⟩ := nsteps_val_inv' (v := .litV .litUnit) rfl hred
    exact ⟨.litV .litUnit, W₂, rfl, worldExt_refl W₂,
      wsat_update hsat hmem₂ (Or.inr rfl), by simp only [valRel]⟩
  · -- the cell holds `1`: the second disjunct fires
    obtain ⟨n₂, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxIf l (flipStore l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 1)) (.litV (.litInt 0))
        (.litV (.litBool false)) rfl rfl rfl)) hred
    obtain ⟨n₃, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (flipStore l))
      (det_step_if_false _ _)) hred
    obtain ⟨n₄, -, hred⟩ :=
      red_load_inv (K := assertCtx₁ (flipStore l)) (v := .litV (.litInt 1)) hlook hred
    obtain ⟨n₅, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (flipStore l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 1)) (.litV (.litInt 1))
        (.litV (.litBool true)) rfl rfl rfl)) hred
    obtain ⟨n₆, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxSeq (flipStore l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₇, -, hred⟩ := red_det_inv (det_step_beta .bAnon (flipStore l) (.lit .litUnit) trivial) hred
    obtain ⟨n₈, -, hred⟩ :=
      red_load_inv (K := flipStoreCtx l) (v := .litV (.litInt 1)) hlook hred
    obtain ⟨n₉, -, hred⟩ := red_det_inv (DetStep.fill (K := [.storeRCtx (.lit (.litLoc l))])
      (det_step_binOp .minusOp _ _ (.litV (.litInt 1)) (.litV (.litInt 1))
        (.litV (.litInt 0)) rfl rfl rfl)) hred
    obtain ⟨n₁₀, -, hred⟩ :=
      red_store_inv (K := []) (v := .litV (.litInt 0)) hlook hred
    obtain ⟨-, rfl, rfl⟩ := nsteps_val_inv' (v := .litV .litUnit) rfl hred
    exact ⟨.litV .litUnit, W₂, rfl, worldExt_refl W₂,
      wsat_update hsat hmem₂ (Or.inl rfl), by simp only [valRel]⟩

private theorem get_body_safe (l : Loc) (k : Nat) (W : World) (hmem : mutbitInv l ∈ W) :
    exprRel anyTyVarInterp .bool k W (getBody l) := by
  unfold exprRel
  intro e' h h' n W₂ hext hsat hn hred
  have hmem₂ : mutbitInv l ∈ W₂ := worldExt_mem hext hmem
  obtain ⟨c, hlook, hc⟩ := wsat_lookup hsat hmem₂
  obtain ⟨n₁, -, hred⟩ :=
    red_load_inv (K := assertCtx l (getTest l)) (v := c) hlook hred
  rcases hc with rfl | rfl
  · obtain ⟨n₂, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxIf l (getTest l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 0)) (.litV (.litInt 0))
        (.litV (.litBool true)) rfl rfl rfl)) hred
    obtain ⟨n₃, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (getTest l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₄, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxSeq (getTest l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₅, -, hred⟩ := red_det_inv (det_step_beta .bAnon (getTest l)
      (.lit .litUnit) trivial) hred
    obtain ⟨n₆, -, hred⟩ :=
      red_load_inv (K := [.binOpRCtx .ltOp (.lit (.litInt 0))]) (v := .litV (.litInt 0))
        hlook hred
    obtain ⟨n₇, -, hred⟩ := red_det_inv
      (det_step_binOp .ltOp _ _ (.litV (.litInt 0)) (.litV (.litInt 0))
        (.litV (.litBool false)) rfl rfl rfl) hred
    obtain ⟨-, rfl, rfl⟩ := nsteps_val_inv' (v := .litV (.litBool false)) rfl hred
    exact ⟨.litV (.litBool false), W₂, rfl, worldExt_refl W₂, hsat,
      by rw [valRel]; trivial⟩
  · obtain ⟨n₂, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxIf l (getTest l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 1)) (.litV (.litInt 0))
        (.litV (.litBool false)) rfl rfl rfl)) hred
    obtain ⟨n₃, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (getTest l))
      (det_step_if_false _ _)) hred
    obtain ⟨n₄, -, hred⟩ :=
      red_load_inv (K := assertCtx₁ (getTest l)) (v := .litV (.litInt 1)) hlook hred
    obtain ⟨n₅, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxAssert (getTest l))
      (det_step_binOp .eqOp _ _ (.litV (.litInt 1)) (.litV (.litInt 1))
        (.litV (.litBool true)) rfl rfl rfl)) hred
    obtain ⟨n₆, -, hred⟩ := red_det_inv (DetStep.fill (K := assertCtxSeq (getTest l))
      (det_step_if_true _ _)) hred
    obtain ⟨n₇, -, hred⟩ := red_det_inv (det_step_beta .bAnon (getTest l)
      (.lit .litUnit) trivial) hred
    obtain ⟨n₈, -, hred⟩ :=
      red_load_inv (K := [.binOpRCtx .ltOp (.lit (.litInt 0))]) (v := .litV (.litInt 1))
        hlook hred
    obtain ⟨n₉, -, hred⟩ := red_det_inv
      (det_step_binOp .ltOp _ _ (.litV (.litInt 0)) (.litV (.litInt 1))
        (.litV (.litBool true)) rfl rfl rfl) hred
    obtain ⟨-, rfl, rfl⟩ := nsteps_val_inv' (v := .litV (.litBool true)) rfl hred
    exact ⟨.litV (.litBool true), W₂, rfl, worldExt_refl W₂, hsat,
      by rw [valRel]; trivial⟩

/-- The pair of closures the `let` produces, with the location substituted in. -/
private def mutbitVal (l : Loc) : Val :=
  .pairV (.lamV (.bNamed "y") (flipBody l)) (.lamV (.bNamed "y") (getBody l))

private theorem flipBody_closed (l : Loc) : closed [] (flipBody l) := by
  simp [flipBody, seqE, mutbitAssert, flipStore, assert, Or, closed, Expr.isClosed]

private theorem getBody_closed (l : Loc) : closed [] (getBody l) := by
  simp [getBody, seqE, mutbitAssert, getTest, assert, Or, closed, Expr.isClosed]

private theorem mutbitBody_subst (l : Loc) :
    subst' (Binder.bNamed "x") (Expr.lit (.litLoc l)) mutbitBody = (mutbitVal l).toExpr := by
  simp +decide [mutbitBody, mutbitVal, flipBody, getBody, mutbitAssert, flipStore, getTest,
    seqE, assert, Or, subst', subst, Val.toExpr]

theorem mymutbit_instrumented_safe (k : Nat) (W : World) :
    exprRel anyTyVarInterp mutbit_t k W mymutbit_instrumented := by
  unfold exprRel
  intro e' h h' n W' hext hsat hn hred
  obtain ⟨j, e₁, h₁, hj, hred₁, hred₂⟩ :=
    red_nsteps_fill (K := [.appRCtx (.lam (.bNamed "x") mutbitBody)])
      (e := Expr.new (.lit (.litInt 0))) hred
  obtain ⟨rfl, l, rfl, rfl, hfresh⟩ :=
    new_nsteps_inv (v := .litV (.litInt 0)) rfl (Heap.bounded_fresh hsat.1) hred₁
  obtain ⟨m, -, hred⟩ := red_det_inv
    (det_step_beta (.bNamed "x") mutbitBody (.lit (.litLoc l)) trivial) hred₂
  rw [mutbitBody_subst l] at hred
  obtain ⟨-, rfl, rfl⟩ := nsteps_val_inv' (v := mutbitVal l) rfl hred
  have hmem : mutbitInv l ∈ W' ++ [mutbitInv l] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨mutbitVal l, W' ++ [mutbitInv l], rfl, ⟨[mutbitInv l], rfl⟩,
    wsat_alloc hsat hfresh (Or.inl rfl), ?_⟩
  show valRel anyTyVarInterp mutbit_t _ _
    (Val.pairV (.lamV (.bNamed "y") (flipBody l)) (.lamV (.bNamed "y") (getBody l)))
  rw [mutbit_t, valRel]
  refine ⟨?_, ?_⟩
  · rw [valRel]
    refine ⟨closed_weaken_nil (flipBody_closed l), fun v' kd W'' hext'' _ => ?_⟩
    rw [subst'_closed_nil (flipBody_closed l)]
    exact flip_body_safe l _ W'' (worldExt_mem hext'' hmem)
  · rw [valRel]
    refine ⟨closed_weaken_nil (getBody_closed l), fun v' kd W'' hext'' _ => ?_⟩
    rw [subst'_closed_nil (getBody_closed l)]
    exact get_body_safe l _ W'' (worldExt_mem hext'' hmem)

end SystemFMuState
