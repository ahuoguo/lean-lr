import LeanLR.TypeSystems.SystemFMuState.Tactics
import LeanLR.TypeSystems.SystemFMuState.Execution
import LeanLR.TypeSystems.SystemFMuState.Notation

/-!
# System F + μ + state, exercise sheet 7

`systemf_mu_state/exercises07_sol.v`. A list type and a stack built on top of an abstract list
implementation, an obfuscated program that nevertheless evaluates to `42`, and a fixpoint
combinator built from a reference ("Landin's knot") with Fibonacci as its example.

The typing judgment here is the one of `types.v` — `SystemFMuState.Syn`, whose `ref` holds an
arbitrary type — not the logical relation's (`CORRESPONDENCE.md` §5.6).
-/

open Iris.Std

namespace SystemFMuState.Syn

set_option maxRecDepth 8000

/-! ## Exercise 1 (LN 45): stacks -/

section Lists

variable (A : Ty)

def list_type : Ty := .mu (.sum .unit (.prod (A.rename (· + 1)) (.tVar 0)))

def nil_val : Val := .rollV (.injLV (.litV .litUnit))

def cons_val (v xs : Val) : Val := .rollV (.injRV (.pairV v xs))

def cons_expr (v xs : Expr) : Expr := .roll (.injR (.pair v xs))

def list_case : Val :=
  .tLamV (λ: l n hf,
    matchE (Expr.unroll (.var "l")) .bAnon (.var "n") (.bNamed "h")
      (Expr.app (Expr.app (.var "hf") (Expr.fst (.var "h"))) (Expr.snd (.var "h"))))

theorem list_type_wf (n : Nat) (hA : TypeWf n A) : TypeWf n (list_type A) :=
  .mu_wf (.sum_wf .unit_wf
    (.prod_wf (TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA)
      (.tVar_wf (by omega))))

/-- Unrolling `list_type`. -/
theorem list_type_unfold :
    (Ty.sum .unit (.prod (A.rename (· + 1)) (.tVar 0))).subst1
        (.mu (Ty.sum .unit (.prod (A.rename (· + 1)) (.tVar 0))))
      = .sum .unit (.prod A (list_type A)) := by
  simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id]
  rfl

theorem nil_val_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) (hA : TypeWf n A) :
    SynTyped Θ n Γ (nil_val).toExpr (list_type A) := by
  refine .typed_roll n Γ _ _ ?_
  rw [list_type_unfold]
  exact .typed_injL n Γ _ .unit (.prod A (list_type A))
    (.prod_wf hA (list_type_wf A n hA)) (.typed_lit_unit n Γ)

theorem cons_val_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) (v xs : Val)
    (_hA : TypeWf n A) (hv : SynTyped Θ n Γ v.toExpr A)
    (hxs : SynTyped Θ n Γ xs.toExpr (list_type A)) :
    SynTyped Θ n Γ (cons_val v xs).toExpr (list_type A) := by
  refine .typed_roll n Γ _ _ ?_
  rw [list_type_unfold]
  exact .typed_injR n Γ _ .unit (.prod A (list_type A)) .unit_wf
    (.typed_pair n Γ _ _ A (list_type A) hv hxs)

theorem cons_expr_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) (x xs : Expr)
    (_hA : TypeWf n A) (hx : SynTyped Θ n Γ x A)
    (hxs : SynTyped Θ n Γ xs (list_type A)) :
    SynTyped Θ n Γ (cons_expr x xs) (list_type A) := by
  refine .typed_roll n Γ _ _ ?_
  rw [list_type_unfold]
  exact .typed_injR n Γ _ .unit (.prod A (list_type A)) .unit_wf
    (.typed_pair n Γ _ _ A (list_type A) hx hxs)

theorem list_case_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) (hA : TypeWf n A) :
    SynTyped Θ n Γ (list_case).toExpr
      (.all (.fn ((list_type A).rename (· + 1))
        (.fn (.tVar 0)
          (.fn (.fn (A.rename (· + 1)) (.fn ((list_type A).rename (· + 1)) (.tVar 0)))
            (.tVar 0))))) := by
  have hAup : TypeWf (n + 1) (A.rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) A (fun m hm => Nat.succ_lt_succ hm) hA
  have hLup : TypeWf (n + 1) ((list_type A).rename (· + 1)) :=
    TypeWf.rename (· + 1) n (n + 1) _ (fun m hm => Nat.succ_lt_succ hm) (list_type_wf A n hA)
  have hlift : (list_type A).rename (· + 1)
      = .mu (Ty.sum .unit (.prod (A.rename (fun m => m + 2)) (.tVar 0))) := by
    simp only [list_type, Ty.rename, Ty.rename_rename]
  have hunfold : (Ty.sum .unit (.prod (A.rename (fun m => m + 2)) (.tVar 0))).subst1
        (.mu (Ty.sum .unit (.prod (A.rename (fun m => m + 2)) (.tVar 0))))
      = .sum .unit (.prod (A.rename (· + 1)) ((list_type A).rename (· + 1))) := by
    rw [hlift]
    simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, ← Ty.rename_eq_substTy]
  refine .typed_tLam n Γ _ _ ?_
  refine .typed_lam (n + 1) _ "l" _ ((list_type A).rename (· + 1)) _ hLup ?_
  refine .typed_lam (n + 1) _ "n" _ (.tVar 0) _ (.tVar_wf (by omega)) ?_
  refine .typed_lam (n + 1) _ "hf" _
    (.fn (A.rename (· + 1)) (.fn ((list_type A).rename (· + 1)) (.tVar 0))) (.tVar 0)
    (.fn_wf hAup (.fn_wf hLup (.tVar_wf (by omega)))) ?_
  refine .typed_case (n + 1) _ _ _ _ .unit
    (.prod (A.rename (· + 1)) ((list_type A).rename (· + 1))) (.tVar 0) ?_ ?_ ?_
  · rw [← hunfold]
    refine SynTyped.typed_unroll (n + 1) _ _ _ ?_
    rw [← hlift]
    exact .typed_var _ _ "l" _ (by solve_lookup)
  · exact .typed_lam_anon (n + 1) _ _ .unit (.tVar 0) .unit_wf
      (.typed_var _ _ "n" _ (by solve_lookup))
  · refine .typed_lam (n + 1) _ "h" _
      (.prod (A.rename (· + 1)) ((list_type A).rename (· + 1))) (.tVar 0)
      (.prod_wf hAup hLup) ?_
    refine .typed_app (n + 1) _ _ _ ((list_type A).rename (· + 1)) (.tVar 0) ?_ ?_
    · exact .typed_app (n + 1) _ _ _ (A.rename (· + 1)) _
        (.typed_var _ _ "hf" _ (by solve_lookup))
        (.typed_fst (n + 1) _ _ (A.rename (· + 1)) ((list_type A).rename (· + 1))
          (.typed_var _ _ "h" _ (by solve_lookup)))
    · exact .typed_snd (n + 1) _ _ (A.rename (· + 1)) ((list_type A).rename (· + 1))
        (.typed_var _ _ "h" _ (by solve_lookup))

end Lists

/-! ### The stack -/

/-- `∃ α. (Unit → α) × (α → A → Unit) × (α → Unit + A)`: new, push, pop. -/
def stack_t (A : Ty) : Ty :=
  .exist (.prod (.prod (.fn .unit (.tVar 0)) (.fn (.tVar 0) (.fn (A.rename (· + 1)) .unit)))
    (.fn (.tVar 0) (.sum .unit (A.rename (· + 1)))))

/-- The list interface the stack is built on; an implementation is `mylist_impl` of sheet 5. -/
def list_t (A : Ty) : Ty :=
  .exist (.prod (.prod (.tVar 0) (.fn (A.rename (· + 1)) (.fn (.tVar 0) (.tVar 0))))
    (.all (.fn (.tVar 1) (.fn (.tVar 0)
      (.fn (.fn (A.rename (fun n => n + 2)) (.fn (.tVar 1) (.tVar 0))) (.tVar 0))))))

def mystack : Val :=
  λᵥ: lc,
    Expr.pair (Expr.pair
      -- new
      (Expr.lam .bAnon (Expr.new (Expr.fst (Expr.fst (.var "lc")))))
      -- push
      (λ: st el,
        let: stv := Expr.load (.var "st") in
          Expr.store (.var "st")
            (Expr.app (Expr.app (Expr.snd (Expr.fst (.var "lc"))) (.var "el")) (.var "stv"))))
      -- pop
      (λ: st,
        let: stv := Expr.load (.var "st") in
          Expr.app (Expr.app (Expr.app (Expr.tApp (Expr.snd (.var "lc"))) (.var "stv"))
            (Expr.injL (.lit .litUnit)))
            (λ: h rstv, seqE (Expr.store (.var "st") (.var "rstv")) (Expr.injR (.var "h"))))

def make_mystack : Val :=
  .tLamV (λ: lc, unpackE (.bNamed "lc") (.var "lc") (Expr.pack (Expr.app mystack.toExpr
    (.var "lc"))))

/-- The list interface at representation type `#0` and element type `#1`; not in the Rocq file,
which lets `solve_typing` infer it. -/
def listIface : Ty :=
  .prod (.prod (.tVar 0) (.fn (.tVar 1) (.fn (.tVar 0) (.tVar 0))))
    (.all (.fn (.tVar 1) (.fn (.tVar 0)
      (.fn (.fn (.tVar 2) (.fn (.tVar 1) (.tVar 0))) (.tVar 0)))))

/-- The stack triple at representation type `Ref #0` and element type `#1`. -/
def stackTriple : Ty :=
  .prod (.prod (.fn .unit (.ref (.tVar 0))) (.fn (.ref (.tVar 0)) (.fn (.tVar 1) .unit)))
    (.fn (.ref (.tVar 0)) (.sum .unit (.tVar 1)))

theorem mystack_typed (Θ : HeapContext) (m : Nat) (Γ : TypingContext) (hm : 2 ≤ m) :
    SynTyped Θ m Γ mystack.toExpr (.fn listIface stackTriple) := by
  have h0 : (0 : Nat) < m := by omega
  have h1 : (1 : Nat) < m := by omega
  refine .typed_lam m Γ "lc" _ listIface stackTriple (by solve_type_wf) ?_
  refine .typed_pair m _ _ _ _ (.fn (.ref (.tVar 0)) (.sum .unit (.tVar 1))) ?_ ?_
  · refine .typed_pair m _ _ _ (.fn .unit (.ref (.tVar 0)))
      (.fn (.ref (.tVar 0)) (.fn (.tVar 1) .unit)) ?_ ?_
    · -- new
      refine .typed_lam_anon m _ _ .unit (.ref (.tVar 0)) .unit_wf ?_
      refine .typed_new m _ _ (.tVar 0) ?_
      exact .typed_fst m _ _ (.tVar 0) (.fn (.tVar 1) (.fn (.tVar 0) (.tVar 0)))
        (.typed_fst m _ _ _ _ (.typed_var _ _ "lc" _ (by solve_lookup)))
    · -- push
      refine .typed_lam m _ "st" _ (.ref (.tVar 0)) _ (by solve_type_wf) ?_
      refine .typed_lam m _ "el" _ (.tVar 1) .unit (by solve_type_wf) ?_
      refine .typed_app m _ _ _ (.tVar 0) .unit ?_
        (.typed_load m _ _ (.tVar 0) (.typed_var _ _ "st" _ (by solve_lookup)))
      refine .typed_lam m _ "stv" _ (.tVar 0) .unit (by solve_type_wf) ?_
      refine .typed_store m _ _ _ (.tVar 0) (.typed_var _ _ "st" _ (by solve_lookup)) ?_
      refine .typed_app m _ _ _ (.tVar 0) (.tVar 0) ?_
        (.typed_var _ _ "stv" _ (by solve_lookup))
      refine .typed_app m _ _ _ (.tVar 1) (.fn (.tVar 0) (.tVar 0)) ?_
        (.typed_var _ _ "el" _ (by solve_lookup))
      exact .typed_snd m _ _ (.tVar 0) (.fn (.tVar 1) (.fn (.tVar 0) (.tVar 0)))
        (.typed_fst m _ _ _ _ (.typed_var _ _ "lc" _ (by solve_lookup)))
  · -- pop
    refine .typed_lam m _ "st" _ (.ref (.tVar 0)) (.sum .unit (.tVar 1))
      (by solve_type_wf) ?_
    refine .typed_app m _ _ _ (.tVar 0) (.sum .unit (.tVar 1)) ?_
      (.typed_load m _ _ (.tVar 0) (.typed_var _ _ "st" _ (by solve_lookup)))
    refine .typed_lam m _ "stv" _ (.tVar 0) (.sum .unit (.tVar 1)) (by solve_type_wf) ?_
    refine .typed_app m _ _ _
      (.fn (.tVar 1) (.fn (.tVar 0) (.sum .unit (.tVar 1)))) (.sum .unit (.tVar 1)) ?_ ?_
    · refine .typed_app m _ _ _ (.sum .unit (.tVar 1)) _ ?_
        (.typed_injL m _ _ .unit (.tVar 1) (by solve_type_wf) (.typed_lit_unit m _))
      refine .typed_app m _ _ _ (.tVar 0) _ ?_ (.typed_var _ _ "stv" _ (by solve_lookup))
      rw [show (Ty.fn (.tVar 0) (.fn (.sum .unit (.tVar 1))
            (.fn (.fn (.tVar 1) (.fn (.tVar 0) (.sum .unit (.tVar 1))))
              (.sum .unit (.tVar 1)))))
          = (Ty.fn (.tVar 1) (.fn (.tVar 0)
              (.fn (.fn (.tVar 2) (.fn (.tVar 1) (.tVar 0))) (.tVar 0)))).subst1
            (.sum .unit (.tVar 1)) from rfl]
      refine .typed_tApp m _ _ _ (.sum .unit (.tVar 1)) (by solve_type_wf) ?_
      exact .typed_snd m _ _ (.prod (.tVar 0) (.fn (.tVar 1) (.fn (.tVar 0) (.tVar 0)))) _
        (.typed_var _ _ "lc" _ (by solve_lookup))
    · refine .typed_lam m _ "h" _ (.tVar 1) _ (by solve_type_wf) ?_
      refine .typed_lam m _ "rstv" _ (.tVar 0) (.sum .unit (.tVar 1)) (by solve_type_wf) ?_
      refine .typed_app m _ _ _ .unit (.sum .unit (.tVar 1)) ?_ ?_
      · exact .typed_lam_anon m _ _ .unit (.sum .unit (.tVar 1)) .unit_wf
          (.typed_injR m _ _ .unit (.tVar 1) .unit_wf
            (.typed_var _ _ "h" _ (by solve_lookup)))
      · exact .typed_store m _ _ _ (.tVar 0) (.typed_var _ _ "st" _ (by solve_lookup))
          (.typed_var _ _ "rstv" _ (by solve_lookup))

theorem make_mystack_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) :
    SynTyped Θ n Γ make_mystack.toExpr (.all (.fn (list_t (.tVar 0)) (stack_t (.tVar 0)))) := by
  refine .typed_tLam n Γ _ _ ?_
  refine .typed_lam (n + 1) _ "lc" _ (list_t (.tVar 0)) (stack_t (.tVar 0))
    (by solve_type_wf) ?_
  refine .typed_unpack (n + 1) _ "lc" _ _ listIface (stack_t (.tVar 0))
    (by solve_type_wf) (.typed_var _ _ "lc" _ (by solve_lookup)) ?_
  rw [show ((stack_t (.tVar 0)).rename (· + 1) : Ty)
      = .exist (.prod (.prod (.fn .unit (.tVar 0)) (.fn (.tVar 0) (.fn (.tVar 2) .unit)))
          (.fn (.tVar 0) (.sum .unit (.tVar 2)))) from rfl]
  refine .typed_pack (n + 2) _ _ _ (.ref (.tVar 0)) (by solve_type_wf) (by solve_type_wf) ?_
  rw [show (Ty.prod (.prod (.fn .unit (.tVar 0)) (.fn (.tVar 0) (.fn (.tVar 2) .unit)))
        (.fn (.tVar 0) (.sum .unit (.tVar 2)))).subst1 (.ref (.tVar 0)) = stackTriple from rfl]
  refine .typed_app (n + 2) _ _ _ listIface stackTriple ?_
    (.typed_var _ _ "lc" _ (by solve_lookup))
  refine mystack_typed _ _ _ ?_
  omega

/-! ## Exercise 2 (LN 46): obfuscated code -/

def obf_expr : Expr :=
  let: x := Expr.new (λ: x, Expr.binOp .plusOp (.var "x") (.var "x")) in
    let: f := (λ: g,
        let: f := Expr.load (.var "x") in
          seqE (Expr.store (.var "x") (.var "g"))
            (Expr.app (.var "f") (.lit (.litInt 11)))) in
      Expr.binOp .plusOp
        (Expr.app (.var "f") (λ: x, Expr.app (.var "f") (Expr.lam .bAnon (.var "x"))))
        (Expr.app (.var "f") (λ: x, Expr.binOp .plusOp (.var "x") (.lit (.litInt 9))))

/-- The reflexive-transitive closure of `ContextualStep`; Rocq's `rtc contextual_step`.  The port
otherwise counts steps (`Nsteps`), which is what the logical relation needs. -/
def ContextualSteps (s s' : Expr × Heap) : Prop := ∃ n, Nsteps n s s'

theorem ContextualSteps.refl {s : Expr × Heap} : ContextualSteps s s := ⟨0, .zero⟩

theorem ContextualSteps.step {s₁ s₂ s₃ : Expr × Heap} (h : ContextualStep s₁ s₂)
    (hs : ContextualSteps s₂ s₃) : ContextualSteps s₁ s₃ := by
  obtain ⟨n, hn⟩ := hs
  exact ⟨n + 1, .step h hn⟩

theorem nsteps_fill {K : Ectx} {n : Nat} {s s' : Expr × Heap} (hs : Nsteps n s s') :
    Nsteps n (fill K s.1, s.2) (fill K s'.1, s'.2) := by
  induction hs with
  | zero => exact .zero
  | @step s₁ s₂ n s₃ hstep _ ih =>
    obtain ⟨e₁, h₁⟩ := s₁
    obtain ⟨e₂, h₂⟩ := s₂
    exact .step (fill_contextual_step hstep) ih

/-- Reductions lift through an evaluation context. -/
theorem rtc_contextual_step_fill (K : Ectx) (e e' : Expr) (h h' : Heap)
    (hs : ContextualSteps (e, h) (e', h')) :
    ContextualSteps (fill K e, h) (fill K e', h') := by
  obtain ⟨n, hn⟩ := hs
  exact ⟨n, nsteps_fill (s := (e, h)) (s' := (e', h')) hn⟩

/-- The two functions the single cell holds during the run. -/
private def obfV0 : Val := .lamV (.bNamed "x") (Expr.binOp .plusOp (.var "x") (.var "x"))

private def obfV9 : Val :=
  .lamV (.bNamed "x") (Expr.binOp .plusOp (.var "x") (.lit (.litInt 9)))

-- The reduction is written as one uniform simp set per step; not every lemma fires every time.
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem obf_expr_eval :
    ∃ h' : Heap, ContextualSteps (obf_expr, Heap.empty) (Expr.lit (.litInt 42), h') := by
  apply Exists.intro
  -- allocate the cell
  refine .step (contextual_step_app_r _ (base_contextual_step
    (BaseStep.newS _ obfV0 ⟨0⟩ Heap.empty rfl rfl))) ?_
  -- the two `let`s
  refine .step (base_contextual_step (BaseStep.betaS _ _ _ _ trivial)) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (base_contextual_step (BaseStep.betaS _ _ _ _ trivial)) ?_
  simp +decide only [subst', subst, reduceIte]
  -- the right summand runs first
  refine .step (contextual_step_binop_r _ _
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_r _ _ (contextual_step_app_r _
    (base_contextual_step (BaseStep.loadS ⟨0⟩ obfV0 _ (by simp [Heap.insert]))))) ?_
  refine .step (contextual_step_binop_r _ _
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte, obfV0]
  refine .step (contextual_step_binop_r _ _ (contextual_step_app_r _
    (base_contextual_step (BaseStep.storeS ⟨0⟩ _ _ _ (by simp [Heap.insert]) rfl)))) ?_
  refine .step (contextual_step_binop_r _ _
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_r _ _
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_r _ _
    (base_contextual_step (BaseStep.binOpS _ _ _ _ _ _ _ rfl rfl rfl))) ?_
  simp +decide only [Val.toExpr, Int.reduceAdd]
  -- now the left summand
  refine .step (contextual_step_binop_l _ trivial
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_l _ trivial (contextual_step_app_r _
    (base_contextual_step (BaseStep.loadS ⟨0⟩ obfV9 _ (by simp [Heap.insert, obfV9]))))) ?_
  refine .step (contextual_step_binop_l _ trivial
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte, obfV9]
  refine .step (contextual_step_binop_l _ trivial (contextual_step_app_r _
    (base_contextual_step (BaseStep.storeS ⟨0⟩ _ _ _ (by simp [Heap.insert]) rfl)))) ?_
  refine .step (contextual_step_binop_l _ trivial
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_l _ trivial
    (base_contextual_step (BaseStep.betaS _ _ _ _ trivial))) ?_
  simp +decide only [subst', subst, reduceIte]
  refine .step (contextual_step_binop_l _ trivial
    (base_contextual_step (BaseStep.binOpS _ _ _ _ _ _ _ rfl rfl rfl))) ?_
  simp +decide only [Val.toExpr, Int.reduceAdd]
  refine .step (base_contextual_step (BaseStep.binOpS _ _ _ _ _ _ _ rfl rfl rfl)) ?_
  simp +decide only [Val.toExpr, Int.reduceAdd]
  exact .refl

/-! ## Exercise 4 (LN 48): Landin's knot and Fibonacci -/

def knot : Val :=
  λᵥ: f,
    let: x := Expr.new (λ: x, (.lit (.litInt 0))) in
      let: g := Expr.app (.var "f")
          (λ: y, Expr.app (Expr.load (.var "x")) (.var "y")) in
        seqE (Expr.store (.var "x") (.var "g")) (.var "g")

def fibonacci : Val :=
  λᵥ: n,
    Expr.app (Expr.app knot.toExpr
      (λ: rec n,
        Expr.ite (Expr.binOp .eqOp (.var "n") (.lit (.litInt 0))) (.lit (.litInt 0))
          (Expr.ite (Expr.binOp .eqOp (.var "n") (.lit (.litInt 1))) (.lit (.litInt 1))
            (Expr.binOp .plusOp
              (Expr.app (.var "rec") (Expr.binOp .minusOp (.var "n") (.lit (.litInt 1))))
              (Expr.app (.var "rec")
                (Expr.binOp .minusOp (.var "n") (.lit (.litInt 2))))))))
      (.var "n")

theorem knot_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) (A : Ty) (hA : TypeWf n A) :
    SynTyped Θ n Γ knot.toExpr (.fn (.fn (.fn A .int) (.fn A .int)) (.fn A .int)) := by
  refine .typed_lam n Γ "f" _ (.fn (.fn A .int) (.fn A .int)) (.fn A .int)
    (by solve_type_wf) ?_
  refine .typed_app n _ _ _ (.ref (.fn A .int)) (.fn A .int) ?_ ?_
  · refine .typed_lam n _ "x" _ (.ref (.fn A .int)) (.fn A .int) (by solve_type_wf) ?_
    refine .typed_app n _ _ _ (.fn A .int) (.fn A .int) ?_ ?_
    · refine .typed_lam n _ "g" _ (.fn A .int) (.fn A .int) (by solve_type_wf) ?_
      refine .typed_app n _ _ _ .unit (.fn A .int) ?_ ?_
      · exact .typed_lam_anon n _ _ .unit (.fn A .int) .unit_wf
          (.typed_var _ _ "g" _ (by solve_lookup))
      · exact .typed_store n _ _ _ (.fn A .int) (.typed_var _ _ "x" _ (by solve_lookup))
          (.typed_var _ _ "g" _ (by solve_lookup))
    · refine .typed_app n _ _ _ (.fn A .int) (.fn A .int)
        (.typed_var _ _ "f" _ (by solve_lookup)) ?_
      refine .typed_lam n _ "y" _ A .int hA ?_
      exact .typed_app n _ _ _ A .int
        (.typed_load n _ _ (.fn A .int) (.typed_var _ _ "x" _ (by solve_lookup)))
        (.typed_var _ _ "y" _ (by solve_lookup))
  · refine .typed_new n _ _ (.fn A .int) ?_
    exact .typed_lam n _ "x" _ A .int hA (.typed_lit_int n _ 0)

theorem fibonacci_typed (Θ : HeapContext) (n : Nat) (Γ : TypingContext) :
    SynTyped Θ n Γ fibonacci.toExpr (.fn .int .int) := by
  refine .typed_lam n Γ "n" _ .int .int .int_wf ?_
  refine .typed_app n _ _ _ .int .int ?_ (.typed_var _ _ "n" _ (by solve_lookup))
  refine .typed_app n _ _ _ (.fn (.fn .int .int) (.fn .int .int)) (.fn .int .int)
    (knot_typed Θ n _ .int .int_wf) ?_
  refine .typed_lam n _ "rec" _ (.fn .int .int) (.fn .int .int) (by solve_type_wf) ?_
  refine .typed_lam n _ "n" _ .int .int .int_wf ?_
  solve_typing

end SystemFMuState.Syn
