import LeanLR.TypeSystems.SystemFMuState.TypeSafety
import LeanLR.TypeSystems.SystemFMuState.Execution
import Lean

/-!
# System F + μ + state: typing automation

`systemf_mu_state/tactics.v`'s `solve_typing`, for the syntactic type system of `types.v`
(`SystemFMuState.Syn`). Same shape as `SystemF/Tactics.lean`; `typed_tApp`, `typed_pack`,
`typed_unpack`, `typed_roll` and `typed_unroll` are left to the caller, since they need a type to
be guessed.
-/

open Lean Elab Tactic
open Iris.Std

namespace SystemFMuState.Syn

/-- Fails when the goal still contains a metavariable. -/
elab "no_mvars" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  if g.hasExprMVar then throwError "goal still contains metavariables"

theorem lookup_here {Γ : TypingContext} {x : String} {A : Ty} :
    get? (M := TyMapStr) (insert (M := TyMapStr) Γ x A) x = some A :=
  LawfulPartialMap.get?_insert_eq (M := TyMapStr) rfl

theorem lookup_there {Γ : TypingContext} {x y : String} {A B : Ty} (h : x ≠ y)
    (hy : get? (M := TyMapStr) Γ y = some B) :
    get? (M := TyMapStr) (insert (M := TyMapStr) Γ x A) y = some B := by
  rw [LawfulPartialMap.get?_insert_ne (M := TyMapStr) h]
  exact hy

/-- Discharges a `get? Γ x = some A` goal. -/
syntax "solve_lookup" : tactic

macro_rules
  | `(tactic| solve_lookup) =>
    `(tactic| first
        | assumption
        | exact lookup_here
        | (rw [shiftCtx_insert]; solve_lookup)
        | (rw [shiftCtx_empty]; solve_lookup)
        | (refine lookup_there ?_ ?_
           · decide
           · solve_lookup))

/-- Discharges a `TypeWf n A` goal. -/
syntax "solve_type_wf" : tactic

macro_rules
  | `(tactic| solve_type_wf) =>
    `(tactic| (no_mvars; first
        | assumption
        | exact TypeWf.int_wf
        | exact TypeWf.bool_wf
        | exact TypeWf.unit_wf
        | (refine TypeWf.tVar_wf ?_; omega)
        | (simp only [Ty.rename]; solve_type_wf)
        | (refine TypeWf.fn_wf ?_ ?_ <;> solve_type_wf)
        | (refine TypeWf.prod_wf ?_ ?_ <;> solve_type_wf)
        | (refine TypeWf.sum_wf ?_ ?_ <;> solve_type_wf)
        | (refine TypeWf.all_wf ?_ <;> solve_type_wf)
        | (refine TypeWf.exist_wf ?_ <;> solve_type_wf)
        | (refine TypeWf.mu_wf ?_ <;> solve_type_wf)
        | (refine TypeWf.ref_wf ?_ <;> solve_type_wf)
        | (refine TypeWf.rename (· + 1) _ _ _ ?_ (by assumption) <;> (intro m hm; omega))
        | (refine TypeWf.rename (fun m => m + 2) _ _ _ ?_ (by assumption) <;>
            (intro m hm; omega))
        | (refine TypeWf.mono ?_ _ (by omega) <;> solve_type_wf)))

/-- One step of `solve_typing`. -/
syntax "typing_step" : tactic

macro_rules
  | `(tactic| typing_step) =>
    `(tactic| first
        | assumption
        | apply SynTyped.typed_lit_int
        | apply SynTyped.typed_lit_bool
        | apply SynTyped.typed_lit_unit
        | (apply SynTyped.typed_var; solve_lookup)
        | apply SynTyped.typed_lam
        | apply SynTyped.typed_lam_anon
        | apply SynTyped.typed_tLam
        | apply SynTyped.typed_pair
        | apply SynTyped.typed_fst
        | apply SynTyped.typed_snd
        | apply SynTyped.typed_injL
        | apply SynTyped.typed_injR
        | apply SynTyped.typed_case
        | apply SynTyped.typed_if
        | apply SynTyped.typed_unOp
        | apply SynTyped.typed_binOp
        | apply SynTyped.typed_app
        | apply SynTyped.typed_new
        | apply SynTyped.typed_load
        | apply SynTyped.typed_store
        | apply UnOpTyped.neg_typed
        | apply UnOpTyped.minus_typed
        | apply BinOpTyped.plus_typed
        | apply BinOpTyped.minus_typed
        | apply BinOpTyped.mult_typed
        | apply BinOpTyped.lt_typed
        | apply BinOpTyped.le_typed
        | apply BinOpTyped.eq_typed
        | solve_type_wf)

/-- `solve_typing` closes the goals of a typing derivation that do not need a type to be
guessed. -/
macro "solve_typing" : tactic => `(tactic| repeat (any_goals typing_step))

/-! ## Reduction

A search for the unique redex of a closed expression, in the spirit of `pure.v`'s
`do_det_step`, but over `ContextualStep` so that it can also take heap steps. -/

/-- Discharges an `Expr.isVal` goal. -/
syntax "solve_isVal" : tactic

macro_rules
  | `(tactic| solve_isVal) =>
    `(tactic| first
        | assumption
        | exact val_isVal _
        | trivial
        | (refine And.intro ?_ ?_ <;> solve_isVal)
        | decide)

/-- Takes one contextual step, descending through evaluation contexts. -/
syntax "ctx_step" : tactic

macro_rules
  | `(tactic| ctx_step) =>
    `(tactic| first
        | assumption
        | exact base_contextual_step (BaseStep.betaS _ _ _ _ (by solve_isVal))
        | exact base_contextual_step (BaseStep.tBetaS _ _)
        | exact base_contextual_step (BaseStep.unpackS _ _ _ _ (by solve_isVal))
        | exact base_contextual_step (BaseStep.ifTrueS _ _ _)
        | exact base_contextual_step (BaseStep.ifFalseS _ _ _)
        | exact base_contextual_step (BaseStep.fstS _ _ _ (by solve_isVal) (by solve_isVal))
        | exact base_contextual_step (BaseStep.sndS _ _ _ (by solve_isVal) (by solve_isVal))
        | exact base_contextual_step (BaseStep.caseLS _ _ _ _ (by solve_isVal))
        | exact base_contextual_step (BaseStep.caseRS _ _ _ _ (by solve_isVal))
        | exact base_contextual_step (BaseStep.unrollS _ _ (by solve_isVal))
        | exact base_contextual_step (BaseStep.binOpS _ _ _ _ _ _ _ rfl rfl rfl)
        | exact base_contextual_step (BaseStep.unOpS _ _ _ _ _ rfl rfl)
        | exact base_contextual_step (BaseStep.loadS _ _ _ (by simp [Heap.insert]))
        | exact base_contextual_step (BaseStep.storeS _ _ _ _ (by simp [Heap.insert]) rfl)
        | exact contextual_step_app_r _ (by ctx_step)
        | exact contextual_step_app_l (by solve_isVal) (by ctx_step)
        | exact contextual_step_binop_r _ _ (by ctx_step)
        | exact contextual_step_binop_l _ (by solve_isVal) (by ctx_step)
        | exact contextual_step_if _ _ (by ctx_step)
        | exact contextual_step_load (by ctx_step)
        | exact contextual_step_store_r _ (by ctx_step)
        | exact contextual_step_store_l (by solve_isVal) (by ctx_step)
        | exact contextual_step_new (by ctx_step)
        | exact contextual_step_pair_r _ (by ctx_step)
        | exact contextual_step_pair_l (by solve_isVal) (by ctx_step)
        | exact contextual_step_fst (by ctx_step)
        | exact contextual_step_snd (by ctx_step)
        | exact contextual_step_injl (by ctx_step)
        | exact contextual_step_injr (by ctx_step)
        | exact contextual_step_case _ _ (by ctx_step)
        | exact contextual_step_roll (by ctx_step)
        | exact contextual_step_unroll (by ctx_step)
        | exact contextual_step_tapp (by ctx_step)
        | exact contextual_step_pack (by ctx_step)
        | exact contextual_step_unpack _ _ (by ctx_step))

end SystemFMuState.Syn
