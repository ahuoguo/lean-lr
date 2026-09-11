import LeanLR.TypeSystems.SystemF.Types
import LeanLR.TypeSystems.SystemF.ChurchEncodings
import LeanLR.TypeSystems.SystemF.TypeSafety
import Lean

/-!
# System F: typing automation

`systemf/tactics.v`'s `solve_typing`, `map_solver` and their helpers, as Lean tactics. Rocq's
`eauto`-style `econstructor` loop becomes a `repeat' first | …` over the constructors of
`SynTyped`; the constructors that need a type to be guessed (`typed_tApp`, `typed_pack`,
`typed_unpack`) are left to the caller, exactly as Rocq's script leaves them to
`typed_tapp'`/`eapply`.
-/

open Lean Elab Tactic

namespace SystemF

/-- Fails when the goal still contains a metavariable, so that a solver cannot "solve" a goal by
inventing the type it is about. Rocq writes this as `assert_fails (is_evar _)`. -/
elab "no_mvars" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  if g.hasExprMVar then throwError "goal still contains metavariables"

/-- Discharges a `get? Γ x = some A` goal by walking the chain of `insert`s. -/
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
        | (refine TypeWf.rename (· + 1) _ _ _ (fun m hm => Nat.succ_lt_succ hm) ?_ <;>
            solve_type_wf)
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
guessed. A goal is retried after every pass, since an earlier pass may have been blocked only by
a type that a later one determines — `repeat'` would drop it. -/
macro "solve_typing" : tactic => `(tactic| repeat (any_goals typing_step))

end SystemF
