import LeanLR.TypeSystems.SystemFMu.Types
import LeanLR.TypeSystems.SystemFMu.TypeSafety
import LeanLR.TypeSystems.SystemFMu.Pure
import Lean

/-!
# System F + μ: typing automation

`systemf_mu/tactics.v`'s `solve_typing` and `map_solver`, as Lean tactics; the same shape as
`SystemF/Tactics.lean`, with `typed_roll`/`typed_unroll` added. The constructors that need a type
to be guessed (`typed_tApp`, `typed_pack`, `typed_unpack`, `typed_roll`, `typed_unroll`) are left
to the caller.
-/

open Lean Elab Tactic
open Iris.Std

namespace SystemFMu

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
        | (refine TypeWf.mu_wf ?_ <;> solve_type_wf)
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
guessed. -/
macro "solve_typing" : tactic => `(tactic| repeat (any_goals typing_step))

/-! ## Deterministic reduction

`systemf_mu/pure.v`'s `do_det_step`: find the unique redex of a closed expression and take the
step, descending through evaluation contexts. -/

/-- Discharges an `Expr.isVal` goal. -/
syntax "solve_isVal" : tactic

macro_rules
  | `(tactic| solve_isVal) =>
    `(tactic| first
        | assumption
        | exact val_isVal _
        | trivial
        | (refine And.intro ?_ ?_ <;> solve_isVal)
        | (show Expr.isVal _; simp only [Val.toExpr]; solve_isVal)
        | decide)

/-- Takes one deterministic step, descending through evaluation contexts. -/
syntax "det_step1" : tactic

macro_rules
  | `(tactic| det_step1) =>
    `(tactic| first
        | assumption
        | exact det_step_beta _ _ _ (by solve_isVal)
        | exact det_step_tBeta _
        | exact det_step_unpack _ _ _ (by solve_isVal)
        | exact det_step_if_true _ _
        | exact det_step_if_false _ _
        | exact det_step_fst _ _ (by solve_isVal) (by solve_isVal)
        | exact det_step_snd _ _ (by solve_isVal) (by solve_isVal)
        | exact det_step_caseL _ _ _ (by solve_isVal)
        | exact det_step_caseR _ _ _ (by solve_isVal)
        | exact det_step_unroll _ (by solve_isVal)
        | exact det_step_binOp _ _ _ _ _ _ rfl rfl rfl
        | exact det_step_unOp _ _ _ _ rfl rfl
        | exact det_step_pair_r _ (by det_step1)
        | exact det_step_pair_l (by solve_isVal) (by det_step1)
        | exact det_step_binop_r _ _ (by det_step1)
        | exact det_step_binop_l _ (by solve_isVal) (by det_step1)
        | exact det_step_if _ _ (by det_step1)
        | exact det_step_app_r _ (by det_step1)
        | exact det_step_app_l (by solve_isVal) (by det_step1)
        | exact det_step_snd_lift (by det_step1)
        | exact det_step_fst_lift (by det_step1))

end SystemFMu
