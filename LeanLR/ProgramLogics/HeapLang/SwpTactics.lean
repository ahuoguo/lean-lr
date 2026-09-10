import LeanLR.ProgramLogics.HoareLib
import LeanLR.ProgramLogics.HeapLang.NoLater

/-!
# Pure steps under the sequential WP

`iris-lean`'s `wp_pures` only fires on a `WP` goal, and the course's weakest precondition is the
sequential one. `swp_pures` below is the same idea spelled out with `HoareLib`'s `pure_step_*`
rules: try each of them in turn, and repeat.

`swp_pure_later` is the variant that leaves a `▷` behind. It is weaker as a rule, but it is what
strips the later from a Löb hypothesis, so a recursive-function proof takes its first step with
`swp_pure_later` and the rest with `swp_pures`.
-/

namespace ProgramLogics

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

/-! ## Working inside the sequential WP

`swp s E E e Φ` *is* `|={E,∅}=> WP e @ s;∅ {{v, |={∅,E}=> Φ v}}`. Giving the mask up once at the
start therefore turns a sequential-WP goal into an ordinary weakest precondition, on which every
one of `iris-lean`'s heap_lang tactics fires — including `wp_pures`, which strips a later from
every hypothesis and so discharges a Löb induction.

What is left over is a closing update `|={∅,E}=> emp`. It is what lets a sequential-WP *fact* be
used again from inside: hand the mask back with it, run the fact's `|={E,∅}=>`, and the two
compose to the `|={∅,∅}=>` that a mask-`∅` weakest precondition absorbs. -/

section Bridge

variable {hlc : outParam HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}

/-- Give the mask up once, and a sequential WP becomes an ordinary one. -/
theorem wp_of_closing :
    iprop((|={∅, E}=> emp) -∗ WP e @ s ; (∅ : CoPset) {{ v, |={∅, E}=> Φ v }}) ⊢
      swp s E E e Φ := by
  iintro H
  unfold swp
  imod (fupd_mask_subseteq (E2 := (∅ : CoPset)) (by simp)) with Hcl
  imodintro
  iapply H $$ Hcl

/-- Spend the closing update to run a sequential WP inside the mask-`∅` one. -/
theorem swp_to_wp : ⊢@{IProp GF}
    iprop(|={∅, E}=> emp) -∗ swp s E E e Φ -∗
      WP e @ s ; (∅ : CoPset) {{ v, |={∅, E}=> Φ v }} := by
  iintro Hcl H
  iapply fupd_wp
  imod Hcl
  unfold swp
  imod H
  imodintro
  iexact H

end Bridge

/-- Turn a sequential-WP goal into the mask-`∅` weakest precondition it is defined as, naming the
closing update. -/
macro "swp_enter " h:introPat : tactic => `(tactic| (iapply wp_of_closing; iintro $h))

/-! ## Evaluation contexts

`swp_bind` wants its context as a function together with a `Language.Context` instance. Each frame
of `ECtxItem` gives one; these are the instances that make `iapply swp_bind (K := fun e => …)`
elaborate. -/

section Contexts

open Iris.HeapLang Iris.ProgramLogic

instance ctxAppL (v : Val) : Language.Context (fun e => Exp.app e (Exp.ofVal v)) :=
  show Language.Context (fill [ECtxItem.appL v]) from inferInstance
instance ctxAppR (e₁ : Exp) : Language.Context (fun e => Exp.app e₁ e) :=
  show Language.Context (fill [ECtxItem.appR e₁]) from inferInstance
instance ctxUnOp (op : UnOp) : Language.Context (fun e => Exp.unop op e) :=
  show Language.Context (fill [ECtxItem.unOp op]) from inferInstance
instance ctxBinOpL (op : BinOp) (v : Val) :
    Language.Context (fun e => Exp.binop op e (Exp.ofVal v)) :=
  show Language.Context (fill [ECtxItem.binOpL op v]) from inferInstance
instance ctxBinOpR (op : BinOp) (e₁ : Exp) : Language.Context (fun e => Exp.binop op e₁ e) :=
  show Language.Context (fill [ECtxItem.binOpR op e₁]) from inferInstance
instance ctxIf (e₁ e₂ : Exp) : Language.Context (fun e => Exp.if e e₁ e₂) :=
  show Language.Context (fill [ECtxItem.if e₁ e₂]) from inferInstance
instance ctxPairL (v : Val) : Language.Context (fun e => Exp.pair e (Exp.ofVal v)) :=
  show Language.Context (fill [ECtxItem.pairL v]) from inferInstance
instance ctxPairR (e₁ : Exp) : Language.Context (fun e => Exp.pair e₁ e) :=
  show Language.Context (fill [ECtxItem.pairR e₁]) from inferInstance
instance ctxFst : Language.Context (fun e => Exp.fst e) :=
  show Language.Context (fill [ECtxItem.fst]) from inferInstance
instance ctxSnd : Language.Context (fun e => Exp.snd e) :=
  show Language.Context (fill [ECtxItem.snd]) from inferInstance
instance ctxInjL : Language.Context (fun e => Exp.injL e) :=
  show Language.Context (fill [ECtxItem.injL]) from inferInstance
instance ctxInjR : Language.Context (fun e => Exp.injR e) :=
  show Language.Context (fill [ECtxItem.injR]) from inferInstance
instance ctxCase (e₁ e₂ : Exp) : Language.Context (fun e => Exp.case e e₁ e₂) :=
  show Language.Context (fill [ECtxItem.case e₁ e₂]) from inferInstance
instance ctxAllocNR (e₁ : Exp) : Language.Context (fun e => Exp.allocN e₁ e) :=
  show Language.Context (fill [ECtxItem.allocNR e₁]) from inferInstance
instance ctxLoad : Language.Context (fun e => Exp.load e) :=
  show Language.Context (fill [ECtxItem.load]) from inferInstance
instance ctxStoreL (v : Val) : Language.Context (fun e => Exp.store e (Exp.ofVal v)) :=
  show Language.Context (fill [ECtxItem.storeL v]) from inferInstance
instance ctxStoreR (e₁ : Exp) : Language.Context (fun e => Exp.store e₁ e) :=
  show Language.Context (fill [ECtxItem.storeR e₁]) from inferInstance

end Contexts

/-! ### Binding one frame

`swp_bind` wants its context as a function; a tactic's unifier will not see through
`ProgramLogic.fill`, so each frame gets its own rule with the frame written out. -/

section Binds

variable {hlc : outParam HasLC} {GF : BundledGFunctors} [IrisGS_gen hlc Exp GF]
variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Exp} {Φ : Val → IProp GF}

theorem swp_bind_appL (w : Val) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.app (Exp.ofVal v) (Exp.ofVal w)) Φ) ⊢
      swp s E₁ E₂ (Exp.app e (Exp.ofVal w)) Φ := swp_bind' (fun e => Exp.app e (Exp.ofVal w))
theorem swp_bind_appR (e₁ : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.app e₁ (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.app e₁ e) Φ := swp_bind' (fun e => Exp.app e₁ e)
theorem swp_bind_unOp (op : UnOp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.unop op (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.unop op e) Φ := swp_bind' (fun e => Exp.unop op e)
theorem swp_bind_binOpL (op : BinOp) (w : Val) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.binop op (Exp.ofVal v) (Exp.ofVal w)) Φ) ⊢
      swp s E₁ E₂ (Exp.binop op e (Exp.ofVal w)) Φ :=
  swp_bind' (fun e => Exp.binop op e (Exp.ofVal w))
theorem swp_bind_binOpR (op : BinOp) (e₁ : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.binop op e₁ (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.binop op e₁ e) Φ := swp_bind' (fun e => Exp.binop op e₁ e)
theorem swp_bind_if (ea eb : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.if (Exp.ofVal v) ea eb) Φ) ⊢
      swp s E₁ E₂ (Exp.if e ea eb) Φ := swp_bind' (fun e => Exp.if e ea eb)
theorem swp_bind_case (ea eb : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.case (Exp.ofVal v) ea eb) Φ) ⊢
      swp s E₁ E₂ (Exp.case e ea eb) Φ := swp_bind' (fun e => Exp.case e ea eb)
theorem swp_bind_fst :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.fst (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.fst e) Φ := swp_bind' (fun e => Exp.fst e)
theorem swp_bind_snd :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.snd (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.snd e) Φ := swp_bind' (fun e => Exp.snd e)
theorem swp_bind_injL :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.injL (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.injL e) Φ := swp_bind' (fun e => Exp.injL e)
theorem swp_bind_injR :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.injR (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.injR e) Φ := swp_bind' (fun e => Exp.injR e)
theorem swp_bind_pairL (w : Val) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.pair (Exp.ofVal v) (Exp.ofVal w)) Φ) ⊢
      swp s E₁ E₂ (Exp.pair e (Exp.ofVal w)) Φ :=
  swp_bind' (fun e => Exp.pair e (Exp.ofVal w))
theorem swp_bind_pairR (e₁ : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.pair e₁ (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.pair e₁ e) Φ := swp_bind' (fun e => Exp.pair e₁ e)
theorem swp_bind_allocNR (e₁ : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.allocN e₁ (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.allocN e₁ e) Φ := swp_bind' (fun e => Exp.allocN e₁ e)
theorem swp_bind_load :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.load (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.load e) Φ := swp_bind' (fun e => Exp.load e)
theorem swp_bind_storeL (w : Val) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.store (Exp.ofVal v) (Exp.ofVal w)) Φ) ⊢
      swp s E₁ E₂ (Exp.store e (Exp.ofVal w)) Φ :=
  swp_bind' (fun e => Exp.store e (Exp.ofVal w))
theorem swp_bind_storeR (e₁ : Exp) :
    swp s E₁ E₁ e (fun v => swp s E₁ E₂ (Exp.store e₁ (Exp.ofVal v)) Φ) ⊢
      swp s E₁ E₂ (Exp.store e₁ e) Φ := swp_bind' (fun e => Exp.store e₁ e)

end Binds

/-- The head pure steps of heap_lang, each applied through `mk`. -/
macro "swp_pure_with " mk:term : tactic => `(tactic| first
  | iapply ($mk (pure_step_beta _ _ _ _))
  | iapply ($mk (pure_step_if_true _ _))
  | iapply ($mk (pure_step_if_false _ _))
  | iapply ($mk (pure_step_fst _ _))
  | iapply ($mk (pure_step_snd _ _))
  | iapply ($mk (pure_step_match_injl _ _ _))
  | iapply ($mk (pure_step_match_injr _ _ _))
  | iapply ($mk (pure_step_add _ _))
  | iapply ($mk (pure_step_sub _ _))
  | iapply ($mk (pure_step_mul _ _))
  | iapply ($mk (pure_step_rec _ _ _))
  | iapply ($mk (pure_step_pair _ _))
  | iapply ($mk (pure_step_injl _))
  | iapply ($mk (pure_step_injr _)))

/-! ### Pure steps under one frame

`pure_step_fill` is stated over `ProgramLogic.fill`, which a tactic's unifier will not reduce.
These are the same rule with the frame written out, one per `ECtxItem`. -/

section Frames

variable {e₁ e₂ : Exp} (h : PureStep e₁ e₂)
include h

theorem pure_step_appL (w : Val) : PureStep (.app e₁ (.ofVal w)) (.app e₂ (.ofVal w)) :=
  pure_step_fill (fill [ECtxItem.appL w]) h
theorem pure_step_appR (e : Exp) : PureStep (.app e e₁) (.app e e₂) :=
  pure_step_fill (fill [ECtxItem.appR e]) h
theorem pure_step_unOp (op : UnOp) : PureStep (.unop op e₁) (.unop op e₂) :=
  pure_step_fill (fill [ECtxItem.unOp op]) h
theorem pure_step_binOpL (op : BinOp) (w : Val) :
    PureStep (.binop op e₁ (.ofVal w)) (.binop op e₂ (.ofVal w)) :=
  pure_step_fill (fill [ECtxItem.binOpL op w]) h
theorem pure_step_binOpR (op : BinOp) (e : Exp) :
    PureStep (.binop op e e₁) (.binop op e e₂) :=
  pure_step_fill (fill [ECtxItem.binOpR op e]) h
theorem pure_step_ifCtx (ea eb : Exp) : PureStep (.if e₁ ea eb) (.if e₂ ea eb) :=
  pure_step_fill (fill [ECtxItem.if ea eb]) h
theorem pure_step_pairL (w : Val) : PureStep (.pair e₁ (.ofVal w)) (.pair e₂ (.ofVal w)) :=
  pure_step_fill (fill [ECtxItem.pairL w]) h
theorem pure_step_pairR (e : Exp) : PureStep (.pair e e₁) (.pair e e₂) :=
  pure_step_fill (fill [ECtxItem.pairR e]) h
theorem pure_step_fstCtx : PureStep (.fst e₁) (.fst e₂) :=
  pure_step_fill (fill [ECtxItem.fst]) h
theorem pure_step_sndCtx : PureStep (.snd e₁) (.snd e₂) :=
  pure_step_fill (fill [ECtxItem.snd]) h
theorem pure_step_injLCtx : PureStep (.injL e₁) (.injL e₂) :=
  pure_step_fill (fill [ECtxItem.injL]) h
theorem pure_step_injRCtx : PureStep (.injR e₁) (.injR e₂) :=
  pure_step_fill (fill [ECtxItem.injR]) h
theorem pure_step_caseCtx (ea eb : Exp) : PureStep (.case e₁ ea eb) (.case e₂ ea eb) :=
  pure_step_fill (fill [ECtxItem.case ea eb]) h
theorem pure_step_allocNR (e : Exp) : PureStep (.allocN e e₁) (.allocN e e₂) :=
  pure_step_fill (fill [ECtxItem.allocNR e]) h
theorem pure_step_loadCtx : PureStep (.load e₁) (.load e₂) :=
  pure_step_fill (fill [ECtxItem.load]) h
theorem pure_step_storeL (w : Val) : PureStep (.store e₁ (.ofVal w)) (.store e₂ (.ofVal w)) :=
  pure_step_fill (fill [ECtxItem.storeL w]) h
theorem pure_step_storeR (e : Exp) : PureStep (.store e e₁) (.store e e₂) :=
  pure_step_fill (fill [ECtxItem.storeR e]) h

end Frames

/-- One pure step under a sequential WP, at the head or under one evaluation-context frame,
without normalising the substitution it leaves behind. -/
macro "swp_pure_raw" : tactic => `(tactic| first
  | swp_pure_with swp_pure_step
  | swp_pure_with (fun h => swp_pure_step (pure_step_appL h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_appR h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpR h _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpL h _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_ifCtx h _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_caseCtx h _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_loadCtx h))
  | swp_pure_with (fun h => swp_pure_step (pure_step_storeR h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_storeL h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_fstCtx h))
  | swp_pure_with (fun h => swp_pure_step (pure_step_sndCtx h))
  | swp_pure_with (fun h => swp_pure_step (pure_step_injLCtx h))
  | swp_pure_with (fun h => swp_pure_step (pure_step_injRCtx h))
  | swp_pure_with (fun h => swp_pure_step (pure_step_pairR h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_pairL h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_allocNR h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_unOp h _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_appL (pure_step_appL h _) _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_appL (pure_step_appR h _) _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_appR (pure_step_appL h _) _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_appR (pure_step_appR h _) _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpR (pure_step_appL h _) _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpL (pure_step_appL h _) _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpR (pure_step_appR h _) _ _))
  | swp_pure_with (fun h => swp_pure_step (pure_step_binOpL (pure_step_appR h _) _ _))
  | swp_pure_with (fun h =>
      swp_pure_step (pure_step_appL (pure_step_appL (pure_step_appL h _) _) _)))

/-- One pure step, with the substitution it leaves behind normalised — the `wp_expr_simp` set is
`iris-lean`'s own, so this is exactly what `wp_pure` does to the expression. -/
macro "swp_pure" : tactic => `(tactic| (swp_pure_raw; try simp only [wp_expr_simp]))

/-- As many pure steps as apply. -/
macro "swp_pures" : tactic => `(tactic| repeat swp_pure)

/-- One pure step, leaving a `▷` in the goal. -/
macro "swp_pure_later_raw" : tactic => `(tactic| first
  | iapply swp_pure_step_later (pure_step_beta _ _ _ _)
  | iapply swp_pure_step_later (pure_step_if_true _ _)
  | iapply swp_pure_step_later (pure_step_if_false _ _)
  | iapply swp_pure_step_later (pure_step_fst _ _)
  | iapply swp_pure_step_later (pure_step_snd _ _)
  | iapply swp_pure_step_later (pure_step_match_injl _ _ _)
  | iapply swp_pure_step_later (pure_step_match_injr _ _ _)
  | iapply swp_pure_step_later (pure_step_rec _ _ _)
  | iapply swp_pure_step_later (pure_step_pair _ _)
  | iapply swp_pure_step_later (pure_step_injl _)
  | iapply swp_pure_step_later (pure_step_injr _))

/-- `swp_pure_later_raw`, with the substitution it leaves behind normalised. -/
macro "swp_pure_later" : tactic => `(tactic| (swp_pure_later_raw; try simp only [wp_expr_simp]))

end ProgramLogics
