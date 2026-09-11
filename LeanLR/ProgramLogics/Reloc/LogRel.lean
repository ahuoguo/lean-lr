import LeanLR.ProgramLogics.Reloc.SrcRules
import LeanLR.ProgramLogics.Reloc.PersistentBipred
import LeanLR.ProgramLogics.LogRel.Notation
import LeanLR.ProgramLogics.HeapLang.SwpTactics
import Iris.Instances.Lib.Invariants

/-!
# A binary logical relation for System F + μ + state

`program_logics/reloc/logrel.v`. A *relational* semantic type is a persistent relation on values;
the expression relation `refines e e' Ψ` says that whatever `e` does, the source `e'` can be
driven — through the ghost state of `SrcRules.lean` — to a related value.
-/

open Iris Iris.BI Iris.OFE Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage

namespace ProgramLogics.Reloc

open ProgramLogics.LogRel (tApp tLamV tLam pack packV unpack roll rollV unroll)

variable {hlc : HasLC} {GF : BundledGFunctors} [RelocGS hlc GF]

/-! ## Relational semantic types -/

/-- A relational semantic type: a persistent relation on values. -/
abbrev SemType (GF : BundledGFunctors) := PersistentBipred Val (IProp GF)

/-- A type-variable environment. -/
abbrev Env (GF : BundledGFunctors) := Nat → SemType GF

/-- Rocq's `mk_semtype`. -/
def mkSemType (pred : Val → Val → IProp GF) (h : ∀ v w, Persistent (pred v w)) : SemType GF :=
  ⟨pred, h⟩

/-- Rocq's `τ .:: δ`. -/
def consEnv (τ : SemType GF) (δ : Env GF) : Env GF
  | 0 => τ
  | n + 1 => δ n

@[inherit_doc] notation:30 τ " .:: " δ => consEnv τ δ

theorem consEnv_ne {n : Nat} {τ τ' : SemType GF} {δ δ' : Env GF}
    (hτ : τ ≡{n}≡ τ') (hδ : δ ≡{n}≡ δ') : (τ .:: δ) ≡{n}≡ (τ' .:: δ') := by
  intro k
  cases k with
  | zero => exact hτ
  | succ k => exact hδ k

/-! ## The expression relation -/

/-- The source expression, together with the invariant that tracks it. -/
def srcExpr (e : Exp) : IProp GF := iprop(srcCtx ∗ exprS e)

/-- `e` refines `e'` at `Ψ`: for every source evaluation context, running `e` drives the source
to a value related by `Ψ`. -/
def refines (e e' : Exp) (Ψ : Val → Val → IProp GF) : IProp GF :=
  iprop(∀ K : List ECtxItem, srcExpr (fill K e') -∗
    swp .NotStuck ⊤ ⊤ e (fun v => iprop(∃ v' : Val, srcExpr (fill K hl(v(&v'))) ∗ Ψ v v')))

theorem refines_ne {n : Nat} {e e' : Exp} {Ψ Ψ' : Val → Val → IProp GF}
    (h : ∀ v w, Ψ v w ≡{n}≡ Ψ' v w) : refines e e' Ψ ≡{n}≡ refines e e' Ψ' := by
  refine BI.forall_ne fun K => BI.wand_ne.ne .rfl (swp_ne.ne fun v => ?_)
  exact BI.exists_ne fun v' => BI.sep_ne.ne .rfl (h v v')

theorem refines_value (v w : Val) (Ψ : Val → Val → IProp GF) :
    Ψ v w ⊢ refines hl(v(&v)) hl(v(&w)) Ψ := by
  iintro Hvw
  unfold refines
  iintro %K Hsrc
  iapply swp_value'
  iexists w
  iframe Hsrc Hvw

theorem refines_bind (e₁ e₂ : Exp) (K₁ K₂ : List ECtxItem) (Ψ : Val → Val → IProp GF) :
    refines e₁ e₂ (fun v₁ v₂ => refines (fill K₁ hl(v(&v₁))) (fill K₂ hl(v(&v₂))) Ψ) ⊢
      refines (fill K₁ e₁) (fill K₂ e₂) Ψ := by
  iintro Hrfn
  unfold refines
  iintro %K Hsrc
  ispecialize Hrfn $$ %(K₂ ++ K)
  rw [fill_append]
  ispecialize Hrfn $$ Hsrc
  iapply swp_bind' (fill K₁)
  iapply swp_wand $$ Hrfn
  iintro %v ⟨%v', Hsrc, Hrfn⟩
  rw [fill_append]
  iapply Hrfn $$ Hsrc

/-- Binding a single evaluation-context frame on each side. -/
theorem refines_bind_item (Ki Ki' : ECtxItem) (e₁ e₂ : Exp) (Ψ : Val → Val → IProp GF) :
    refines e₁ e₂ (fun v₁ v₂ => refines (Ki.fill hl(v(&v₁))) (Ki'.fill hl(v(&v₂))) Ψ) ⊢
      refines (Ki.fill e₁) (Ki'.fill e₂) Ψ :=
  refines_bind e₁ e₂ [Ki] [Ki'] Ψ

/-! ### Binding, one frame at a time

As with the sequential-WP tactics, a tactic's unifier will not see through `fill`, so each frame
gets its own lemma with the frame written out. -/

section Bind

variable {e e' : Exp} {Ψ : Val → Val → IProp GF}

theorem refines_bind_appR (f f' : Exp) :
    refines e e' (fun v v' => refines (.app f hl(v(&v))) (.app f' hl(v(&v'))) Ψ) ⊢
      refines (.app f e) (.app f' e') Ψ := refines_bind e e' [.appR f] [.appR f'] Ψ

theorem refines_bind_appL (w w' : Val) :
    refines e e' (fun v v' => refines (.app hl(v(&v)) hl(v(&w))) (.app hl(v(&v')) hl(v(&w'))) Ψ) ⊢
      refines (.app e hl(v(&w))) (.app e' hl(v(&w'))) Ψ :=
  refines_bind e e' [.appL w] [.appL w'] Ψ

theorem refines_bind_binOpR (op : BinOp) (f f' : Exp) :
    refines e e' (fun v v' => refines (.binop op f hl(v(&v))) (.binop op f' hl(v(&v'))) Ψ) ⊢
      refines (.binop op f e) (.binop op f' e') Ψ :=
  refines_bind e e' [.binOpR op f] [.binOpR op f'] Ψ

theorem refines_bind_binOpL (op : BinOp) (w w' : Val) :
    refines e e' (fun v v' =>
        refines (.binop op hl(v(&v)) hl(v(&w))) (.binop op hl(v(&v')) hl(v(&w'))) Ψ) ⊢
      refines (.binop op e hl(v(&w))) (.binop op e' hl(v(&w'))) Ψ :=
  refines_bind e e' [.binOpL op w] [.binOpL op w'] Ψ

theorem refines_bind_unOp (op : UnOp) :
    refines e e' (fun v v' => refines (.unop op hl(v(&v))) (.unop op hl(v(&v'))) Ψ) ⊢
      refines (.unop op e) (.unop op e') Ψ := refines_bind e e' [.unOp op] [.unOp op] Ψ

theorem refines_bind_if (e₁ e₂ e₁' e₂' : Exp) :
    refines e e' (fun v v' => refines (.if hl(v(&v)) e₁ e₂) (.if hl(v(&v')) e₁' e₂') Ψ) ⊢
      refines (.if e e₁ e₂) (.if e' e₁' e₂') Ψ :=
  refines_bind e e' [.if e₁ e₂] [.if e₁' e₂'] Ψ

theorem refines_bind_pairR (f f' : Exp) :
    refines e e' (fun v v' => refines (.pair f hl(v(&v))) (.pair f' hl(v(&v'))) Ψ) ⊢
      refines (.pair f e) (.pair f' e') Ψ := refines_bind e e' [.pairR f] [.pairR f'] Ψ

theorem refines_bind_pairL (w w' : Val) :
    refines e e' (fun v v' =>
        refines (.pair hl(v(&v)) hl(v(&w))) (.pair hl(v(&v')) hl(v(&w'))) Ψ) ⊢
      refines (.pair e hl(v(&w))) (.pair e' hl(v(&w'))) Ψ :=
  refines_bind e e' [.pairL w] [.pairL w'] Ψ

theorem refines_bind_fst :
    refines e e' (fun v v' => refines (.fst hl(v(&v))) (.fst hl(v(&v'))) Ψ) ⊢
      refines (.fst e) (.fst e') Ψ := refines_bind e e' [.fst] [.fst] Ψ

theorem refines_bind_snd :
    refines e e' (fun v v' => refines (.snd hl(v(&v))) (.snd hl(v(&v'))) Ψ) ⊢
      refines (.snd e) (.snd e') Ψ := refines_bind e e' [.snd] [.snd] Ψ

theorem refines_bind_injL :
    refines e e' (fun v v' => refines (.injL hl(v(&v))) (.injL hl(v(&v'))) Ψ) ⊢
      refines (.injL e) (.injL e') Ψ := refines_bind e e' [.injL] [.injL] Ψ

theorem refines_bind_injR :
    refines e e' (fun v v' => refines (.injR hl(v(&v))) (.injR hl(v(&v'))) Ψ) ⊢
      refines (.injR e) (.injR e') Ψ := refines_bind e e' [.injR] [.injR] Ψ

theorem refines_bind_case (e₁ e₂ e₁' e₂' : Exp) :
    refines e e' (fun v v' => refines (.case hl(v(&v)) e₁ e₂) (.case hl(v(&v')) e₁' e₂') Ψ) ⊢
      refines (.case e e₁ e₂) (.case e' e₁' e₂') Ψ :=
  refines_bind e e' [.case e₁ e₂] [.case e₁' e₂'] Ψ

theorem refines_bind_allocNR (f f' : Exp) :
    refines e e' (fun v v' => refines (.allocN f hl(v(&v))) (.allocN f' hl(v(&v'))) Ψ) ⊢
      refines (.allocN f e) (.allocN f' e') Ψ :=
  refines_bind e e' [.allocNR f] [.allocNR f'] Ψ

theorem refines_bind_load :
    refines e e' (fun v v' => refines (.load hl(v(&v))) (.load hl(v(&v'))) Ψ) ⊢
      refines (.load e) (.load e') Ψ := refines_bind e e' [.load] [.load] Ψ

theorem refines_bind_storeR (f f' : Exp) :
    refines e e' (fun v v' => refines (.store f hl(v(&v))) (.store f' hl(v(&v'))) Ψ) ⊢
      refines (.store f e) (.store f' e') Ψ := refines_bind e e' [.storeR f] [.storeR f'] Ψ

theorem refines_bind_storeL (w w' : Val) :
    refines e e' (fun v v' =>
        refines (.store hl(v(&v)) hl(v(&w))) (.store hl(v(&v')) hl(v(&w'))) Ψ) ⊢
      refines (.store e hl(v(&w))) (.store e' hl(v(&w'))) Ψ :=
  refines_bind e e' [.storeL w] [.storeL w'] Ψ

end Bind

theorem refines_wand {e e' : Exp} {Ψ Φ : Val → Val → IProp GF} :
    refines e e' Ψ ⊢ iprop((∀ v : Val, ∀ w : Val, Ψ v w -∗ Φ v w) -∗ refines e e' Φ) := by
  iintro H HΨ
  unfold refines
  iintro %K Hs
  ispecialize H $$ %K Hs
  iapply swp_wand $$ H
  iintro %v ⟨%v', Hs, HΨv⟩
  iexists v'
  isplitl [Hs]
  · iexact Hs
  · iapply HΨ $$ %v %v' HΨv

theorem refines_mono {e e' : Exp} {Ψ Φ : Val → Val → IProp GF} (h : ∀ v w, Ψ v w ⊢ Φ v w) :
    refines e e' Ψ ⊢ refines e e' Φ := by
  iintro H
  unfold refines
  iintro %K Hs
  ispecialize H $$ %K Hs
  iapply swp_wand $$ H
  iintro %v ⟨%v', Hs, HΨ⟩
  iexists v'
  isplitl [Hs]
  · iexact Hs
  · iapply h v v' $$ HΨ

/-! ### Source steps, bundled with the invariant

`program_logics/reloc/proofmode.v`'s four `src_expr_step_*` lemmas. The `tac_src_*` lemmas and
the `src_pure`/`src_load`/`src_store`/`src_alloc` tactics they support are Rocq proof automation
(`CORRESPONDENCE.md` §4.2); these are the statements underneath. -/

section SrcExprSteps

variable {E : CoPset} {K : List ECtxItem} {e₁ e₂ : Exp} {l : Loc} {v w : Val}

theorem srcExpr_step_pure {φ : Prop} {n : Nat} (hφ : φ)
    [hpe : Language.PureExec φ n e₁ e₂] (hE : ↑srcN ⊆ E) :
    srcExpr (hlc := hlc) (GF := GF) (fill K e₁) ⊢ iprop(|={E}=> srcExpr (fill K e₂)) := by
  unfold srcExpr
  iintro ⟨#Hctx, Hs⟩
  imod src_step_pures hφ hE $$ Hctx Hs with Hs
  imodintro
  iframe Hctx Hs

theorem srcExpr_step_load (hE : ↑srcN ⊆ E) :
    iprop(srcExpr (hlc := hlc) (GF := GF) (fill K hl(!#l)) ∗ (l ↦ₛ v)) ⊢
      iprop(|={E}=> srcExpr (fill K hl(v(&v))) ∗ (l ↦ₛ v)) := by
  unfold srcExpr
  iintro ⟨⟨#Hctx, Hs⟩, Hl⟩
  imod src_step_load hE $$ Hctx Hs Hl with ⟨Hs, Hl⟩
  imodintro
  iframe Hctx Hs Hl

theorem srcExpr_step_store (hE : ↑srcN ⊆ E) :
    iprop(srcExpr (hlc := hlc) (GF := GF) (fill K hl(#l ← v(&w))) ∗ (l ↦ₛ v)) ⊢
      iprop(|={E}=> srcExpr (fill K hl(#())) ∗ (l ↦ₛ w)) := by
  unfold srcExpr
  iintro ⟨⟨#Hctx, Hs⟩, Hl⟩
  imod src_step_store hE $$ Hctx Hs Hl with ⟨Hs, Hl⟩
  imodintro
  iframe Hctx Hs Hl

theorem srcExpr_step_alloc (hE : ↑srcN ⊆ E) :
    srcExpr (hlc := hlc) (GF := GF) (fill K hl(ref(v(&v)))) ⊢
      iprop(|={E}=> ∃ l : Loc, srcExpr (fill K hl(#l)) ∗ (l ↦ₛ v)) := by
  unfold srcExpr
  iintro ⟨#Hctx, Hs⟩
  imod src_step_alloc hE $$ Hctx Hs with ⟨%l, Hs, Hl⟩
  imodintro
  iexists l
  iframe Hctx Hs Hl

/-- Pure steps in the source. -/
theorem refines_src_pure {φ : Prop} {n : Nat} {e₁ e₂ e₂' : Exp} {Ψ : Val → Val → IProp GF}
    (hφ : φ) [Language.PureExec φ n e₂ e₂'] :
    refines (hlc := hlc) e₁ e₂' Ψ ⊢ refines e₁ e₂ Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  iapply fupd_swp (E₂ := ⊤)
  imod srcExpr_step_pure hφ srcN_subseteq_top $$ Hs with Hs
  imodintro
  iapply H $$ %K Hs

/-- Pure steps in the target. -/
theorem refines_target_pure {φ : Prop} {n : Nat} {e₁ e₁' e₂ : Exp} {Ψ : Val → Val → IProp GF}
    (hφ : φ) [h : Language.PureExec φ n e₁ e₁'] :
    refines (hlc := hlc) e₁' e₂ Ψ ⊢ refines e₁ e₂ Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  ispecialize H $$ %K Hs
  iapply swp_pure_steps (Language.PureExec.mk (φ := True) fun _ => h.pureExec hφ)
  iexact H

/-- A given pure step in the target. -/
theorem refines_target_step {n : Nat} {e₁ e₁' e₂ : Exp} {Ψ : Val → Val → IProp GF}
    (h : Language.PureExec True n e₁ e₁') :
    refines (hlc := hlc) e₁' e₂ Ψ ⊢ refines e₁ e₂ Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  ispecialize H $$ %K Hs
  iapply swp_pure_steps h
  iexact H

/-- A given pure step in the source. -/
theorem refines_src_step {n : Nat} {e₁ e₂ e₂' : Exp} {Ψ : Val → Val → IProp GF}
    (h : Language.PureExec True n e₂ e₂') :
    refines (hlc := hlc) e₁ e₂' Ψ ⊢ refines e₁ e₂ Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  iapply fupd_swp (E₂ := ⊤)
  imod srcExpr_step_pure (hpe := h) trivial srcN_subseteq_top $$ Hs with Hs
  imodintro
  iapply H $$ %K Hs

/-- A pure step in the target that strips a `▷`: this is what lets `unroll` unfold a recursive
type. -/
theorem refines_target_step_later {e₁ e₁' e₂ : Exp} {Ψ : Val → Val → IProp GF}
    (h : Language.PureExec True 1 e₁ e₁') :
    iprop(▷ refines (hlc := hlc) e₁' e₂ Ψ) ⊢ refines e₁ e₂ Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  iapply swp_pure_step_later h
  inext
  iapply H $$ %K Hs

/-- A load in the source. -/
theorem refines_src_load {e₁ : Exp} {Ψ : Val → Val → IProp GF} (l : Loc) (v : Val) :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v) -∗ refines (hlc := hlc) e₁ hl(v(&v)) Ψ)) ⊢
      refines e₁ hl(!#l) Ψ := by
  iintro ⟨Hl, H⟩
  unfold refines
  iintro %K Hs
  iapply fupd_swp (E₂ := ⊤)
  imod srcExpr_step_load srcN_subseteq_top $$ [Hs Hl] with ⟨Hs, Hl⟩
  · iframe Hs Hl
  imodintro
  iapply H $$ Hl %K Hs

/-- A store in the source. -/
theorem refines_src_store {e₁ : Exp} {Ψ : Val → Val → IProp GF} (l : Loc) (v w : Val) :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ w) -∗ refines (hlc := hlc) e₁ hl(#()) Ψ)) ⊢
      refines e₁ hl(#l ← v(&w)) Ψ := by
  iintro ⟨Hl, H⟩
  unfold refines
  iintro %K Hs
  iapply fupd_swp (E₂ := ⊤)
  imod srcExpr_step_store srcN_subseteq_top $$ [Hs Hl] with ⟨Hs, Hl⟩
  · iframe Hs Hl
  imodintro
  iapply H $$ Hl %K Hs

/-- An allocation in the source. -/
theorem refines_src_alloc {e₁ : Exp} {Ψ : Val → Val → IProp GF} (v : Val) :
    iprop(∀ l : Loc, (l ↦ₛ v) -∗ refines (hlc := hlc) e₁ hl(#l) Ψ) ⊢
      refines e₁ hl(ref(v(&v))) Ψ := by
  iintro H
  unfold refines
  iintro %K Hs
  iapply fupd_swp (E₂ := ⊤)
  imod srcExpr_step_alloc srcN_subseteq_top $$ Hs with ⟨%l, Hs, Hl⟩
  imodintro
  iapply H $$ %l Hl %K Hs

end SrcExprSteps

/-! ## The interpretations -/

def intInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v v' => iprop(∃ n : Int, ⌜v = hl_val(#n)⌝ ∗ ⌜v' = hl_val(#n)⌝))
    (fun _ _ => inferInstance)

def boolInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v v' => iprop(∃ b : Bool, ⌜v = hl_val(#b)⌝ ∗ ⌜v' = hl_val(#b)⌝))
    (fun _ _ => inferInstance)

def unitInterp : Env GF → SemType GF := fun _ =>
  mkSemType (fun v v' => iprop(⌜v = hl_val(#())⌝ ∗ ⌜v' = hl_val(#())⌝))
    (fun _ _ => inferInstance)

def funInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(∀ w : Val, ∀ w' : Val,
      □ (σ₁ δ w w' -∗ refines hl(v(&v) v(&w)) hl(v(&v') v(&w')) (σ₂ δ))))
    (fun _ _ => inferInstance)

def varInterp (x : Nat) : Env GF → SemType GF := fun δ => δ x

def allInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(□ ∀ τ : SemType GF,
      refines (tApp hl(v(&v))) (tApp hl(v(&v'))) (σ (τ .:: δ))))
    (fun _ _ => inferInstance)

def existInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(∃ w : Val, ∃ w' : Val, ⌜v = packV w⌝ ∗ ⌜v' = packV w'⌝ ∗
      ∃ τ : SemType GF, (σ (τ .:: δ)) w w'))
    (fun _ _ => inferInstance)

/-- One unrolling of a recursive type. -/
def muRec (σ : Env GF → SemType GF) (δ : Env GF) (ρ : SemType GF) : SemType GF :=
  mkSemType (fun v v' => iprop(∃ w : Val, ∃ w' : Val, ⌜v = rollV w⌝ ∗ ⌜v' = rollV w'⌝ ∗
      ▷ (σ (ρ .:: δ)) w w'))
    (fun _ _ => inferInstance)

/-- The invariant tying a target location to a source location. -/
def refInv (l l' : Loc) (τ : SemType GF) : IProp GF :=
  iprop(∃ w : Val, ∃ w' : Val, (l ↦ some w) ∗ (l' ↦ₛ w') ∗ τ w w')

def refInterp (σ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(∃ l : Loc, ∃ l' : Loc, ⌜v = hl_val(#l)⌝ ∗ ⌜v' = hl_val(#l')⌝ ∗
      inv logN (refInv l l' (σ δ))))
    (fun _ _ => inferInstance)

def prodInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(∃ w₁ : Val, ∃ w₁' : Val, ∃ w₂ : Val, ∃ w₂' : Val,
      ⌜v = hl_val((&w₁, &w₂))⌝ ∗ ⌜v' = hl_val((&w₁', &w₂'))⌝ ∗
      σ₁ δ w₁ w₁' ∗ σ₂ δ w₂ w₂'))
    (fun _ _ => inferInstance)

def sumInterp (σ₁ σ₂ : Env GF → SemType GF) : Env GF → SemType GF := fun δ =>
  mkSemType (fun v v' => iprop(
      (∃ w : Val, ∃ w' : Val, ⌜v = hl_val(injl(&w))⌝ ∗ ⌜v' = hl_val(injl(&w'))⌝ ∗ σ₁ δ w w') ∨
      (∃ w : Val, ∃ w' : Val, ⌜v = hl_val(injr(&w))⌝ ∗ ⌜v' = hl_val(injr(&w'))⌝ ∗ σ₂ δ w w')))
    (fun _ _ => inferInstance)

/-! ### Applying an interpretation to a pair of values -/

@[simp] theorem intInterp_car (δ : Env GF) (v v' : Val) :
    (intInterp δ).car v v' = iprop(∃ n : Int, ⌜v = hl_val(#n)⌝ ∗ ⌜v' = hl_val(#n)⌝) := rfl
@[simp] theorem boolInterp_car (δ : Env GF) (v v' : Val) :
    (boolInterp δ).car v v' = iprop(∃ b : Bool, ⌜v = hl_val(#b)⌝ ∗ ⌜v' = hl_val(#b)⌝) := rfl
@[simp] theorem unitInterp_car (δ : Env GF) (v v' : Val) :
    (unitInterp δ).car v v' = iprop(⌜v = hl_val(#())⌝ ∗ ⌜v' = hl_val(#())⌝) := rfl
@[simp] theorem funInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (funInterp σ₁ σ₂ δ).car v v' = iprop(∀ w : Val, ∀ w' : Val,
      □ ((σ₁ δ).car w w' -∗ refines hl(v(&v) v(&w)) hl(v(&v') v(&w')) (σ₂ δ))) := rfl
@[simp] theorem allInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (allInterp σ δ).car v v' = iprop(□ ∀ τ : SemType GF,
      refines (tApp hl(v(&v))) (tApp hl(v(&v'))) (σ (τ .:: δ))) := rfl
@[simp] theorem existInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (existInterp σ δ).car v v' = iprop(∃ w : Val, ∃ w' : Val, ⌜v = packV w⌝ ∗ ⌜v' = packV w'⌝ ∗
      ∃ τ : SemType GF, (σ (τ .:: δ)).car w w') := rfl
@[simp] theorem refInterp_car (σ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (refInterp σ δ).car v v' = iprop(∃ l : Loc, ∃ l' : Loc, ⌜v = hl_val(#l)⌝ ∗ ⌜v' = hl_val(#l')⌝ ∗
      inv logN (refInv l l' (σ δ))) := rfl
@[simp] theorem prodInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (prodInterp σ₁ σ₂ δ).car v v' = iprop(∃ w₁ : Val, ∃ w₁' : Val, ∃ w₂ : Val, ∃ w₂' : Val,
      ⌜v = hl_val((&w₁, &w₂))⌝ ∗ ⌜v' = hl_val((&w₁', &w₂'))⌝ ∗
      (σ₁ δ).car w₁ w₁' ∗ (σ₂ δ).car w₂ w₂') := rfl
@[simp] theorem sumInterp_car (σ₁ σ₂ : Env GF → SemType GF) (δ : Env GF) (v v' : Val) :
    (sumInterp σ₁ σ₂ δ).car v v' = iprop(
      (∃ w : Val, ∃ w' : Val, ⌜v = hl_val(injl(&w))⌝ ∗ ⌜v' = hl_val(injl(&w'))⌝ ∗ (σ₁ δ).car w w') ∨
      (∃ w : Val, ∃ w' : Val, ⌜v = hl_val(injr(&w))⌝ ∗ ⌜v' = hl_val(injr(&w'))⌝ ∗
        (σ₂ δ).car w w')) := rfl
@[simp] theorem muRec_car (σ : Env GF → SemType GF) (δ : Env GF) (ρ : SemType GF) (v v' : Val) :
    (muRec σ δ ρ).car v v' = iprop(∃ w : Val, ∃ w' : Val, ⌜v = rollV w⌝ ∗ ⌜v' = rollV w'⌝ ∗
      ▷ (σ (ρ .:: δ)).car w w') := rfl

/-- `muRec` is contractive in its recursive argument. -/
theorem muRec_contractive (σ : Env GF → SemType GF) (hσ : NonExpansive σ) (δ : Env GF) :
    Contractive (muRec σ δ) where
  distLater_dist {n ρ ρ'} h v v' := by
    refine BI.exists_ne fun w => BI.exists_ne fun w' => BI.sep_ne.ne .rfl ?_
    refine BI.sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist (f := (BIBase.later : IProp GF → IProp GF)) ?_
    intro m hm
    exact hσ.ne (consEnv_ne (h m hm) .rfl) w w'

end ProgramLogics.Reloc
