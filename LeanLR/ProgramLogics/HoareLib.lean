import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
import Iris.Instances.Lib.Invariants

/-!
# Program logics: the course's separation-logic interface

This is the Lean counterpart of `program_logics/hoare_lib.v`. Its purpose in the course is to hide
Iris behind a small, named set of rules, so that `hoare.v` and `ipm.v` can be worked through
*from the rules* rather than from the model.

Two things differ from Rocq, both recorded in `CORRESPONDENCE.md` §5.4:

* The course forks Iris to get a sequential two-mask `WP e @ s; E₁, E₂ {{Φ}}` and later-free heap
  laws. `iris-lean` ships the upstream concurrent, single-mask `WP e @ s; E {{Φ}}`; since nothing
  outside `sequential_wp.v` uses `E₁ ≠ E₂`, the rules below are unchanged in shape.
* `iris-lean`'s heap maps `Loc` to `Option Val`, so the points-to assertion reads `l ↦ some v`
  where Rocq writes `l ↦ v`.

Rocq's `Axiom ghost_state : heapGS heapΣ` becomes the `[HeapLangGS hlc GF]` instance binder — no
axiom is introduced.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic

namespace ProgramLogics

section Entailment

variable {GF : BundledGFunctors}
variable {P Q R : IProp GF} {φ : Prop}

/-- Equivalence is entailment in both directions. -/
theorem ent_equiv (P Q : IProp GF) : (P ⊣⊢ Q) ↔ ((P ⊢ Q) ∧ (Q ⊢ P)) :=
  ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

theorem ent_refl (P : IProp GF) : P ⊢ P := by iintro H; iexact H

theorem ent_trans (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R := h₁.trans h₂

/-- `True` and `False` are the pure propositions `⌜True⌝` and `⌜False⌝`. -/
theorem ent_prove_pure (P : IProp GF) (h : φ) : P ⊢ iprop(⌜φ⌝) := by
  iintro H; ipureintro; exact h

theorem ent_assume_pure (hent : P ⊢ iprop(⌜φ⌝)) (h : φ → (P ⊢ Q)) : P ⊢ Q := by
  iintro HP
  ihave %Hφ : ⌜φ⌝ $$ [HP]
  · iapply hent $$ [$]
  iapply h Hφ $$ [$]

theorem ent_and_elim_l (P Q : IProp GF) : iprop(P ∧ Q) ⊢ P := and_elim_l

theorem ent_and_elim_r (P Q : IProp GF) : iprop(P ∧ Q) ⊢ Q := and_elim_r

theorem ent_and_intro (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ iprop(Q ∧ R) := and_intro h₁ h₂

theorem ent_or_introl (P Q : IProp GF) : P ⊢ iprop(P ∨ Q) := or_intro_l

theorem ent_or_intror (P Q : IProp GF) : Q ⊢ iprop(P ∨ Q) := or_intro_r

theorem ent_or_elim (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : iprop(P ∨ Q) ⊢ R := or_elim h₁ h₂

theorem ent_all_intro {X : Type} {Φ : X → IProp GF} (h : ∀ x, P ⊢ Φ x) :
    P ⊢ iprop(∀ x, Φ x) := forall_intro h

theorem ent_all_elim {X : Type} (x : X) (Φ : X → IProp GF) : iprop(∀ y, Φ y) ⊢ Φ x :=
  forall_elim x

theorem ent_exist_intro {X : Type} (x : X) {Φ : X → IProp GF} (h : P ⊢ Φ x) :
    P ⊢ iprop(∃ y, Φ y) := h.trans (exists_intro x)

theorem ent_exist_elim {X : Type} {Φ : X → IProp GF} (h : ∀ x, Φ x ⊢ Q) :
    iprop(∃ x, Φ x) ⊢ Q := exists_elim h

/-! ### Separating conjunction -/

theorem ent_sep_comm (P Q : IProp GF) : iprop(P ∗ Q) ⊣⊢ iprop(Q ∗ P) := sep_comm

theorem ent_sep_assoc (P₁ P₂ P₃ : IProp GF) :
    iprop(P₁ ∗ (P₂ ∗ P₃)) ⊣⊢ iprop((P₁ ∗ P₂) ∗ P₃) := ⟨sep_assoc.mpr, sep_assoc.mp⟩

theorem ent_sep_split {P P' Q Q' : IProp GF} (h : P ⊢ Q) (h' : P' ⊢ Q') :
    iprop(P ∗ P') ⊢ iprop(Q ∗ Q') := sep_mono h h'

theorem ent_sep_true (P : IProp GF) : P ⊢ iprop(True ∗ P) := by
  iintro H; isplitr [H]; itrivial; iexact H

theorem ent_sep_weaken (P Q : IProp GF) : iprop(P ∗ Q) ⊢ P := sep_elim_left

theorem ent_exists_sep {X : Type} (Φ : X → IProp GF) (P : IProp GF) :
    iprop((∃ x, Φ x) ∗ P) ⊢ iprop(∃ x, Φ x ∗ P) := by
  iintro ⟨⟨%x, HΦ⟩, HP⟩
  iexists x
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

/-! ### Magic wand -/

theorem ent_wand_intro (h : iprop(P ∗ Q) ⊢ R) : P ⊢ iprop(Q -∗ R) := wand_intro h

theorem ent_wand_elim (h : P ⊢ iprop(Q -∗ R)) : iprop(P ∗ Q) ⊢ R := wand_elim h

end Entailment

/-! ## Persistency -/

section Persistency

variable {GF : BundledGFunctors} {P Q : IProp GF} {φ : Prop}

theorem ent_pers_dup (P : IProp GF) : iprop(□ P) ⊢ iprop(□ P ∗ □ P) := by
  iintro #H; isplit <;> iexact H

theorem ent_pers_elim (P : IProp GF) : iprop(□ P) ⊢ P := intuitionistically_elim

/-- Pure facts are persistent. -/
theorem ent_pers_pure (φ : Prop) : (iprop(⌜φ⌝) : IProp GF) ⊢ iprop(□ ⌜φ⌝) := by
  iintro %h
  iintro
  ipureintro
  exact h

theorem ent_pers_mono (h : P ⊢ Q) : iprop(□ P) ⊢ iprop(□ Q) := intuitionistically_mono h

theorem ent_pers_and_sep (P Q : IProp GF) : iprop(□ P ∧ Q) ⊢ iprop(□ P ∗ Q) := by
  iintro ⟨#H, HQ⟩
  isplitr [HQ]
  · iexact H
  · iexact HQ

theorem ent_pers_idemp (P : IProp GF) : iprop(□ P) ⊢ iprop(□ □ P) :=
  intuitionistically_idem.mpr

theorem ent_pers_all {X : Type} (Φ : X → IProp GF) :
    iprop(∀ x, □ Φ x) ⊢ iprop(□ ∀ x, Φ x) := by
  iintro #H
  imodintro
  iintro %x
  iapply H

theorem ent_pers_exists {X : Type} (Φ : X → IProp GF) :
    iprop(□ ∃ x, Φ x) ⊢ iprop(∃ x, □ Φ x) := intuitionistically_exists.mp

end Persistency

/-! ## Later and Löb -/

section Later

variable {GF : BundledGFunctors} {P Q : IProp GF}

theorem ent_later_intro (P : IProp GF) : P ⊢ iprop(▷ P) := later_intro

theorem ent_later_mono (h : P ⊢ Q) : iprop(▷ P) ⊢ iprop(▷ Q) := later_mono h

theorem ent_later_sep (P Q : IProp GF) : iprop(▷ (P ∗ Q)) ⊣⊢ iprop(▷ P ∗ ▷ Q) := later_sep

theorem ent_later_all {X : Type} (Φ : X → IProp GF) :
    iprop(▷ ∀ x, Φ x) ⊣⊢ iprop(∀ x, ▷ Φ x) := later_forall

theorem ent_later_exists {X : Type} [Inhabited X] (Φ : X → IProp GF) :
    iprop(▷ ∃ x, Φ x) ⊣⊢ iprop(∃ x, ▷ Φ x) := later_exists.symm

theorem ent_later_pers (P : IProp GF) : iprop(▷ □ P) ⊣⊢ iprop(□ ▷ P) :=
  ⟨later_intuitionistically.mpr, later_intuitionistically.mp⟩

/-- Löb induction. -/
theorem ent_loeb (h : iprop(▷ P) ⊢ P) : (iprop(True) : IProp GF) ⊢ P :=
  (BI.imp_intro (and_elim_r.trans h)).trans loeb

end Later

/-! ## Hoare triples -/

section Hoare

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {P Q F : IProp GF} {Φ Ψ : Val → IProp GF} {φ : Prop}

/-- The course's Hoare triple: a weakest precondition read as a specification. -/
def hoare (P : IProp GF) (e : Exp) (Φ : Val → IProp GF) : Prop := P ⊢ WP e {{ Φ }}

theorem hoare_value (v : Val) (Φ : Val → IProp GF) : hoare (Φ v) (Exp.val v) Φ :=
  wp_value (by exact ⟨rfl⟩)

theorem hoare_con {e : Exp} (hpre : P ⊢ Q) (hpost : ∀ v, Ψ v ⊢ Φ v) (h : hoare Q e Ψ) :
    hoare P e Φ := hpre.trans (h.trans (wp_mono hpost))

theorem hoare_pure {e : Exp} (hent : P ⊢ iprop(⌜φ⌝)) (h : φ → hoare P e Φ) : hoare P e Φ :=
  ent_assume_pure hent h

theorem hoare_exist_pre {X : Type} {e : Exp} {Φ : X → IProp GF} {Ψ : Val → IProp GF}
    (h : ∀ x, hoare (Φ x) e Ψ) : hoare iprop(∃ x, Φ x) e Ψ := exists_elim h

theorem hoare_bind (K : Exp → Exp) [Language.Context K] {e : Exp}
    (h : hoare P e Ψ) (hk : ∀ v, hoare (Ψ v) (K (Exp.val v)) Φ) : hoare P (K e) Φ :=
  (h.trans (wp_mono hk)).trans (wp_bind K)

theorem hoare_frame {e : Exp} (h : hoare P e Φ) :
    hoare iprop(P ∗ F) e (fun v => iprop(Φ v ∗ F)) :=
  (sep_comm.mp.trans ((sep_mono (ent_refl F) h).trans wp_frame_l)).trans
    (wp_mono fun _ => sep_comm.mp)

/-! ### Pure steps

Rocq's `pure_step` is `iris-lean`'s `Language.PureExec True 1`; `PureStep` names that so the rules
below read like the course's. The `£ n` later credit in `wp_pure_step_later` is simply discarded —
the course's WP has no credits. -/

/-- A single pure reduction step, in the course's sense. -/
abbrev PureStep (e₁ e₂ : Exp) : Prop := Language.PureExec True 1 e₁ e₂

/-- A `PureExec` at index 1 whose side condition holds is a pure step. -/
theorem PureStep.of_pureExec {φ : Prop} {e₁ e₂ : Exp}
    (h : Language.PureExec φ 1 e₁ e₂) (hφ : φ) : PureStep e₁ e₂ := ⟨fun _ => h.pureExec hφ⟩

/-- Pure steps are closed under evaluation contexts. -/
theorem pure_step_fill (K : Exp → Exp) [Language.Context K] {e₁ e₂ : Exp}
    (h : PureStep e₁ e₂) : PureStep (K e₁) (K e₂) := Language.pureExec_fill K h

theorem ent_later_wp_pure_step' {e e' : Exp} (hp : PureStep e e') (Φ : Val → IProp GF) :
    iprop(▷ WP e' {{ Φ }}) ⊢ WP e {{ Φ }} :=
  (later_mono (wand_intro sep_elim_left)).trans
    (wp_pure_step_later (n := 1) (Hexec := hp) trivial)

theorem ent_later_wp_pure_step {e e' : Exp} [hp : PureStep e e'] (Φ : Val → IProp GF) :
    iprop(▷ WP e' {{ Φ }}) ⊢ WP e {{ Φ }} := ent_later_wp_pure_step' hp Φ

/-- A pure step may be taken under a weakest precondition without
paying a later. -/
theorem ent_wp_pure_step {e e' : Exp} (hp : PureStep e e') (Φ : Val → IProp GF) :
    WP e' {{ Φ }} ⊢ WP e {{ Φ }} :=
  later_intro.trans (ent_later_wp_pure_step' hp Φ)

theorem hoare_pure_step' {e₁ e₂ : Exp} (hp : PureStep e₁ e₂) (h : hoare P e₂ Φ) : hoare P e₁ Φ :=
  (h.trans later_intro).trans (ent_later_wp_pure_step' hp Φ)

theorem hoare_pure_step {e₁ e₂ : Exp} [hp : PureStep e₁ e₂] (h : hoare P e₂ Φ) : hoare P e₁ Φ :=
  hoare_pure_step' hp h

/-- The reflexive-transitive closure of `PureStep`, replacing -/
inductive PureSteps : Exp → Exp → Prop where
  | refl {e} : PureSteps e e
  | step {e₁ e₂ e₃} : PureStep e₁ e₂ → PureSteps e₂ e₃ → PureSteps e₁ e₃

theorem PureSteps.single {e₁ e₂ : Exp} (h : PureStep e₁ e₂) : PureSteps e₁ e₂ := .step h .refl

theorem PureSteps.trans {e₁ e₂ e₃ : Exp} (h₁ : PureSteps e₁ e₂) (h₂ : PureSteps e₂ e₃) :
    PureSteps e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem rtc_pure_step_fill (K : Exp → Exp) [Language.Context K] {e₁ e₂ : Exp}
    (h : PureSteps e₁ e₂) : PureSteps (K e₁) (K e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (pure_step_fill K hs) ih

theorem hoare_pure_steps {e₁ e₂ : Exp} (hs : PureSteps e₁ e₂) (h : hoare P e₂ Φ) :
    hoare P e₁ Φ := by
  induction hs with
  | refl => exact h
  | step hp _ ih => exact hoare_pure_step' hp (ih h)

/-! #### The individual pure steps

In Lean these are exactly `iris-lean`'s registered `PureExec` instances, so most are
`inferInstance`; the arithmetic ones go through `PureStep.of_pureExec` because their `PureExec`
instance carries the evaluation of the operator as a side condition. -/

theorem pure_step_beta (f x : Binder) (e : Exp) (v : Val) :
    PureStep hl(v(rec &f &x := &e) &v) ((e.subst f (.rec_ f x e)).subst x v) := inferInstance

theorem pure_step_rec (f x : Binder) (e : Exp) :
    PureStep hl(rec &f &x := &e) hl(v(rec &f &x := &e)) := inferInstance

theorem pure_step_if_true (e₁ e₂ : Exp) : PureStep hl(if #true then &e₁ else &e₂) e₁ :=
  inferInstance

theorem pure_step_if_false (e₁ e₂ : Exp) : PureStep hl(if #false then &e₁ else &e₂) e₂ :=
  inferInstance

theorem pure_step_pair (v₁ v₂ : Val) : PureStep hl((&v₁, &v₂)) hl(v((&v₁, &v₂))) := inferInstance

theorem pure_step_fst (v₁ v₂ : Val) : PureStep hl(fst(v((&v₁, &v₂)))) v₁ := inferInstance

theorem pure_step_snd (v₁ v₂ : Val) : PureStep hl(snd(v((&v₁, &v₂)))) v₂ := inferInstance

theorem pure_step_injl (v : Val) : PureStep hl(injl(&v)) hl(v(injl(&v))) := inferInstance

theorem pure_step_injr (v : Val) : PureStep hl(injr(&v)) hl(v(injr(&v))) := inferInstance

theorem pure_step_match_injl (v : Val) (e₁ e₂ : Exp) :
    PureStep (Exp.case hl(v(injl(&v))) e₁ e₂) (.app e₁ (.ofVal v)) := inferInstance

theorem pure_step_match_injr (v : Val) (e₁ e₂ : Exp) :
    PureStep (Exp.case hl(v(injr(&v))) e₁ e₂) (.app e₂ (.ofVal v)) := inferInstance

/-- Comparison of two equal integer literals. -/
theorem pure_step_eq {n m : Int} (h : n = m) : PureStep hl(#n = #m) hl(#true) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .eq) (v1 := hl_val(#n)) (v2 := hl_val(#m))
    (v' := hl_val(#true)))
    (by subst h; simp [BinOp.eval, Val.compareSafe, BaseLit.isUnboxed, Val.isUnboxed])

/-- Comparison of two distinct integer literals. -/
theorem pure_step_neq {n m : Int} (h : n ≠ m) : PureStep hl(#n = #m) hl(#false) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .eq) (v1 := hl_val(#n)) (v2 := hl_val(#m))
    (v' := hl_val(#false)))
    (by simp [BinOp.eval, Val.compareSafe, BaseLit.isUnboxed, Val.isUnboxed, BEq.beq]; omega)

theorem pure_step_add (n m : Int) : PureStep hl(#n + #m) hl(#(n + m)) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .plus)
    (v1 := hl_val(#n)) (v2 := hl_val(#m)) (v' := hl_val(#(n + m)))) rfl

theorem pure_step_sub (n m : Int) : PureStep hl(#n - #m) hl(#(n - m)) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .minus)
    (v1 := hl_val(#n)) (v2 := hl_val(#m)) (v' := hl_val(#(n - m)))) rfl

theorem pure_step_mul (n m : Int) : PureStep hl(#n * #m) hl(#(n * m)) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .mult)
    (v1 := hl_val(#n)) (v2 := hl_val(#m)) (v' := hl_val(#(n * m)))) rfl

/-! ### Reaching a value by pure steps

Not every value expression is syntactically `Exp.val v`: `rec`, and pairs and injections of
values, are values of the language but distinct expressions, and each takes one pure step to its
`Exp.val` form. `ExprIsVal` records that a given expression reaches a given value that way, and
`pure_step_val` turns it into the pure reduction. -/

/-- A pure step is exactly a `PureExec` at index 1 with a satisfied
side condition. -/
theorem pureExec_1_equiv {e₁ e₂ : Exp} :
    (∃ φ : Prop, φ ∧ Language.PureExec φ 1 e₁ e₂) ↔ PureStep e₁ e₂ :=
  ⟨fun ⟨_, hφ, h⟩ => PureStep.of_pureExec h hφ, fun h => ⟨True, trivial, h⟩⟩

/-- `e` reaches the value `v` by pure reduction of value constructors
only. -/
inductive ExprIsVal : Exp → Val → Prop where
  | base (v : Val) : ExprIsVal (.ofVal v) v
  | rec_ (f x : Binder) (e : Exp) : ExprIsVal (.rec_ f x e) (.rec_ f x e)
  | pair {e₁ e₂ : Exp} {v₁ v₂ : Val} :
      ExprIsVal e₁ v₁ → ExprIsVal e₂ v₂ → ExprIsVal (.pair e₁ e₂) (.pair v₁ v₂)
  | injL {e : Exp} {v : Val} : ExprIsVal e v → ExprIsVal (.injL e) (.injL v)
  | injR {e : Exp} {v : Val} : ExprIsVal e v → ExprIsVal (.injR e) (.injR v)

theorem exprIsVal_ofVal (v : Val) : ExprIsVal (.ofVal v) v := .base v

theorem pure_step_val_fun (f x : Binder) (e : Exp) :
    PureSteps (.rec_ f x e) (.ofVal (.rec_ f x e)) :=
  .single (pure_step_rec f x e)

/-- Pairs evaluate right to left, so the right component is reduced
under `pairR` first and the left one under `pairL` afterwards. -/
theorem pure_step_val_pair {e₁ e₂ : Exp} {v₁ v₂ : Val}
    (h₁ : PureSteps e₁ (.ofVal v₁)) (h₂ : PureSteps e₂ (.ofVal v₂)) :
    PureSteps (.pair e₁ e₂) (.ofVal (.pair v₁ v₂)) := by
  have s₂ : PureSteps (.pair e₁ e₂) (.pair e₁ (.ofVal v₂)) :=
    rtc_pure_step_fill (EvContext.fill (Ectx := List ECtxItem) [.pairR e₁]) h₂
  have s₁ : PureSteps (.pair e₁ (.ofVal v₂)) (.pair (.ofVal v₁) (.ofVal v₂)) :=
    rtc_pure_step_fill (EvContext.fill (Ectx := List ECtxItem) [.pairL v₂]) h₁
  exact (s₂.trans s₁).trans (.single (pure_step_pair v₁ v₂))

theorem pure_step_val_injl {e : Exp} {v : Val} (h : PureSteps e (.ofVal v)) :
    PureSteps (.injL e) (.ofVal (.injL v)) :=
  (rtc_pure_step_fill (EvContext.fill (Ectx := List ECtxItem) [.injL]) h).trans
    (.single (pure_step_injl v))

theorem pure_step_val_injr {e : Exp} {v : Val} (h : PureSteps e (.ofVal v)) :
    PureSteps (.injR e) (.ofVal (.injR v)) :=
  (rtc_pure_step_fill (EvContext.fill (Ectx := List ECtxItem) [.injR]) h).trans
    (.single (pure_step_injr v))

/-- Everything `ExprIsVal` relates is reached by pure steps. -/
theorem pure_step_val {e : Exp} {v : Val} (h : ExprIsVal e v) : PureSteps e (.ofVal v) := by
  induction h with
  | base _ => exact .refl
  | rec_ f x e => exact pure_step_val_fun f x e
  | pair _ _ ih₁ ih₂ => exact pure_step_val_pair ih₁ ih₂
  | injL _ ih => exact pure_step_val_injl ih
  | injR _ ih => exact pure_step_val_injr ih

/-- Truncated division of two integer literals. Rocq's `pure_step_quot` (`heap_lang`'s `quot` is
`Int.tdiv`). -/
theorem pure_step_quot (n m : Int) : PureStep hl(#n / #m) hl(#(n.tdiv m)) :=
  PureStep.of_pureExec (instPureExecBinOp (op := .tdiv) (v1 := hl_val(#n)) (v2 := hl_val(#m))
    (v' := hl_val(#(n.tdiv m)))) (by simp [BinOp.eval, BinOp.evalInt])

/-! ### Points-to is exclusive -/

theorem ent_pointsto_sep (l : Loc) (v w : Val) :
    iprop((l ↦ some v) ∗ (l ↦ some w)) ⊢ (False : IProp GF) := by
  iintro ⟨H1, H2⟩
  icases pointsTo_ne $$ H1 H2 with %hne
  exact (hne rfl).elim

/-! ### Weakest-precondition rules -/

theorem ent_wp_value (Φ : Val → IProp GF) (v : Val) : Φ v ⊢ WP (Exp.val v) {{ w, Φ w }} :=
  wp_value (by exact ⟨rfl⟩)

theorem ent_wp_wand {e : Exp} (Φ Ψ : Val → IProp GF) :
    WP e {{ Φ }} ⊢ iprop((∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}) := wp_wand

/-- The doubly-curried form of `ent_wp_wand`. -/
theorem ent_wp_wand' {e : Exp} (Φ Ψ : Val → IProp GF) :
    ⊢ iprop((∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Φ }} -∗ WP e {{ Ψ }}) := by
  iintro Hp Hwp
  iapply ent_wp_wand $$ Hwp
  iexact Hp

theorem ent_wp_bind (K : Exp → Exp) [Language.Context K] {e : Exp} (Φ : Val → IProp GF) :
    WP e {{ v, WP (K (Exp.val v)) {{ Φ }} }} ⊢ WP (K e) {{ Φ }} := wp_bind K

/-! ### Heap rules

`iris-lean`'s heap laws already carry the `▷`, so these are the course's `ent_later_wp_*` family;
the later-free versions of `hoare_lib.v` correspond to `heap_lang/primitive_laws_nolater.v`, which
this port does not reproduce (`CORRESPONDENCE.md` §5.4). -/

theorem ent_later_wp_new (v : Val) (Φ : Val → IProp GF) :
    iprop(▷ ∀ l : Loc, l ↦ some v -∗ Φ hl_val(#l)) ⊢ WP hl(ref(v(&v))) {{ Φ }} := by
  iintro H
  iapply wp_alloc
  · itrivial
  · iexact H

theorem ent_later_wp_load (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    iprop((l ↦ some v) ∗ ▷ (l ↦ some v -∗ Φ v)) ⊢ WP hl(!#l) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_load $$ Hl
  iexact HΦ

/-- Allocation. -/
theorem hoare_new (v : Val) :
    hoare iprop(True) hl(ref(v(&v)))
      (fun w => iprop(∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v)) := by
  unfold hoare
  iintro _
  iapply wp_alloc
  · itrivial
  · inext
    iintro %l Hl
    iexists l
    isplitr [Hl]
    · ipureintro; rfl
    · iexact Hl

/-- Dereferencing. -/
theorem hoare_load (l : Loc) (v : Val) :
    hoare iprop(l ↦ some v) hl(!#l) (fun w => iprop(⌜w = v⌝ ∗ l ↦ some v)) := by
  unfold hoare
  iintro Hl
  iapply wp_load $$ Hl
  inext
  iintro Hl
  isplitr [Hl]
  · ipureintro; rfl
  · iexact Hl

/-- Assignment. -/
theorem hoare_store (l : Loc) (v w : Val) :
    hoare iprop(l ↦ some v) hl(#l ← v(&w)) (fun _ => iprop(l ↦ some w)) := by
  unfold hoare
  iintro Hl
  iapply wp_store $$ Hl
  inext
  iintro Hl
  iexact Hl

theorem ent_later_wp_store (l : Loc) (v w : Val) (Φ : Val → IProp GF) :
    iprop((l ↦ some v) ∗ ▷ (l ↦ some w -∗ Φ hl_val(#()))) ⊢ WP hl(#l ← v(&w)) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_store $$ Hl
  iexact HΦ

end Hoare

/-! ## Invariants

Allocation transfers directly. **Opening** does not: the course's `ent_inv_open` keeps an invariant
open across a whole expression, which is sound only for its *sequential* two-mask WP. `iris-lean`'s
WP is the upstream concurrent one, where an invariant may only be open across a single atomic step
(`wp_atomic` + `inv_acc_timeless`, or the `iinv` tactic). See `CORRESPONDENCE.md` §5.10. -/

section Invariants

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {E : CoPset}

theorem ent_inv_pers (N : Namespace) (F : IProp GF) : inv N F ⊢ iprop(□ inv N F) := by
  iintro #H
  iexact H

/-- Renamed to avoid the clash with `iris-lean`'s own `inv_alloc`. -/
theorem inv_alloc_wp (N : Namespace) (F : IProp GF) {e : Exp} {Φ : Val → IProp GF} :
    F ⊢ iprop((inv N F -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}) := by
  iintro HF Hs
  imod Iris.inv_alloc N E F $$ HF with #Hinv
  iapply Hs $$ Hinv

theorem ent_inv_alloc (N : Namespace) (F P : IProp GF) {e : Exp} {Φ : Val → IProp GF}
    (h : iprop(P ∗ inv N F) ⊢ WP e @ E {{ Φ }}) : iprop(P ∗ F) ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨HP, HF⟩
  imod Iris.inv_alloc N E F $$ HF with #Hinv
  iapply h
  isplitl [HP]
  · iexact HP
  · iexact Hinv

end Invariants

end ProgramLogics
