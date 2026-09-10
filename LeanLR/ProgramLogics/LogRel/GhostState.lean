import LeanLR.ProgramLogics.LogRel.GhostStateLib

/-!
# Ghost state, in use

`program_logics/logrel/ghost_state_sol.v`. Rules derived from the three primitive update rules of
`GhostStateLib.lean`, and their specialisations to the monotone counter.

The file's `ipm` section is a tour of `iMod` and `iFrame` in which every lemma is `Abort`ed; the
same tactics (`imod`, `iframe`) are used throughout the proofs below. Its four `logrel_*` sections
are examples over the logical relation and belong with `logrel_sol.v`.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProofMode

namespace ProgramLogics.LogRel

/-! ## Derived update rules -/

section Derived

variable {GF : BundledGFunctors} {P Q : IProp GF}

theorem upd_wand : ⊢@{IProp GF} iprop(|==> P) -∗ (P -∗ Q) -∗ |==> Q := by
  iintro Hp Hpq
  imod Hp
  imodintro
  iapply Hpq $$ Hp

theorem upd_mono (h : P ⊢ Q) : iprop(|==> P) ⊢ iprop(|==> Q) := by
  iintro Hp
  imod Hp
  imodintro
  iapply h $$ Hp

theorem upd_trans : iprop(|==> |==> P) ⊢ iprop(|==> P) := by
  iintro Hp
  imod Hp
  iexact Hp

theorem upd_frame : ⊢@{IProp GF} P -∗ iprop(|==> Q) -∗ |==> (P ∗ Q) := by
  iintro Hp Hq
  imod Hq
  imodintro
  iframe Hp Hq

end Derived

/-! ## Derived rules for the monotone counter -/

section MonoDerived

variable {GF : BundledGFunctors} {hlc : HasLC} [MonoNatG GF] {γ : GName} {n m : Nat}

private theorem mono_nat_increase_add (k : Nat) :
    ⊢@{IProp GF} mono γ n -∗ |==> mono γ (n + k) := by
  induction k with
  | zero =>
    iintro H
    imodintro
    iexact H
  | succ k ih =>
    iintro H
    imod ih $$ H with H
    iapply mono_nat_increase_val $$ H

theorem mono_nat_increase (h : n ≤ m) : ⊢@{IProp GF} mono γ n -∗ |==> mono γ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact mono_nat_increase_add k

variable [HeapLangGS hlc GF] {e : Exp} {Φ : Val → IProp GF}

/-- A bound may be raised at any point before the expression runs. -/
theorem mono_nat_increase_wp (h : n ≤ m) :
    ⊢@{IProp GF} (mono γ m -∗ WP e {{ Φ }}) -∗ (mono γ n -∗ WP e {{ Φ }}) := by
  iintro He Hauth
  iapply upd_wp
  imod mono_nat_increase h $$ Hauth with Hauth
  imodintro
  iapply He $$ Hauth

/-- A fresh counter may be allocated at any point before the expression runs. -/
theorem mono_nat_new_wp (n : Nat) :
    ⊢@{IProp GF} (∀ γ, mono γ n -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }} := by
  iintro Hwand
  iapply upd_wp
  imod mono_nat_new (GF := GF) n with ⟨%γ, Hauth⟩
  imodintro
  iapply Hwand $$ Hauth

end MonoDerived

end ProgramLogics.LogRel
