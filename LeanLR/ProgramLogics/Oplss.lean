import LeanLR.ProgramLogics.Hoare

/-!
# Lecture demonstrations

`program_logics/oplss1.v`. The file exists to contrast a proof carried out by the entailment rules
with the same proof carried out in the IPM, and to run one small heap program end to end.

`oplss2.v` is the `MutBit` module of `ipm_persistency.v`; it is ported there.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics.Oplss

variable {GF : BundledGFunctors}

/-- `HoareLib.ent_exists_sep` again, proved in the IPM rather than from the rules. -/
theorem exists_sep_ipm {X : Type} (Φ : X → IProp GF) (Q : IProp GF) :
    iprop((∃ x, Φ x) ∗ Q) ⊢ iprop(∃ x, Φ x ∗ Q) := by
  iintro ⟨⟨%x, HΦ⟩, HQ⟩
  iexists x
  isplitl [HΦ]
  · iexact HΦ
  iexact HQ

section Heap

variable {hlc : HasLC} [HeapLangGS hlc GF]

def foo : Val := hl_val(λ r1 r2, r1 ← #(23 : Int))

def bar : Exp :=
  hl(let x := ref(#(0 : Int)); let y := ref(#(42 : Int)); &foo x y; !x + !y)

theorem foo_correct (l : Loc) (v w : Val) :
    hoare iprop(l ↦ some w) hl(&foo #l v(&v))
      (fun _ => iprop(l ↦ some hl_val(#(23 : Int)))) := by
  unfold hoare foo
  iintro Hl
  wp_pures
  wp_store
  iexact Hl

theorem bar_correct :
    hoare (GF := GF) iprop(True) bar (fun v => iprop(⌜v = hl_val(#(65 : Int))⌝)) := by
  unfold hoare bar
  iintro _
  wp_alloc l1 with Hl1
  wp_alloc l2 with Hl2
  wp_pures
  have hfoo : iprop(l1 ↦ some hl_val(#(0 : Int))) ⊢
      WP hl(&foo #l1 #l2) {{ fun _ => iprop(l1 ↦ some hl_val(#(23 : Int))) }} :=
    foo_correct l1 hl_val(#l2) hl_val(#(0 : Int))
  wp_bind (&foo #l1 #l2)
  icases hfoo $$ Hl1 with HW
  iapply ent_wp_wand $$ HW
  iintro %v Hl1
  wp_pures
  wp_load
  wp_load
  wp_pures
  ipureintro; rfl

end Heap

end ProgramLogics.Oplss
