import LeanLR.ProgramLogics.IpmPersistency

/-!
# OPLSS, second lecture: a mutable bit behind an invariant

`program_logics/oplss2.v`. The same `MutBit` module as `ipm_persistency.v`, but with a getter
that inspects the cell and asserts it holds `0` or `1` — the assertion is unreachable, and the
invariant is what says so.

The file's own `hoare` and `{{ P }} e {{ Φ }}` notation are `IpmPersistency.hoare`, so they are
not repeated.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode
open ProgramLogics.IpmPersistency (swp_fst_app swp_snd_app)

namespace ProgramLogics.Oplss2

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

/-- The file's `assert`, a value rather than an expression former. -/
def assertV : Val := hl_val(λ x, if x then #() else #(42 : Int) #(42 : Int))

def MutBitImpl : Exp := hl(
  let x := ref(#(0 : Int));
  ((λ _, x ← (#(1 : Int) - !x)),
   (λ _, let y := !x;
         (if (y = #(0 : Int)) then #false
          else if (y = #(1 : Int)) then #true
          else v(&assertV) #false))))

def MutBitSpec (v : Val) : IProp GF :=
  iprop(IpmPersistency.hoare (iprop(True)) hl(fst(v(&v)) #())
      (fun w => iprop(⌜w = hl_val(#())⌝)) ∗
    IpmPersistency.hoare (iprop(True)) hl(snd(v(&v)) #())
      (fun w => iprop(⌜w = hl_val(#true)⌝ ∨ ⌜w = hl_val(#false)⌝)))

def mutbitN : Namespace := nroot .@ "mutbit"

theorem MutBitImpl_proof :
    ⊢ IpmPersistency.hoare (GF := GF) iprop(True) MutBitImpl (fun v => MutBitSpec v) := by
  unfold IpmPersistency.hoare MutBitImpl
  imodintro
  iintro _
  iapply wp_empty_swp
  wp_alloc l with Hl
  wp_pures
  imod (Iris.inv_alloc mutbitN ∅
    iprop((l ↦ some hl_val(#(0 : Int))) ∨ (l ↦ some hl_val(#(1 : Int))))) $$ [Hl] with #Hinv
  · ileft
    iexact Hl
  imodintro
  unfold MutBitSpec
  isplitl []
  · unfold IpmPersistency.hoare
    imodintro
    iintro _
    iapply swp_fst_app
    iapply inv_open_swp (N := mutbitN) (by simp) $$ Hinv
    iintro Hl
    iapply wp_empty_swp
    icases Hl with (Hl | Hl)
    · wp_pures
      wp_load
      wp_store
      simp only [show (1 : Int) - 0 = 1 from by decide]
      isplitl [Hl]
      · iright; iexact Hl
      · itrivial
    · wp_pures
      wp_load
      wp_store
      simp only [show (1 : Int) - 1 = 0 from by decide]
      isplitl [Hl]
      · ileft; iexact Hl
      · itrivial
  · unfold IpmPersistency.hoare
    imodintro
    iintro _
    iapply swp_snd_app
    iapply inv_open_swp (N := mutbitN) (by simp) $$ Hinv
    iintro Hl
    iapply wp_empty_swp
    icases Hl with (Hl | Hl)
    · wp_pures
      wp_load
      wp_pures
      simp only [show ((hl_val(#(0 : Int)) : Val) == hl_val(#(0 : Int))) = true from rfl]
      wp_pures
      isplitl [Hl]
      · ileft; iexact Hl
      · iright; ipureintro; rfl
    · wp_pures
      wp_load
      wp_pures
      simp only [show ((hl_val(#(1 : Int)) : Val) == hl_val(#(0 : Int))) = false from rfl]
      wp_pures
      simp only [show ((hl_val(#(1 : Int)) : Val) == hl_val(#(1 : Int))) = true from rfl]
      wp_pures
      isplitl [Hl]
      · iright; iexact Hl
      · ileft; ipureintro; rfl

end ProgramLogics.Oplss2
