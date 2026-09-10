import LeanLR.ProgramLogics.SequentialWp
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.DerivedLaws
import Iris.HeapLang.ProofMode

/-!
# heap_lang: the heap laws over the sequential WP, without laters

`program_logics/heap_lang/primitive_laws_nolater.v`. The course restates the heap laws over the
sequential WP of `SequentialWp.lean` and drops the `▷`, so that a proof carried out *from the
rules* never has to reason about laters.

`iris-lean`'s laws hold at every mask, `∅` included, so each one is obtained by giving the mask up
before the expression runs, applying the one-mask law at `∅`, and handing the mask back in the
postcondition (`wp_empty_swp`). The `▷` is weakened away by `inext` — which is exactly what
Rocq's one-line `by iApply wp_alloc` does there.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics

section NoLater

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

/-- A weakest precondition at the empty mask is a sequential one at any mask. -/
theorem wp_empty_swp {e : Exp} : (WP e @ s ; (∅ : CoPset) {{ Φ }}) ⊢ swp s E E e Φ := by
  unfold swp
  iintro H
  imod (fupd_mask_subseteq (E2 := (∅ : CoPset)) (by simp)) with Hclose
  imodintro
  iapply wp_wand $$ H
  iintro %v HΦ
  imod Hclose
  imodintro
  iexact HΦ

theorem swp_alloc (v : Val) :
    iprop(∀ l : Loc, l ↦ some v -∗ Φ hl_val(#l)) ⊢ swp s E E hl(ref(&v)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro H
  iapply wp_alloc
  · itrivial
  · inext
    iintro %l Hl
    iapply H $$ Hl

theorem swp_load (l : Loc) (v : Val) :
    iprop((l ↦ some v) ∗ (l ↦ some v -∗ Φ v)) ⊢ swp s E E hl(!v(#l)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_load $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

theorem swp_store (l : Loc) (v w : Val) :
    iprop((l ↦ some v) ∗ (l ↦ some w -∗ Φ hl_val(#()))) ⊢ swp s E E hl(v(#l) ← &w) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_store $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

theorem swp_free (l : Loc) (v : Val) :
    iprop((l ↦ some v) ∗ Φ hl_val(#())) ⊢ swp s E E hl(free(#l)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_free $$ Hl
  inext
  iintro _
  iexact HΦ

theorem swp_allocN_seq (v : Val) {n : Int} (hn : 0 < n) :
    iprop(∀ l : Loc, ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v) -∗ Φ hl_val(#l)) ⊢
      swp s E E hl(allocn(#n, &v)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro H
  iapply wp_allocN_seq v hn
  · itrivial
  · inext
    iintro %l Hl
    iapply H
    iapply BigSepL.bigSepL_mono (fun _ => sep_elim_left) $$ Hl

theorem swp_allocN (v : Val) {n : Int} (hn : 0 < n) :
    iprop(∀ l : Loc, l ↦∗ List.replicate n.toNat v -∗ Φ hl_val(#l)) ⊢
      swp s E E hl(allocn(#n, &v)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro H
  iapply wp_allocN v hn
  · itrivial
  · inext
    iintro %l ⟨Hl, _⟩
    iapply H $$ Hl

theorem swp_load_offset {l : Loc} {dq : DFrac} {vs : List Val} {v : Val} {off : Nat}
    (h : vs[off]? = some v) :
    iprop((l ↦∗{dq} vs) ∗ (l ↦∗{dq} vs -∗ Φ v)) ⊢ swp s E E hl(!v(#(l + off))) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_load_offset h $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

theorem swp_store_offset {l : Loc} {vs : List Val} {v w : Val} {off : Nat}
    (h : vs[off]? = some w) :
    iprop((l ↦∗ vs) ∗ (l ↦∗ vs.set off v -∗ Φ hl_val(#()))) ⊢
      swp s E E hl(v(#(l + off)) ← &v) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_store_offset h $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

theorem swp_allocN_vec (v : Val) {n : Int} (hn : 0 < n) :
    iprop(∀ l : Loc, l ↦∗ (Vector.replicate n.toNat v).toList -∗ Φ hl_val(#l)) ⊢
      swp s E E hl(allocn(#n, &v)) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro H
  iapply wp_allocN_vec v hn
  · itrivial
  · inext
    iintro %l ⟨Hl, _⟩
    iapply H $$ Hl

theorem swp_load_offset_vec {l : Loc} {dq : DFrac} {sz : Nat} {off : Fin sz}
    {ws : Vector Val sz} :
    iprop((l ↦∗{dq} ws.toList) ∗ (l ↦∗{dq} ws.toList -∗ Φ ws[off])) ⊢
      swp s E E hl(!v(#(l + off.val))) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_load_offset_vec $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

theorem swp_store_offset_vec {l : Loc} {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v : Val} :
    iprop((l ↦∗ ws.toList) ∗ (l ↦∗ (ws.set off v).toList -∗ Φ hl_val(#()))) ⊢
      swp s E E hl(v(#(l + Int.ofNat off.val)) ← &v) Φ := by
  refine Entails.trans ?_ wp_empty_swp
  iintro ⟨Hl, HΦ⟩
  iapply wp_store_offset_vec $$ Hl
  inext
  iintro Hl
  iapply HΦ $$ Hl

/-! ### The course's names

`hoare_lib.v` re-exports the three laws it uses under `ent_wp_*`. They are the same statements;
the aliases exist so that a proof written against the course's rule set finds them. -/

theorem ent_wp_new (v : Val) :
    iprop(∀ l : Loc, l ↦ some v -∗ Φ hl_val(#l)) ⊢ swp s E E hl(ref(&v)) Φ := swp_alloc v

theorem ent_wp_load (l : Loc) (v : Val) :
    iprop((l ↦ some v) ∗ (l ↦ some v -∗ Φ v)) ⊢ swp s E E hl(!v(#l)) Φ := swp_load l v

theorem ent_wp_store (l : Loc) (v w : Val) :
    iprop((l ↦ some v) ∗ (l ↦ some w -∗ Φ hl_val(#()))) ⊢ swp s E E hl(v(#l) ← &w) Φ :=
  swp_store l v w

end NoLater

end ProgramLogics
