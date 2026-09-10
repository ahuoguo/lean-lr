import LeanLR.ProgramLogics.Concurrency
import Iris.Algebra.Auth
import Iris.Algebra.Numbers

/-!
# A toy `Arc`

`program_logics/arc_sol.v`, adapted there from Diaframe's `arc_simple.v`. An `Arc` is backed by
`Auth ℕ`: the authoritative part records the true reference count and each holder owns one
fragment, so the count is at least the number of live references.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Auth
open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open CommMonoidLike

namespace ProgramLogics.Arc

/-! ## The reference count as a resource algebra -/

abbrev Count := Nat

scoped instance : Associative (Add.add (α := Count)) := ⟨Nat.add_assoc⟩
scoped instance : Commutative (Add.add (α := Count)) := ⟨Nat.add_comm⟩
scoped instance : LeftIdentity (Add.add (α := Count)) (0 : Count) where
scoped instance : LawfulLeftIdentity (Add.add (α := Count)) (0 : Count) := ⟨Nat.zero_add⟩
scoped instance : LeftCancelAdd Count := ⟨Nat.add_left_cancel⟩
scoped instance : COFE Count := COFE.ofDiscrete _
scoped instance : OFE.Discrete Count := ⟨fun h => h⟩
scoped instance : UCMRA Count := CommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete Count := CommMonoidLike.instDiscrete

abbrev ArcRF : COFE.OFunctorPre := constOF (Auth Count)

class ArcG (GF : BundledGFunctors) where [elemG : ElemG GF ArcRF]

attribute [reducible, instance] ArcG.elemG

section ArcGhost

variable {GF : BundledGFunctors} [ArcG GF] {γ : GName} {n : Nat}

def arc_auth (γ : GName) (n : Nat) : IProp GF := iOwn (F := ArcRF) γ (● (n : Count))
def arc_tok (γ : GName) : IProp GF := iOwn (F := ArcRF) γ (◯ (1 : Count))

instance arc_auth_timeless : Timeless (arc_auth (GF := GF) γ n) := by
  unfold arc_auth; infer_instance
instance arc_tok_timeless : Timeless (arc_tok (GF := GF) γ) := by
  unfold arc_tok; infer_instance

theorem arc_alloc :
    ⊢ (iprop(|==> ∃ γ, arc_auth (GF := GF) γ 1 ∗ arc_tok γ) : IProp GF) := by
  unfold arc_auth arc_tok
  refine Entails.trans (iOwn_alloc (F := ArcRF)
    ((● (1 : Count)) • ◯ (1 : Count)) (auth_both_valid_2 trivial ⟨0, rfl⟩)) (BIUpdate.mono ?_)
  iintro ⟨%γ, Ha, Ht⟩
  iexists γ
  iframe Ha Ht

theorem arc_tok_bound : ⊢@{IProp GF} arc_auth γ n -∗ arc_tok γ -∗ ⌜1 ≤ n⌝ := by
  unfold arc_auth arc_tok
  iintro Ha Ht
  icombine Ha Ht gives %Hv
  ipureintro
  obtain ⟨z, hz⟩ := (auth_both_valid_discrete.mp Hv).1
  have hz' : n = 1 + z := hz
  omega

theorem arc_clone_upd :
    ⊢@{IProp GF} arc_auth γ n -∗ |==> (arc_auth γ (n + 1) ∗ arc_tok γ) := by
  unfold arc_auth arc_tok
  refine BI.wand_intro (BI.emp_sep.mp.trans ?_)
  exact (iOwn_update (auth_update_alloc
    (leftCancelAdd_local_update (x := (n : Count)) (y := 0) (x' := n + 1) (y' := 1)
      (by simp [Add.add])))).trans (BIUpdate.mono iOwn_op.mp)

theorem arc_drop_upd (h : 1 ≤ n) :
    ⊢@{IProp GF} arc_auth γ n -∗ arc_tok γ -∗ |==> arc_auth γ (n - 1) := by
  unfold arc_auth arc_tok
  iintro Ha Ht
  iapply iOwn_update_op (auth_update_dealloc
    (leftCancelAdd_local_update (x := (n : Count)) (y := 1) (x' := n - 1) (y' := 0)
      (by simp [Add.add]; omega)))
  isplitl [Ha]
  · iexact Ha
  · iexact Ht

end ArcGhost

/-! ## The implementation

The handle is a pair `(cl, dl)`: `cl` holds the reference count, `dl` the data. -/

def mk_arc : Val := hl_val(λ data, (ref(#(1 : Int)), ref(data)))
def clone : Val := hl_val(λ a, (faa(fst(a), #(1 : Int)); a))
def read : Val := hl_val(λ a, !(snd(a)))
def drop : Val := hl_val(λ a,
  let old := faa(fst(a), #((-1 : Int)));
  if old = #(1 : Int) then (free(fst(a)); free(snd(a))) else #())

section ArcSpec

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [ArcG GF]

def arcN : Namespace := nroot .@ "arc"

/-- While the count is positive the invariant owns both cells; at zero it owns nothing, because
the last dropper has taken them out and freed them. -/
def arc_inv (γ : GName) (cl dl : Loc) : IProp GF :=
  iprop(∃ n : Nat, arc_auth (GF := GF) γ n ∗
    (⌜n = 0⌝ ∨ ((cl ↦ some hl_val(#((n : Int)))) ∗ ∃ w : Val, dl ↦ some w)))

/-- Holding `is_arc` means owning one reference. It is not persistent. -/
def is_arc (v : Val) (γ : GName) : IProp GF :=
  iprop(∃ cl dl : Loc, ⌜v = hl_val((#cl, #dl))⌝ ∗ inv arcN (arc_inv (GF := GF) γ cl dl) ∗
    arc_tok γ)

theorem mk_arc_spec (x : Val) :
    ⊢ Concurrency.hoare (GF := GF) iprop(True) hl(v(&mk_arc) &x)
      (fun v => iprop(∃ γ, is_arc v γ)) := by
  unfold Concurrency.hoare mk_arc
  imodintro
  iintro _
  wp_pures
  wp_alloc dl with Hdl
  wp_alloc cl with Hcl
  wp_pures
  imod arc_alloc (GF := GF) with ⟨%γ, Ha, Ht⟩
  imod inv_alloc arcN ⊤ (arc_inv (GF := GF) γ cl dl) $$ [Ha Hcl Hdl] with #Hinv
  · unfold arc_inv
    iexists 1
    isplitl [Ha]
    · iexact Ha
    iright
    isplitl [Hcl]
    · iexact Hcl
    iexists hl_val(&x)
    iexact Hdl
  imodintro
  iexists γ
  unfold is_arc
  iexists cl
  iexists dl
  isplitr
  · ipureintro; rfl
  iframe Hinv Ht

theorem clone_arc_spec (v : Val) (γ : GName) :
    ⊢ Concurrency.hoare (GF := GF) (is_arc v γ) hl(v(&clone) &v)
      (fun w => iprop(is_arc v γ ∗ is_arc w γ)) := by
  unfold Concurrency.hoare is_arc clone
  imodintro
  iintro ⟨%cl, %dl, %hv, #Hinv, Htok⟩
  subst hv
  wp_pures
  wp_bind (faa(#cl, #(1 : Int)))
  unfold arc_inv
  iinv Hinv with ⟨%n, >Ha, Hinner⟩ Hclose
  icases arc_tok_bound $$ Ha Htok with %Hn
  icases Hinner with ⟨>%Hn0 | ⟨>Hcl, >Hdl⟩⟩
  · exact absurd Hn0 (by omega)
  wp_faa
  imod arc_clone_upd $$ Ha with ⟨Ha, Htok2⟩
  imod Hclose $$ [Ha Hcl Hdl]
  · inext
    iexists (n + 1)
    isplitl [Ha]
    · iexact Ha
    iright
    isplitl [Hcl]
    · simp only [show ((n : Int) + 1) = (((n + 1 : Nat) : Int)) from by omega]
      iexact Hcl
    · iexact Hdl
  imodintro
  wp_pures
  isplitl [Htok]
  · iexists cl
    iexists dl
    isplitr
    · ipureintro; rfl
    iframe Hinv Htok
  · iexists cl
    iexists dl
    isplitr
    · ipureintro; rfl
    iframe Hinv Htok2

theorem read_arc_spec (v : Val) (γ : GName) :
    ⊢ Concurrency.hoare (GF := GF) (is_arc v γ) hl(v(&read) &v) (fun _ => is_arc v γ) := by
  unfold Concurrency.hoare is_arc read
  imodintro
  iintro ⟨%cl, %dl, %hv, #Hinv, Htok⟩
  subst hv
  wp_pures
  unfold arc_inv
  iinv Hinv with ⟨%n, >Ha, Hinner⟩ Hclose
  icases arc_tok_bound $$ Ha Htok with %Hn
  icases Hinner with ⟨>%Hn0 | ⟨>Hcl, %w, >Hdl⟩⟩
  · exact absurd Hn0 (by omega)
  wp_load
  imod Hclose $$ [Ha Hcl Hdl]
  · inext
    iexists n
    isplitl [Ha]
    · iexact Ha
    iright
    isplitl [Hcl]
    · iexact Hcl
    iexists w
    iexact Hdl
  imodintro
  iexists cl
  iexists dl
  isplitr
  · ipureintro; rfl
  iframe Hinv Htok

theorem drop_arc_spec (v : Val) (γ : GName) :
    ⊢ Concurrency.hoare (GF := GF) (is_arc v γ) hl(v(&drop) &v) (fun _ => iprop(True)) := by
  unfold Concurrency.hoare is_arc drop
  imodintro
  iintro ⟨%cl, %dl, %hv, #Hinv, Htok⟩
  subst hv
  wp_pures
  wp_bind (faa(#cl, #((-1 : Int))))
  unfold arc_inv
  iinv Hinv with ⟨%n, >Ha, Hinner⟩ Hclose
  icases arc_tok_bound $$ Ha Htok with %Hn
  icases Hinner with ⟨>%Hn0 | ⟨>Hcl, %w, >Hdl⟩⟩
  · exact absurd Hn0 (by omega)
  wp_faa
  imod arc_drop_upd Hn $$ Ha Htok with Ha
  by_cases hn1 : n = 1
  · subst hn1
    imod Hclose $$ [Ha]
    · inext
      iexists 0
      isplitl [Ha]
      · iexact Ha
      ileft
      ipureintro; rfl
    imodintro
    wp_pures
    simp only [show (hl_val(#(((1 : Nat) : Int))) == hl_val(#(1 : Int))) = true from rfl]
    wp_pures
    wp_free
    wp_pures
    wp_free
    itrivial
  · imod Hclose $$ [Ha Hcl Hdl]
    · inext
      iexists (n - 1)
      isplitl [Ha]
      · iexact Ha
      iright
      isplitl [Hcl]
      · simp only [show ((n : Int) + (-1 : Int)) = (((n - 1 : Nat) : Int)) from by omega]
        iexact Hcl
      iexists w
      iexact Hdl
    imodintro
    wp_pures
    simp only [show (hl_val(#((n : Int))) == hl_val(#(1 : Int))) = false from by
      simp [BEq.beq]; omega]
    wp_pures
    itrivial

end ArcSpec

end ProgramLogics.Arc
