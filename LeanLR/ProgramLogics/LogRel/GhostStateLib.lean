import Iris.BI.Lib.MonoNat
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.GhostMap
import Iris.HeapLang.PrimitiveLaws
import LeanLR.ProgramLogics.GhostTheories

/-!
# Ghost-state library

`program_logics/logrel/ghost_state_lib.v`. The same ghost theories as `GhostTheories.lean`, but
built on the library modules — `Iris.MonoNat`, `Iris.ghost_var`, `Iris.ghost_map` — rather than
from the algebras. That is how one would actually use them, and it is what the logical relation
below is stated against.

Rocq seals each definition so that its clients see only the interface. Lean has no `seal`; the
definitions are ordinary and the `*_eq` unfolding lemmas are not needed.
-/

open Iris Iris.BI Iris.Std Iris.ProofMode

namespace ProgramLogics.LogRel

/-! ## The update modality -/

section Updates

variable {GF : BundledGFunctors} {hlc : HasLC} {P Q : IProp GF}

theorem upd_return : P ⊢ iprop(|==> P) := BIUpdate.intro

theorem upd_bind : ⊢@{IProp GF} iprop(|==> P) -∗ (P -∗ |==> Q) -∗ |==> Q := by
  iintro Hp Hq
  imod Hp
  iapply Hq $$ Hp

theorem upd_wp [Iris.HeapLang.HeapLangGS hlc GF] {e : HeapLang.Exp}
    {Φ : HeapLang.Val → IProp GF} : iprop(|==> WP e {{ Φ }}) ⊢ WP e {{ Φ }} := by
  iintro H
  imod H
  iexact H

end Updates

/-! ## A monotone natural number -/

section MonoNat

variable {GF : BundledGFunctors} [MonoNatG GF] {γ : GName} {n m : Nat}

/-- Full ownership of the authoritative bound. -/
def mono (γ : GName) (n : Nat) : IProp GF := iprop(γ ↪●MN MaxNat.ofNat n)

/-- A persistent lower bound. -/
def lb (γ : GName) (n : Nat) : IProp GF := iprop(γ ↪◯MN MaxNat.ofNat n)

instance mono_nat_lb_persistent : Persistent (lb (GF := GF) γ n) := by
  unfold lb; infer_instance
instance mono_nat_lb_timeless : Timeless (lb (GF := GF) γ n) := by
  unfold lb; infer_instance
instance mono_nat_mono_timeless : Timeless (mono (GF := GF) γ n) := by
  unfold mono; infer_instance

theorem mono_nat_make_bound : mono (GF := GF) γ n ⊢ lb γ n := by
  unfold mono lb
  iintro H
  iapply MonoNat.lb_own_get γ _ _ $$ H

/-- Reading off the bound keeps the authoritative element: this is what Rocq's `iPoseProof … as
"#Hbound"` does in one step, `lb` being persistent. -/
theorem mono_nat_get_bound : mono (GF := GF) γ n ⊢ iprop(mono γ n ∗ lb γ n) :=
  (BI.and_intro .rfl mono_nat_make_bound).trans BI.persistent_and_sep_mp

theorem mono_nat_use_bound : ⊢@{IProp GF} mono γ n -∗ lb γ m -∗ ⌜m ≤ n⌝ := by
  unfold mono lb
  iintro Hauth Hlb
  icases MonoNat.auth_lb_own_valid γ _ _ _ $$ Hauth Hlb with %Hv
  ipureintro
  exact Hv.2

/-- Using the bound keeps the authoritative element; the conclusion being pure, this is the one
step Rocq's `iPoseProof … as "%Hleq"` takes. -/
theorem mono_nat_use_bound' :
    iprop(mono (GF := GF) γ n ∗ lb γ m) ⊢ iprop(mono γ n ∗ ⌜m ≤ n⌝) := by
  refine (BI.and_intro BI.sep_elim_left ?_).trans BI.persistent_and_sep_mp
  iintro ⟨Hauth, Hlb⟩
  iapply mono_nat_use_bound $$ Hauth Hlb

theorem mono_nat_increase_val : ⊢@{IProp GF} mono γ n -∗ |==> mono γ (n + 1) := by
  unfold mono
  iintro Hauth
  imod MonoNat.own_update γ (MaxNat.ofNat n) (MaxNat.ofNat (n + 1)) (by simp) $$ Hauth
    with ⟨Hauth, _⟩
  imodintro
  iexact Hauth

theorem mono_nat_new (n : Nat) : ⊢ (iprop(|==> ∃ γ, mono (GF := GF) γ n) : IProp GF) := by
  unfold mono
  imod MonoNat.own_alloc (MaxNat.ofNat n) with ⟨%γ, Hauth, _⟩
  imodintro
  iexists γ
  iexact Hauth

end MonoNat

/-! ## Two halves of one ghost variable -/

section Halves

variable {A : Type} {GF : BundledGFunctors} [GhostVarG GF A] {γ : GName} {a b : A}

/-- One half of a ghost variable. Rocq abbreviates the two halves `left` and `right`; they are the
same assertion. -/
def ghalf (γ : GName) (a : A) : IProp GF := iprop(γ ↪VAR{.own (1 : Qp).half} a)

instance ghalf_timeless : Timeless (ghalf (GF := GF) γ a) := by unfold ghalf; infer_instance

theorem ghalves_alloc (a : A) :
    ⊢ (iprop(|==> ∃ γ, (ghalf (GF := GF) γ a ∗ ghalf γ a)) : IProp GF) := by
  imod ghost_var_alloc (GF := GF) a with ⟨%γ, Hγ⟩
  imodintro
  iexists γ
  unfold ghalf
  iapply ghost_var_split γ a (1 : Qp).half (1 : Qp).half
  ieval (rewrite [Qp.half_add_half])
  iexact Hγ

theorem ghalves_agree : ⊢@{IProp GF} ghalf γ a -∗ ghalf γ b -∗ ⌜a = b⌝ := by
  unfold ghalf
  exact ghost_var_agree γ a _ b _

/-- Agreement keeps both halves; the conclusion is pure. -/
theorem ghalves_agree' :
    iprop(ghalf (GF := GF) γ a ∗ ghalf γ b) ⊢ iprop((ghalf γ a ∗ ghalf γ b) ∗ ⌜a = b⌝) := by
  refine (BI.and_intro .rfl ?_).trans BI.persistent_and_sep_mp
  iintro ⟨H1, H2⟩
  iapply ghalves_agree $$ H1 H2

theorem ghalves_update (c : A) :
    ⊢@{IProp GF} ghalf γ a -∗ ghalf γ b -∗ |==> (ghalf γ c ∗ ghalf γ c) := by
  unfold ghalf
  exact ghost_var_update_halves c γ a b

end Halves

/-! ## Maps of agreements

An entry is handed out with a discarded fraction, which is what makes it persistent. -/

section Agmap

variable {K V : Type} {H : Type → Type} [LawfulFiniteMap H K]
variable {GF : BundledGFunctors} [GhostMapG GF K V H] {γ : GName} {M : H V} {k : K} {v w : V}

/-- The authoritative map. -/
def agmapAuth (γ : GName) (M : H V) : IProp GF := iprop(γ ↪●MAP M)

/-- A single, persistent entry. -/
def agmapElem (γ : GName) (k : K) (v : V) : IProp GF := iprop(γ ↪◯MAP[k]{.discard} v)

instance agmap_elem_persistent : Persistent (agmapElem (H := H) (GF := GF) γ k v) := by
  unfold agmapElem; infer_instance
instance agmap_elem_timeless : Timeless (agmapElem (H := H) (GF := GF) γ k v) := by
  unfold agmapElem; infer_instance
instance agmap_auth_timeless : Timeless (agmapAuth (GF := GF) γ M) := by
  unfold agmapAuth; infer_instance

theorem agmap_auth_alloc_empty [DecidableEq K] :
    ⊢ (iprop(|==> ∃ γ, agmapAuth (H := H) (V := V) (GF := GF) γ ∅) : IProp GF) :=
  ghost_map_alloc_empty

theorem agmap_auth_insert (h : get? M k = none) :
    ⊢@{IProp GF} agmapAuth γ M -∗ |==> (agmapAuth γ (insert M k v) ∗ agmapElem (H := H) γ k v) := by
  unfold agmapAuth agmapElem
  iintro Hauth
  imod ghost_map_insert k v h $$ Hauth with ⟨Hauth, Helem⟩
  imod ghost_map_elem_persist γ k _ v $$ Helem with #Helem
  imodintro
  iframe Hauth Helem

theorem agmap_auth_lookup :
    ⊢@{IProp GF} agmapAuth γ M -∗ agmapElem (H := H) γ k v -∗ ⌜get? M k = some v⌝ := by
  unfold agmapAuth agmapElem
  exact ghost_map_lookup

theorem agmap_elem_agree :
    ⊢@{IProp GF} agmapElem (H := H) γ k v -∗ agmapElem γ k w -∗ ⌜v = w⌝ := by
  unfold agmapElem
  iintro H1 H2
  iapply ghost_map_elem_agree γ k _ _ v w
  isplitl [H1]
  · iexact H1
  iexact H2

end Agmap

end ProgramLogics.LogRel
