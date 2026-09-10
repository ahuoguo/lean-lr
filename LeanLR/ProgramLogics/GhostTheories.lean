import Iris.Algebra.Auth
import Iris.Algebra.Csum
import Iris.Algebra.Frac
import Iris.Algebra.Heap
import Iris.ProofMode
import Iris.Instances.IProp
import LeanLR.ProgramLogics.RaLib

/-!
# Ghost theories

`program_logics/resource_algebras_2_sol.v`.

Each section registers one resource algebra with Iris and derives the laws that its ghost
assertions obey. The shape is always the same: an `abbrev` for the functor, a class carrying the
`ElemG` witness, and `iOwn` applied to the algebra's elements.
-/

namespace ProgramLogics.GhostTheories

open Iris Iris.BI Iris.CMRA Iris.OFE Iris.Std Auth Iris.ProofMode

/-! ## One-shot ghost state

A ghost location that starts out *pending* and may be *shot* once, after which its value is fixed
and freely duplicable. -/

abbrev OneShotRF (A : Type) : COFE.OFunctorPre := constOF (Csum (Excl Unit) (Agree (DiscreteO A)))

class OneShotG (GF : BundledGFunctors) (A : Type) where [elemG : ElemG GF (OneShotRF A)]

attribute [reducible, instance] OneShotG.elemG

section OneShot

variable {A : Type} {GF : BundledGFunctors} [OneShotG GF A] {γ : GName} {a b : A}

def osPending (A : Type) [OneShotG GF A] (γ : GName) : IProp GF :=
  iOwn (F := OneShotRF A) γ (.inl (.excl ()))

def osShot (γ : GName) (a : A) : IProp GF :=
  iOwn (F := OneShotRF A) γ (.inr (toAgree (DiscreteO.mk a)))

instance : Persistent (osShot (GF := GF) γ a) := by unfold osShot; infer_instance
instance : Timeless (osShot (GF := GF) γ a) := by unfold osShot; infer_instance
instance : Timeless (osPending (GF := GF) A γ) := by unfold osPending; infer_instance

theorem os_pending_alloc : ⊢ (iprop(|==> ∃ γ, osPending (GF := GF) A γ) : IProp GF) :=
  iOwn_alloc _ trivial

theorem os_pending_shoot (a : A) :
    osPending (GF := GF) A γ ⊢ iprop(|==> osShot γ a) :=
  iOwn_update (Update.exclusive (Csum.inr_valid.mpr Agree.toAgree_valid))

theorem os_pending_shot_False : osPending (GF := GF) A γ ⊢ iprop(osShot γ a -∗ False) := by
  unfold osPending osShot
  iintro Hp Hs
  icombine Hp Hs gives %Hv
  exact Hv.elim

theorem os_pending_pending_False :
    osPending (GF := GF) A γ ⊢ iprop(osPending A γ -∗ False) := by
  unfold osPending
  iintro Hp Hp'
  icombine Hp Hp' gives %Hv
  exact Hv.elim

theorem os_shot_agree : osShot (GF := GF) γ a ⊢ iprop(osShot γ b -∗ ⌜a = b⌝) := by
  unfold osShot
  iintro Ha Hb
  icombine Ha Hb gives %Hv
  ipureintro
  exact DiscreteO.eqv_inj (toAgree_op_valid_iff_eq.mp (Csum.inr_valid.mp Hv))

end OneShot

/-! ## Synchronised ghost state

Two halves of one ghost variable: each holds the same value, and neither can move without the
other. -/

abbrev HalvesRF (A : Type) : COFE.OFunctorPre := constOF (Auth (Option (Excl (DiscreteO A))))

class HalvesG (GF : BundledGFunctors) (A : Type) where [elemG : ElemG GF (HalvesRF A)]

attribute [reducible, instance] HalvesG.elemG

section Halves

variable {A : Type} {GF : BundledGFunctors} [HalvesG GF A] {γ : GName} {a b : A}

def gleft (γ : GName) (a : A) : IProp GF :=
  iOwn (F := HalvesRF A) γ (● some (Excl.excl ⟨a⟩))

def gright (γ : GName) (a : A) : IProp GF :=
  iOwn (F := HalvesRF A) γ (◯ some (Excl.excl ⟨a⟩))

instance : Timeless (gleft (GF := GF) γ a) := by unfold gleft; infer_instance
instance : Timeless (gright (GF := GF) γ a) := by unfold gright; infer_instance

theorem ghalves_alloc (a : A) :
    ⊢ (iprop(|==> ∃ γ, gleft (GF := GF) γ a ∗ gright γ a) : IProp GF) := by
  unfold gleft gright
  have hv : ✓ (some (Excl.excl (⟨a⟩ : DiscreteO A))) := trivial
  refine Entails.trans (iOwn_alloc (F := HalvesRF A) _
    (auth_both_valid_2 hv (Excl.excl_included.mpr rfl))) (BIUpdate.mono ?_)
  iintro ⟨%γ, Hl, Hr⟩
  iexists γ
  iframe Hl Hr

theorem ghalves_agree : gleft (GF := GF) γ a ⊢ iprop(gright γ b -∗ ⌜a = b⌝) := by
  unfold gleft gright
  iintro Hl Hr
  icombine Hl Hr gives %Hv
  ipureintro
  exact (DiscreteO.eqv_inj (Excl.excl_included.mp (auth_both_valid_discrete.mp Hv).1)).symm

theorem ghalves_update (c : A) :
    gleft (GF := GF) γ a ⊢ iprop(gright γ b -∗ |==> (gleft γ c ∗ gright γ c)) := by
  refine BI.wand_intro ?_
  unfold gleft gright
  exact (iOwn_update_op (auth_update (LocalUpdate.option
    (LocalUpdate.exclusive (x' := Excl.excl (⟨c⟩ : DiscreteO A)) trivial)))).trans
    (BIUpdate.mono iOwn_op.mp)

end Halves

/-! ## Fractional ghost variables

`Qp × Agree A`: the fraction says how much of the variable one owns, and the `Agree` component
forces all owners to agree on its value. -/

abbrev GvarRF (A : Type) : COFE.OFunctorPre := constOF (Qp × Agree (DiscreteO A))

class GvarG (GF : BundledGFunctors) (A : Type) where [elemG : ElemG GF (GvarRF A)]

attribute [reducible, instance] GvarG.elemG

section Gvar

variable {A : Type} {GF : BundledGFunctors} [GvarG GF A] {γ : GName} {q q' : Qp} {a b : A}

def gvar (γ : GName) (q : Qp) (a : A) : IProp GF :=
  iOwn (F := GvarRF A) γ (q, toAgree (DiscreteO.mk a))

instance : Timeless (gvar (GF := GF) γ q a) := by unfold gvar; infer_instance

theorem gvar_alloc (a : A) : ⊢ (iprop(|==> ∃ γ, gvar (GF := GF) γ 1 a) : IProp GF) :=
  iOwn_alloc _ ⟨Qp.valid_one, Agree.toAgree_valid⟩

theorem gvar_agree :
    gvar (GF := GF) γ q a ⊢ iprop(gvar γ q' b -∗ ⌜(q + q').val ≤ 1 ∧ a = b⌝) := by
  unfold gvar
  iintro Ha Hb
  icombine Ha Hb gives %Hv
  ipureintro
  exact ⟨Hv.1, DiscreteO.eqv_inj (toAgree_op_valid_iff_eq.mp Hv.2)⟩

/-- Ownership of a variable splits and merges along the fraction. -/
theorem gvar_fractional :
    iprop(gvar (GF := GF) γ q a ∗ gvar γ q' a) ⊣⊢ gvar γ (q + q') a := by
  unfold gvar
  have e : ((q, toAgree (DiscreteO.mk a)) • (q', toAgree (DiscreteO.mk a)) :
      Qp × Agree (DiscreteO A)) = (q + q', toAgree (DiscreteO.mk a)) :=
    congrArg (Prod.mk (q + q')) Agree.idemp
  exact e ▸ iOwn_op.symm

theorem gvar_update (b : A) : gvar (GF := GF) γ 1 a ⊢ iprop(|==> gvar γ 1 b) :=
  iOwn_update (Update.exclusive ⟨Qp.valid_one, Agree.toAgree_valid⟩)

end Gvar

/-! ## Maps of agreements

`Auth (K ⇀ Agree B)`: the authoritative element is the whole map, and a fragment is a single
persistent entry. -/

abbrev AgmapRF {K : Type} (M : Type → Type) [LawfulPartialMap M K] (B : Type) :
    COFE.OFunctorPre := constOF (Auth (M (Agree (DiscreteO B))))

private theorem toAgree_some_inc {B : Type} {a b : DiscreteO B}
    (h : (some (toAgree a) : Option (Agree (DiscreteO B))) ≼ some (toAgree b)) : a = b := by
  rcases Option.some_inc_some_iff.mp h with h | h
  · exact toAgree.inj (n := 0) h.dist
  · exact Agree.toAgree_included.mp h

section Agmap

variable {K B : Type} {M : Type → Type} [LawfulPartialMap M K]
variable {GF : BundledGFunctors} [ElemG GF (AgmapRF M B)]
variable {γ : GName} {m : M B} {k : K} {b : B}

def toAgmap (m : M B) : M (Agree (DiscreteO B)) :=
  Iris.Std.PartialMap.map (fun x : B => toAgree (DiscreteO.mk x)) m

def agmapAuth (γ : GName) (m : M B) : IProp GF :=
  iOwn (F := AgmapRF M B) γ (● toAgmap m)

def agmapElem (γ : GName) (k : K) (b : B) : IProp GF :=
  iOwn (F := AgmapRF M B) γ (◯ Iris.Std.PartialMap.singleton k (toAgree (DiscreteO.mk b)))

instance : Persistent (agmapElem (M := M) (B := B) (GF := GF) γ k b) := by
  unfold agmapElem; infer_instance
instance : Timeless (agmapAuth (M := M) (B := B) (GF := GF) γ m) := by
  unfold agmapAuth; infer_instance
instance : Timeless (agmapElem (M := M) (B := B) (GF := GF) γ k b) := by
  unfold agmapElem; infer_instance

theorem agmap_alloc_empty :
    ⊢ (iprop(|==> ∃ γ, agmapAuth (M := M) (B := B) (GF := GF) γ ∅) : IProp GF) := by
  unfold agmapAuth toAgmap
  rw [Iris.Std.LawfulPartialMap.map_empty]
  exact iOwn_alloc _ (auth_valid.mpr UCMRA.unit_valid)

theorem agmap_insert (h : get? m k = none) :
    agmapAuth (M := M) (B := B) (GF := GF) γ m ⊢
      iprop(|==> (agmapAuth γ (insert m k b) ∗ agmapElem (M := M) γ k b)) := by
  unfold agmapAuth agmapElem toAgmap
  rw [Iris.Std.LawfulPartialMap.map_insert]
  refine (iOwn_update (auth_update_alloc (Heap.alloc_singleton_local_update ?_ ?_))).trans
    (BIUpdate.mono iOwn_op.mp)
  · rw [Iris.Std.LawfulPartialMap.get?_map, h]; rfl
  · exact Agree.toAgree_valid

theorem agmap_lookup :
    agmapAuth (M := M) (B := B) (GF := GF) γ m ⊢
      iprop(agmapElem (M := M) γ k b -∗ ⌜get? m k = some b⌝) := by
  unfold agmapAuth agmapElem
  iintro Ha He
  icombine Ha He gives %Hv
  ipureintro
  obtain ⟨y, hy, hinc⟩ := Heap.singleton_inc_iff.mp (auth_both_valid_discrete.mp Hv).1
  rw [toAgmap, Iris.Std.LawfulPartialMap.get?_map] at hy
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hy
  exact hb'.trans (congrArg some (DiscreteO.eqv_inj (toAgree_some_inc hinc)).symm)

end Agmap

/-! ## Maps of exclusive elements

`Auth (K ⇀ Excl B)`: the same shape, but an entry is now exclusive, so its owner may change or
remove it. -/

abbrev ExmapRF {K : Type} (M : Type → Type) [LawfulPartialMap M K] (B : Type) :
    COFE.OFunctorPre := constOF (Auth (M (Excl (DiscreteO B))))

section Exmap

variable {K B : Type} {M : Type → Type} [LawfulPartialMap M K]
variable {GF : BundledGFunctors} [ElemG GF (ExmapRF M B)]
variable {γ : GName} {m : M B} {k : K} {b : B}

def toExmap (m : M B) : M (Excl (DiscreteO B)) :=
  Iris.Std.PartialMap.map (fun x : B => Excl.excl (DiscreteO.mk x)) m

def exmapAuth (γ : GName) (m : M B) : IProp GF :=
  iOwn (F := ExmapRF M B) γ (● toExmap m)

def exmapElem (γ : GName) (k : K) (b : B) : IProp GF :=
  iOwn (F := ExmapRF M B) γ (◯ Iris.Std.PartialMap.singleton k (Excl.excl (DiscreteO.mk b)))

instance : Timeless (exmapAuth (M := M) (B := B) (GF := GF) γ m) := by
  unfold exmapAuth; infer_instance
instance : Timeless (exmapElem (M := M) (B := B) (GF := GF) γ k b) := by
  unfold exmapElem; infer_instance

theorem exmap_alloc_empty :
    ⊢ (iprop(|==> ∃ γ, exmapAuth (M := M) (B := B) (GF := GF) γ ∅) : IProp GF) := by
  unfold exmapAuth toExmap
  rw [Iris.Std.LawfulPartialMap.map_empty]
  exact iOwn_alloc _ (auth_valid.mpr UCMRA.unit_valid)

theorem exmap_insert (h : get? m k = none) :
    exmapAuth (M := M) (B := B) (GF := GF) γ m ⊢
      iprop(|==> (exmapAuth γ (insert m k b) ∗ exmapElem (M := M) γ k b)) := by
  unfold exmapAuth exmapElem toExmap
  rw [Iris.Std.LawfulPartialMap.map_insert]
  refine (iOwn_update (auth_update_alloc (Heap.alloc_singleton_local_update ?_ trivial))).trans
    (BIUpdate.mono iOwn_op.mp)
  rw [Iris.Std.LawfulPartialMap.get?_map, h]; rfl

theorem exmap_lookup :
    exmapAuth (M := M) (B := B) (GF := GF) γ m ⊢
      iprop(exmapElem (M := M) γ k b -∗ ⌜get? m k = some b⌝) := by
  unfold exmapAuth exmapElem
  iintro Ha He
  icombine Ha He gives %Hv
  ipureintro
  obtain ⟨y, hy, hinc⟩ := Heap.singleton_inc_iff.mp (auth_both_valid_discrete.mp Hv).1
  rw [toExmap, Iris.Std.LawfulPartialMap.get?_map] at hy
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hy
  exact hb'.trans (congrArg some (DiscreteO.eqv_inj (Excl.excl_included.mp hinc)).symm)

/-- An exclusive entry may be overwritten. -/
theorem exmap_update (c : B) :
    exmapAuth (M := M) (B := B) (GF := GF) γ m ⊢ iprop(exmapElem (M := M) γ k b -∗
      |==> (exmapAuth γ (insert m k c) ∗ exmapElem (M := M) γ k c)) := by
  refine BI.wand_intro ?_
  unfold exmapAuth exmapElem toExmap
  rw [Iris.Std.LawfulPartialMap.map_insert]
  exact (iOwn_update_op (auth_update (Heap.singleton_local_update_any
    (fun _ _ => LocalUpdate.exclusive trivial)))).trans (BIUpdate.mono iOwn_op.mp)

/-- An exclusive entry may be removed. -/
theorem exmap_delete :
    exmapAuth (M := M) (B := B) (GF := GF) γ m ⊢
      iprop(exmapElem (M := M) γ k b -∗ |==> exmapAuth γ (delete m k)) := by
  refine BI.wand_intro ?_
  unfold exmapAuth exmapElem toExmap
  rw [Iris.Std.LawfulPartialMap.map_delete]
  exact iOwn_update_op (auth_update_dealloc
    (Heap.delete_singleton_local_update (Excl.excl (DiscreteO.mk b))))

end Exmap

end ProgramLogics.GhostTheories
