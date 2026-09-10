import Iris.Algebra.Auth
import Iris.ProofMode
import Iris.Instances.IProp
import LeanLR.ProgramLogics.RaLib

/-!
# Resource algebras

`program_logics/resource_algebras_1_sol.v`.

The course builds a dozen resource algebras from scratch — options, sums, products, `Excl`,
`Agree`, `Auth`, `(ℕ, +)`, `(ℕ, max)`, `(ℕ, min)`, `(ℤ, +)`, fractions — and then a first ghost
theory on top of `Auth (ℕ, max)`. All of those algebras are in `Iris.Algebra.*` already, so this
file does the two things the port can usefully add: it builds one algebra by hand, to show what
`CMRA.ofDiscreteTotal` wants, and it assembles the monotone-counter ghost theory on top of it.
-/

namespace ProgramLogics.ResourceAlgebras

open Iris Iris.BI Iris.CMRA Iris.OFE Auth Iris.ProofMode

/-! ## The (ℕ, max) resource algebra

Every element is valid, composition is `max`, and every element is its own core. -/

/-- The carrier of the (ℕ, max) resource algebra. -/
structure MaxNat where
  ofNat ::
  toNat : Nat

namespace MaxNat

theorem ext {a b : MaxNat} (h : a.toNat = b.toNat) : a = b := congrArg ofNat h

/-- Composition. -/
def max (a b : MaxNat) : MaxNat := ofNat (a.toNat.max b.toNat)

@[simp, grind =] theorem toNat_max (a b : MaxNat) : (a.max b).toNat = a.toNat.max b.toNat := rfl

instance : COFE MaxNat := COFE.ofDiscrete _
instance : OFE.Discrete MaxNat := ⟨fun h => h⟩

instance : CMRA MaxNat :=
  CMRA.ofDiscreteTotal id max (fun _ => True)
    (fun _ _ _ => ext (by grind))
    (fun _ _ => ext (by grind))
    (fun _ => ext (by grind))
    (fun _ => rfl)
    (fun _ _ h => h)
    (fun _ _ _ => trivial)

instance : CMRA.Discrete MaxNat where discrete_valid := id

@[simp, grind =] theorem toNat_op (a b : MaxNat) : (a • b).toNat = a.toNat.max b.toNat := rfl
theorem op_eq (a b : MaxNat) : a • b = a.max b := rfl
theorem pcore_eq (a : MaxNat) : pcore a = some a := rfl
theorem valid (a : MaxNat) : ✓ a := trivial

instance coreId (a : MaxNat) : CMRA.CoreId a := ⟨pcore_eq a⟩

instance : UCMRA MaxNat where
  unit := ofNat 0
  unit_valid := trivial
  unit_left_id := ext (by grind)
  pcore_unit := rfl

@[grind =] theorem inc_iff {a b : MaxNat} : a ≼ b ↔ a.toNat ≤ b.toNat where
  mp | ⟨_, h⟩ => by grind [congrArg toNat h]
  mpr h := ⟨b, ext (by grind)⟩

/-- Updates in this algebra are unconstrained: every element composes with every other. -/
theorem update (a b : MaxNat) : LraUpdate a b := fun _ _ => trivial

/-- Raising the authoritative element is a local update, because `max` is idempotent. -/
theorem local_update {a b a' : MaxNat} (h : a.toNat ≤ a'.toNat) : (a, b) ~l~> (a', a') := by
  refine lraLocalUpdate_iff.mp fun f _ he => ⟨trivial, ?_⟩
  cases f with
  | none => rfl
  | some c =>
    simp only [CMRA.op?] at he ⊢
    exact ext (by grind [congrArg toNat he])

end MaxNat

/-! ## A ghost theory for a monotone natural number

`Auth MaxNat` is registered with Iris as usual: an `ElemG` field on a class over
`BundledGFunctors`, whose instances Lean then synthesizes. -/

abbrev MonoNatRF : COFE.OFunctorPre := constOF (Auth MaxNat)

class MonoNatG (GF : BundledGFunctors) where [elemG : ElemG GF MonoNatRF]

attribute [reducible, instance] MonoNatG.elemG

section MonoNat

variable {GF : BundledGFunctors} [MonoNatG GF] {γ : GName} {n m : Nat}

/-- The authoritative bound, together with the fragment that witnesses it. -/
def monoNatAuth (γ : GName) (n : Nat) : IProp GF :=
  iOwn (F := MonoNatRF) γ ((● MaxNat.ofNat n) • ◯ MaxNat.ofNat n)

/-- A lower bound on the authoritative element. -/
def monoNatFrag (γ : GName) (n : Nat) : IProp GF :=
  iOwn (F := MonoNatRF) γ (◯ MaxNat.ofNat n)

instance : Persistent (monoNatFrag (GF := GF) γ n) := by
  unfold monoNatFrag; infer_instance

/-- A bound may be handed out, and being persistent it may be handed out again. -/
theorem mono_make_bound :
    monoNatAuth (GF := GF) γ n ⊢ iprop(monoNatAuth γ n ∗ monoNatFrag γ n) := by
  unfold monoNatAuth monoNatFrag
  iintro Hγ
  icases iOwn_op.mp $$ Hγ with ⟨Hauth, #Hfrag⟩
  isplitl [Hauth]
  · iapply iOwn_op.mpr
    isplitl [Hauth]
    · iexact Hauth
    iexact Hfrag
  iexact Hfrag

/-- A fragment is a genuine lower bound on the authoritative element. -/
theorem mono_use_bound :
    monoNatAuth (GF := GF) γ n ⊢ iprop(monoNatFrag γ m -∗ ⌜m ≤ n⌝) := by
  unfold monoNatAuth monoNatFrag
  iintro Hγ Hfrag
  icases iOwn_op.mp $$ Hγ with ⟨Hauth, _⟩
  icombine Hauth Hfrag gives %Hv
  ipureintro
  exact MaxNat.inc_iff.mp (auth_both_valid_discrete.mp Hv).1

/-- The authoritative element may always be raised. -/
theorem mono_increase_val :
    monoNatAuth (GF := GF) γ n ⊢ iprop(|==> monoNatAuth γ (n + 1)) :=
  own_lra_update (lraUpdate_iff.mpr (auth_update (MaxNat.local_update (by simp))))

/-- A fresh monotone counter may be allocated at any value. -/
theorem mono_new (n : Nat) : ⊢ (iprop(|==> ∃ γ, monoNatAuth (GF := GF) γ n) : IProp GF) := by
  unfold monoNatAuth
  exact iOwn_alloc _ (auth_both_valid_2 trivial (MaxNat.inc_iff.mpr (by simp)))

end MonoNat

end ProgramLogics.ResourceAlgebras
