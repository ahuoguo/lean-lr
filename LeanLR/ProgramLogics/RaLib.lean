import Iris.Algebra.Updates
import Iris.Algebra.LocalUpdates
import Iris.Instances.IProp

/-!
# Leibniz resource algebras

`program_logics/ra_lib.v`.

The course carries its own record of RA laws, `LRAMixin`, so that they may be stated with Rocq's
propositional equality rather than a setoid. In `iris-lean` that is already so: `CMRA`'s `assoc`,
`comm`, `pcore_op_left` and `pcore_idem` fields *are* equations, and `CMRA.ofDiscrete` takes
precisely the fields of `LRAMixin` as its arguments. There is therefore no separate structure
here — an "LRA" is a `CMRA` built by `CMRA.ofDiscrete`, and `CMRA.Discrete` is the class that
says so.

What does need restating is the *updates*: `Update`, `UpdateP` and `LocalUpdate` are step-indexed,
whereas the course's are not. The definitions below are the course's, and each comes with the
equivalence that lets `iris-lean`'s ghost-state lemmas be applied to it.
-/

namespace ProgramLogics

open Iris Iris.CMRA

variable {α : Type _} [CMRA α]

/-- A frame-preserving update. -/
def LraUpdate (x y : α) : Prop := ∀ f : Option α, ✓ (x •? f) → ✓ (y •? f)

/-- A nondeterministic frame-preserving update: some element of `P` is reachable. -/
def LraUpdateP (x : α) (P : α → Prop) : Prop :=
  ∀ f : Option α, ✓ (x •? f) → ∃ y, P y ∧ ✓ (y •? f)

/-- `a` composes with no frame whatsoever. -/
def LraExclusive (a : α) : Prop := ∀ b, ¬✓ (a • b)

/-- A local update: the authoritative element may move from `p.1` to `q.1` provided the fragment
moves from `p.2` to `q.2`, whatever the remaining frame. -/
def LraLocalUpdate (p q : α × α) : Prop :=
  ∀ f : Option α, ✓ p.1 → p.1 = p.2 •? f → ✓ q.1 ∧ q.1 = q.2 •? f

/-! ## Relation to `iris-lean`'s step-indexed notions -/

variable [CMRA.Discrete α]

theorem lraUpdate_iff {x y : α} : LraUpdate x y ↔ x ~~> y := Update.discrete.symm

theorem lraUpdateP_iff {x : α} {P : α → Prop} : LraUpdateP x P ↔ x ~~>: P := UpdateP.discrete.symm

theorem lraExclusive_iff {a : α} : LraExclusive a ↔ CMRA.Exclusive a where
  mp h := ⟨fun b hb => h b (CMRA.discrete_valid hb)⟩
  mpr h b hb := h.exclusive0_l b hb.validN

theorem lraLocalUpdate_iff {x y x' y' : α} :
    LraLocalUpdate (x, y) (x', y') ↔ (x, y) ~l~> (x', y') :=
  (LocalUpdate.discrete x y x' y').symm

/-! ## Ghost state -/

variable {GF : BundledGFunctors} {F : COFE.OFunctorPre} [RFunctorContractive F]
variable [E : ElemG GF F] [CMRA.Discrete (F.ap (IProp GF))]

/-- A frame-preserving update may be performed under `iOwn`. -/
theorem own_lra_update {γ : GName} {a b : F.ap (IProp GF)} (h : LraUpdate a b) :
    iOwn γ a ⊢ iprop(|==> iOwn γ b) :=
  iOwn_update (lraUpdate_iff.mp h)

end ProgramLogics
