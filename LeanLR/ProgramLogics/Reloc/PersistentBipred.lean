import Iris.BI
import Iris.Algebra.OFE

/-!
# Persistent bipredicates

`program_logics/reloc/persistent_bipred.v`, itself taken from `iris/examples`. This is the domain
of *relational* semantic types: binary relations valued in a BI whose every instance is
persistent.

As with the unary `PersistentPred`, a `Subtype` does what Rocq needs a record for, and inherits
its OFE from `Iris.Algebra.OFE`; only completeness has to be proved.
-/

open Iris Iris.BI Iris.OFE

namespace ProgramLogics.Reloc

/-- Binary relations on `A`, valued in `PROP`, that are persistent at every pair. -/
abbrev PersistentBipred (A : Type _) (PROP : Type _) [BI PROP] :=
  Subtype (fun Φ : A → A → PROP => ∀ x y, Persistent (Φ x y))

namespace PersistentBipred

variable {A : Type _} {PROP : Type _} [BI PROP]

/-- The underlying relation. -/
def car (Φ : PersistentBipred A PROP) : A → A → PROP := Φ.val

instance : CoeFun (PersistentBipred A PROP) (fun _ => A → A → PROP) := ⟨car⟩

instance persistent (Φ : PersistentBipred A PROP) (x y : A) : Persistent (Φ x y) :=
  Φ.property x y

/-- Two persistent bipredicates are equal exactly when they agree pointwise. -/
theorem ext {Φ Ψ : PersistentBipred A PROP} (h : ∀ x y, Φ x y = Ψ x y) : Φ = Ψ :=
  Subtype.ext (funext fun x => funext (h x))

instance : IsCOFE (PersistentBipred A PROP) :=
  sigCofe (LimitPreserving.forall _ fun x => LimitPreserving.forall _ fun y =>
    limitPreserving_persistent (A := A → A → PROP) (fun Φ => Φ x y)
      (Φne := ⟨fun {_ _ _} h => h x y⟩))

instance : Inhabited (PersistentBipred A PROP) :=
  ⟨⟨fun _ _ => iprop(True), fun _ _ => inferInstance⟩⟩

end PersistentBipred

end ProgramLogics.Reloc
