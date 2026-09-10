import Iris.BI
import Iris.Algebra.OFE

/-!
# Persistent predicates

`program_logics/logrel/persistent_pred.v`, itself taken from `iris/examples`. This is the domain
of semantic types: predicates valued in a BI whose every instance is persistent, so that a
semantic type may be used more than once.

Rocq needs a record with a coercion; in Lean a `Subtype` does the same job and inherits its OFE
from `Iris.Algebra.OFE`, so the whole file is the completeness proof. `BI` already extends `COFE`,
so no extra hypothesis on `PROP` is needed.
-/

open Iris Iris.BI Iris.OFE

namespace ProgramLogics.LogRel

/-- Predicates on `A`, valued in `PROP`, that are persistent at every argument. -/
abbrev PersistentPred (A : Type _) (PROP : Type _) [BI PROP] :=
  Subtype (fun Φ : A → PROP => ∀ x, Persistent (Φ x))

namespace PersistentPred

variable {A : Type _} {PROP : Type _} [BI PROP]

/-- The underlying predicate. -/
def car (Φ : PersistentPred A PROP) : A → PROP := Φ.val

instance : CoeFun (PersistentPred A PROP) (fun _ => A → PROP) := ⟨car⟩

instance persistent (Φ : PersistentPred A PROP) (x : A) : Persistent (Φ x) := Φ.property x

/-- Two persistent predicates are equal exactly when they agree pointwise. -/
theorem ext {Φ Ψ : PersistentPred A PROP} (h : ∀ x, Φ x = Ψ x) : Φ = Ψ :=
  Subtype.ext (funext h)

instance : IsCOFE (PersistentPred A PROP) :=
  sigCofe (LimitPreserving.forall _ fun x =>
    limitPreserving_persistent (A := A → PROP) (fun Φ => Φ x) (Φne := ⟨fun {_ _ _} h => h x⟩))

instance : Inhabited (PersistentPred A PROP) := ⟨⟨fun _ => iprop(True), fun _ => inferInstance⟩⟩

end PersistentPred

end ProgramLogics.LogRel
