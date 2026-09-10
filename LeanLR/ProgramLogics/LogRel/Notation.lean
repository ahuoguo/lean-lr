import Iris.HeapLang.Notation

/-!
# Encoding the polymorphic constructs in heap_lang

`program_logics/logrel/notation.v`. heap_lang has no type abstraction, no packing and no
recursive-type folding, so the source language's constructs are encoded: a type abstraction is a
thunk and type application forces it, `pack` and `roll` are the identity, and `unroll` inserts the
one reduction step that makes it an *operation* rather than a coercion.
-/

open Iris.HeapLang

namespace ProgramLogics.LogRel

/-- Type application: force the thunk. -/
def tApp (e : Exp) : Exp := hl(&e #())

/-- Type abstraction, as a value. -/
def tLamV (e : Exp) : Val := hl_val(λ _, &e)

/-- Type abstraction. -/
def tLam (e : Exp) : Exp := hl(λ _, &e)

/-- Packing is erased. -/
def pack (e : Exp) : Exp := e

@[inherit_doc pack] def packV (v : Val) : Val := v

/-- `unpack e as x in e'`, encoded as a `let`. -/
def unpack (e : Exp) (x : Binder) (e' : Exp) : Exp := hl((λ &x, &e') &e)

/-- Folding a recursive type is erased. -/
def roll (e : Exp) : Exp := e

@[inherit_doc roll] def rollV (v : Val) : Val := v

/-- Unfolding takes one step, which is what the logical relation for `μ` needs in order to strip a
later. -/
def unroll (e : Exp) : Exp := hl(let x := &e; x)

end ProgramLogics.LogRel
