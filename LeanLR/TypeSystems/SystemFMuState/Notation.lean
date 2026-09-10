import LeanLR.TypeSystems.SystemFMuState.Lang
import Lean

/-!
# System F with recursive types and mutable state: notation

The surface syntax of `systemf_mu_state/notation.v`. Rocq's coercions and notation scopes become
Lean `Coe`/`CoeFun` instances and macros; the derived forms Rocq introduces as `only parsing`
notations (`Let`, `Seq`, `Match`, `assert`, `Or`, `And`) become plain definitions, since Lean has
no notion of a parsing-only notation and a definition is what a reader wants anyway.
-/

namespace SystemFMuState

/-! ## Coercions -/

instance : Coe String Expr where coe s := .var s
instance : Coe Int BaseLit where coe n := .litInt n
instance : Coe Bool BaseLit where coe b := .litBool b
instance : Coe Loc BaseLit where coe l := .litLoc l
instance : Coe BaseLit Expr where coe l := .lit l
instance : Coe BaseLit Val where coe l := .litV l
instance : Coe Val Expr where coe v := v.toExpr

instance : CoeFun Expr (fun _ => Expr → Expr) where coe e := fun arg => .app e arg

/-! ## Operators -/

/-- Addition. -/
infixl:65 " +ₑ " => Expr.binOp BinOp.plusOp
/-- Subtraction. -/
infixl:65 " -ₑ " => Expr.binOp BinOp.minusOp
/-- Multiplication. -/
infixl:70 " *ₑ " => Expr.binOp BinOp.multOp
/-- Less than. -/
infix:50 " <ₑ " => Expr.binOp BinOp.ltOp
/-- Less than or equal. -/
infix:50 " ≤ₑ " => Expr.binOp BinOp.leOp
/-- Equality test. -/
infix:50 " =ₑ " => Expr.binOp BinOp.eqOp
/-- Boolean negation. -/
prefix:75 "¬ₑ" => Expr.unOp UnOp.negOp
/-- Arithmetic negation. -/
prefix:75 "-ₑ" => Expr.unOp UnOp.minusUnOp

/-! ## Binders and derived forms -/

/-- Multi-argument λ over expressions: `λ: x y z, e`. -/
syntax "λ:" ident ident* "," term : term

macro_rules
  | `(λ: $x:ident, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.lam (Binder.bNamed $xStr) $e)
  | `(λ: $x:ident $y:ident $rest:ident*, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.lam (Binder.bNamed $xStr) (λ: $y $rest*, $e))

/-- Multi-argument λ producing a value: `λᵥ: x y z, e`. -/
syntax "λᵥ:" ident ident* "," term : term

macro_rules
  | `(λᵥ: $x:ident, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Val.lamV (Binder.bNamed $xStr) $e)
  | `(λᵥ: $x:ident $y:ident $rest:ident*, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Val.lamV (Binder.bNamed $xStr) (λ: $y $rest*, $e))

/-- `let: x := e₁ in e₂`, -/
syntax "let:" ident " := " term " in " term : term

macro_rules
  | `(let: $x:ident := $e₁:term in $e₂:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.app (Expr.lam (Binder.bNamed $xStr) $e₂) $e₁)

/-- Sequencing: run `e₁` for its effect, then `e₂`. -/
def seqE (e₁ e₂ : Expr) : Expr := .app (.lam .bAnon e₂) e₁

@[inherit_doc] infixr:60 " ;;ₑ " => seqE

/-- Case analysis binding the payload in each branch. -/
def matchE (e₀ : Expr) (x₁ : Binder) (e₁ : Expr) (x₂ : Binder) (e₂ : Expr) : Expr :=
  .case e₀ (.lam x₁ e₁) (.lam x₂ e₂)

/-- Conditional. -/
abbrev ifE (e₀ e₁ e₂ : Expr) : Expr := .ite e₀ e₁ e₂

/-! ## Polymorphism, existentials, recursive types and state -/

/-- Type abstraction. -/
prefix:max "Λₑ" => Expr.tLam
/-- Type abstraction, as a value. -/
prefix:max "Λᵥ" => Val.tLamV
/-- Type application. -/
postfix:max "<>" => Expr.tApp
/-- Existential packing. -/
prefix:max "packₑ" => Expr.pack
/-- Existential packing, as a value. -/
prefix:max "packᵥ" => Val.packV
/-- Existential unpacking. -/
abbrev unpackE (x : Binder) (e₁ e₂ : Expr) : Expr := .unpack x e₁ e₂
/-- Folding a recursive type. -/
prefix:max "rollₑ" => Expr.roll
/-- Folding a recursive type, as a value. -/
prefix:max "rollᵥ" => Val.rollV
/-- Unfolding a recursive type. -/
prefix:max "unrollₑ" => Expr.unroll
/-- Dereferencing. -/
prefix:9 "!ₑ" => Expr.load
/-- Allocation. -/
prefix:10 "newₑ" => Expr.new
/-- Assignment. -/
infix:80 " <-ₑ " => Expr.store

/-! ## Assertions and short-circuiting booleans -/

/-- `assert e` diverges — in fact gets stuck — when `e` is false. -/
def assert (e : Expr) : Expr :=
  .ite e (.lit .litUnit) (.app (.lit (.litInt 0)) (.lit (.litInt 0)))

/-- Short-circuiting disjunction. -/
def Or (e₁ e₂ : Expr) : Expr := .ite e₁ (.lit (.litBool true)) e₂

/-- Short-circuiting conjunction. -/
def And (e₁ e₂ : Expr) : Expr := .ite e₁ e₂ (.lit (.litBool false))

@[inherit_doc] infixr:30 " ||ₑ " => Or
@[inherit_doc] infixr:35 " &&ₑ " => And

/-! ## Sanity checks -/

example : (λ: x, "x") = Expr.lam (.bNamed "x") (.var "x") := rfl
example : (λ: x y, ("x" : Expr) "y")
    = Expr.lam (.bNamed "x") (Expr.lam (.bNamed "y") (.app (.var "x") (.var "y"))) := rfl
example : (let: x := (Expr.lit (.litInt 1)) in "x")
    = Expr.app (Expr.lam (.bNamed "x") (.var "x")) (.lit (.litInt 1)) := rfl
example : (Expr.lit (.litInt 1) +ₑ Expr.lit (.litInt 2))
    = Expr.binOp .plusOp (.lit (.litInt 1)) (.lit (.litInt 2)) := rfl
example : (Λₑ (Expr.lit (.litInt 4)))<> = Expr.tApp (.tLam (.lit (.litInt 4))) := rfl
example : (!ₑ (Expr.lit (.litLoc ⟨0⟩))) = Expr.load (.lit (.litLoc ⟨0⟩)) := rfl
example : (Expr.lit (.litLoc ⟨0⟩) <-ₑ Expr.lit (.litInt 1))
    = Expr.store (.lit (.litLoc ⟨0⟩)) (.lit (.litInt 1)) := rfl
example : Expr.isVal (Expr.pair (.lit (.litInt 1)) (.injL (.lit (.litInt 2)))) :=
  ⟨trivial, trivial⟩

end SystemFMuState
