/-
  STLC notation for cleaner syntax
-/

import LeanLr.Lang
import Lean

namespace STLC

-- Coercions
instance : Coe String Expr where
  coe s := Expr.var s

instance : Coe Int Expr where
  coe n := Expr.litInt n

instance : Coe Int Val where
  coe n := Val.litIntV n

instance : CoeFun Expr (fun _ => Expr → Expr) where
  coe e := fun arg => Expr.app e arg

-- Basic notations
notation:75 "λ" x " . " e => Expr.lam (Binder.named x) e
infixl:65 " +ₑ " => Expr.plus

-- Multi-argument lambda: λ: x y z, e
syntax "λ:" ident ident* "," term : term

macro_rules
  | `(λ: $x:ident, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.lam (Binder.named $xStr) $e)
  | `(λ: $x:ident $y:ident $rest:ident*, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.lam (Binder.named $xStr) (λ: $y $rest*, $e))

-- Multi-argument value lambda: λᵥ: x y z, e
syntax "λᵥ:" ident ident* "," term : term

macro_rules
  | `(λᵥ: $x:ident, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Val.lamV (Binder.named $xStr) $e)
  | `(λᵥ: $x:ident $y:ident $rest:ident*, $e:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Val.lamV (Binder.named $xStr) (λ: $y $rest*, $e))

-- SKI combinators
def S : Val := λᵥ: f g x, (("f" : Expr) "x") (("g" : Expr) "x")
def K : Val := λᵥ: x y, "x"
def I : Val := λᵥ: x, "x"

-- Arithmetic
def add : Val := λᵥ: x y, "x" +ₑ "y"

-- Church numerals
def zero : Val := λᵥ: f x, "x"
def one : Val := λᵥ: f x, ("f" : Expr) "x"
def two : Val := λᵥ: f x, ("f" : Expr) (("f" : Expr) "x")

-- Combinators
def compose : Val := λᵥ: f g x, ("f" : Expr) (("g" : Expr) "x")
def apply : Val := λᵥ: f x, ("f" : Expr) "x"

-- Tests
example : (λ: x, "x").isValue = true := rfl
example : (λ: x y, ("x" : Expr) "y").isValue = true := rfl
example : ("x" : Expr) = Expr.var "x" := rfl
example : ((42 : Int) : Expr) = Expr.litInt 42 := rfl
example : (("f" : Expr) "x" : Expr) = Expr.app "f" "x" := rfl
example : ((1 : Int) +ₑ (2 : Int) : Expr) = Expr.plus (Expr.litInt 1) (Expr.litInt 2) := rfl
example : (λ: f x y, ("f" : Expr) ("x" +ₑ "y")).isValue = true := rfl

end STLC
