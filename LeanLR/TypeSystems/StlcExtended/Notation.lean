import LeanLR.TypeSystems.StlcExtended.Lang
import Lean

/-!
# Extended STLC: notation

Lean macros for the surface syntax the Rocq development provides through notation scopes:
multi-argument λ, `let:`, sequencing, and `match:` on sums. Rocq's `%E`/`%V` scopes have no
counterpart; the coercions below play their role.
-/

namespace StlcExtended

/-! ## Coercions -/

instance : Coe String Expr where coe s := .var s
instance : Coe Int Expr where coe n := .litInt n
instance : Coe Int Val where coe n := .litIntV n
instance : Coe Val Expr where coe v := v.toExpr

instance : CoeFun Expr (fun _ => Expr → Expr) where coe e := fun arg => .app e arg

/-! ## Terms -/

/-- Addition on expressions. -/
infixl:65 " +ₑ " => Expr.plus

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

/-- `let: x := e₁ in e₂` is sugar for `(λ x. e₂) e₁`. -/
syntax "let:" ident " := " term " in " term : term

macro_rules
  | `(let: $x:ident := $e₁:term in $e₂:term) => do
      let xStr := Lean.Syntax.mkStrLit (toString x.getId)
      `(Expr.app (Expr.lam (Binder.bNamed $xStr) $e₂) $e₁)

/-- Sequencing: run `e₁` for its (absent) effect, then `e₂`. -/
def seqE (e₁ e₂ : Expr) : Expr := .app (.lam .bAnon e₂) e₁

@[inherit_doc] infixr:60 " ;;ₑ " => seqE

/-- Case analysis binding the payload in each branch. -/
def matchE (e₀ : Expr) (x₁ : String) (e₁ : Expr) (x₂ : String) (e₂ : Expr) : Expr :=
  .case e₀ (.lam (.bNamed x₁) e₁) (.lam (.bNamed x₂) e₂)

/-! ## Sanity checks -/

example : (λ: x, "x") = Expr.lam (.bNamed "x") (.var "x") := rfl
example : (λ: x y, ("x" : Expr) "y")
    = Expr.lam (.bNamed "x") (Expr.lam (.bNamed "y") (.app (.var "x") (.var "y"))) := rfl
example : (let: x := ((1 : Int) : Expr) in "x")
    = Expr.app (Expr.lam (.bNamed "x") (.var "x")) (.litInt 1) := rfl
example : (((1 : Int) : Expr) +ₑ ((2 : Int) : Expr)) = Expr.plus (.litInt 1) (.litInt 2) := rfl
example : matchE (Expr.injL (.litInt 1)) "a" (.var "a") "b" (.var "b")
    = Expr.case (.injL (.litInt 1)) (Expr.lam (.bNamed "a") (.var "a"))
        (Expr.lam (.bNamed "b") (.var "b")) := rfl
example : (Expr.litInt 1 ;;ₑ Expr.litInt 2)
    = Expr.app (Expr.lam .bAnon (.litInt 2)) (.litInt 1) := rfl
example : Expr.isVal (Expr.pair (.litInt 1) (.injL (.litInt 2))) := ⟨trivial, trivial⟩

end StlcExtended
