/-!
# System F: language definition

Syntax, values, substitution, evaluation contexts, and the contextual operational semantics.

This is `SystemFMu.Lang` without recursive types: no `roll`/`unroll` and no `rollV`.
-/

namespace SystemF

/-! ## Syntax -/

inductive BaseLit where
  | litInt (n : Int)
  | litBool (b : Bool)
  | litUnit
  deriving Repr, DecidableEq

inductive UnOp where
  | negOp
  | minusUnOp
  deriving Repr, DecidableEq

inductive BinOp where
  | plusOp | minusOp | multOp
  | ltOp | leOp | eqOp
  deriving Repr, DecidableEq

/-- A binder is either a name or anonymous; an anonymous binder discards its argument. -/
inductive Binder where
  | bNamed (s : String)
  | bAnon
  deriving Repr, DecidableEq

/-- Adds a binder to a list of names, dropping the anonymous binder. -/
def Binder.cons (b : Binder) (ss : List String) : List String :=
  match b with
  | .bAnon => ss
  | .bNamed s => s :: ss

@[inherit_doc] notation :90 b " :b: " ss => Binder.cons b ss

/-- Expressions. Type abstraction and existential packing are erased: `tLam`, `tApp`, `pack`
and `roll` carry no type annotation, and `unpack` binds only a term variable. -/
inductive Expr where
  | lit (l : BaseLit)
  | var (x : String)
  | lam (x : Binder) (e : Expr)
  | app (e₁ e₂ : Expr)
  | unOp (op : UnOp) (e : Expr)
  | binOp (op : BinOp) (e₁ e₂ : Expr)
  | ite (e₀ e₁ e₂ : Expr)
  -- Polymorphism
  | tApp (e : Expr)
  | tLam (e : Expr)
  | pack (e : Expr)
  | unpack (x : Binder) (e₁ e₂ : Expr)
  -- Products
  | pair (e₁ e₂ : Expr)
  | fst (e : Expr)
  | snd (e : Expr)
  -- Sums
  | injL (e : Expr)
  | injR (e : Expr)
  | case (e₀ e₁ e₂ : Expr)
  deriving Repr

inductive Val where
  | litV (l : BaseLit)
  | lamV (x : Binder) (e : Expr)
  | tLamV (e : Expr)
  | packV (v : Val)
  | pairV (v₁ v₂ : Val)
  | injLV (v : Val)
  | injRV (v : Val)
  deriving Repr

/-- Injects a value into the expressions. -/
def Val.toExpr : Val → Expr
  | .litV l => .lit l
  | .lamV x e => .lam x e
  | .tLamV e => .tLam e
  | .packV v => .pack v.toExpr
  | .pairV v₁ v₂ => .pair v₁.toExpr v₂.toExpr
  | .injLV v => .injL v.toExpr
  | .injRV v => .injR v.toExpr

/-- Partial inverse of `Val.toExpr`: returns `some v` exactly when the expression is a value. -/
def Expr.toVal? : Expr → Option Val
  | .lit l => some (.litV l)
  | .lam x e => some (.lamV x e)
  | .tLam e => some (.tLamV e)
  | .pack e => e.toVal?.map Val.packV
  | .pair e₁ e₂ => do
    let v₁ ← e₁.toVal?
    let v₂ ← e₂.toVal?
    return .pairV v₁ v₂
  | .injL e => e.toVal?.map Val.injLV
  | .injR e => e.toVal?.map Val.injRV
  | _ => none

/-- `e.isVal` holds exactly when `e` is in the image of `Val.toExpr`. Stated as a `Prop` rather
than via `Expr.toVal?` so that the reduction rules can be destructed structurally. -/
def Expr.isVal : Expr → Prop
  | .lit _ => True
  | .lam _ _ => True
  | .tLam _ => True
  | .pack e => e.isVal
  | .pair e₁ e₂ => e₁.isVal ∧ e₂.isVal
  | .injL e => e.isVal
  | .injR e => e.isVal
  | _ => False

/-! ## Substitution -/

/-- `subst x es e` replaces every free occurrence of the term variable `x` in `e` by `es`. -/
def subst (x : String) (es : Expr) : Expr → Expr
  | .lit l => .lit l
  | .var y => if x = y then es else .var y
  | .lam y e =>
    .lam y (if Binder.bNamed x = y then e else subst x es e)
  | .app e₁ e₂ => .app (subst x es e₁) (subst x es e₂)
  | .unOp op e => .unOp op (subst x es e)
  | .binOp op e₁ e₂ => .binOp op (subst x es e₁) (subst x es e₂)
  | .ite e₀ e₁ e₂ => .ite (subst x es e₀) (subst x es e₁) (subst x es e₂)
  | .tApp e => .tApp (subst x es e)
  | .tLam e => .tLam (subst x es e)
  | .pack e => .pack (subst x es e)
  | .unpack y e₁ e₂ =>
    .unpack y (subst x es e₁) (if Binder.bNamed x = y then e₂ else subst x es e₂)
  | .pair e₁ e₂ => .pair (subst x es e₁) (subst x es e₂)
  | .fst e => .fst (subst x es e)
  | .snd e => .snd (subst x es e)
  | .injL e => .injL (subst x es e)
  | .injR e => .injR (subst x es e)
  | .case e₀ e₁ e₂ => .case (subst x es e₀) (subst x es e₁) (subst x es e₂)

/-- Substitution for a binder; the anonymous binder substitutes nothing. -/
def subst' (b : Binder) (es : Expr) : Expr → Expr :=
  match b with
  | .bNamed x => subst x es
  | .bAnon => id

/-! ## Operational semantics -/

/-- Evaluates a unary operator, failing on ill-typed operands. -/
def unOpEval (op : UnOp) (v : Val) : Option Val :=
  match op, v with
  | .negOp, .litV (.litBool b) => some (.litV (.litBool (!b)))
  | .minusUnOp, .litV (.litInt n) => some (.litV (.litInt (-n)))
  | _, _ => none

/-- Evaluates a binary operator, failing on ill-typed operands. -/
def binOpEval (op : BinOp) (v₁ v₂ : Val) : Option Val :=
  match op, v₁, v₂ with
  | .plusOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litInt (n₁ + n₂)))
  | .minusOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litInt (n₁ - n₂)))
  | .multOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litInt (n₁ * n₂)))
  | .ltOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litBool (n₁ < n₂)))
  | .leOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litBool (n₁ ≤ n₂)))
  | .eqOp, .litV (.litInt n₁), .litV (.litInt n₂) => some (.litV (.litBool (n₁ = n₂)))
  | _, _, _ => none

/-- A single evaluation-context frame. Binary constructs evaluate right to left: the left frame
holds an already-evaluated `Val` and the right frame a not-yet-evaluated `Expr`. -/
inductive EctxItem where
  | appLCtx (v : Val)
  | appRCtx (e : Expr)
  | unOpCtx (op : UnOp)
  | binOpLCtx (op : BinOp) (v : Val)
  | binOpRCtx (op : BinOp) (e : Expr)
  | ifCtx (e₁ e₂ : Expr)
  | tAppCtx
  | packCtx
  | unpackCtx (x : Binder) (e₂ : Expr)
  | pairLCtx (v : Val)
  | pairRCtx (e : Expr)
  | fstCtx
  | sndCtx
  | injLCtx
  | injRCtx
  | caseCtx (e₁ e₂ : Expr)

/-- An evaluation context, innermost frame first. -/
abbrev Ectx := List EctxItem

/-- Plugs an expression into a single frame. -/
def fillItem (Ki : EctxItem) (e : Expr) : Expr :=
  match Ki with
  | .appLCtx v => .app e v.toExpr
  | .appRCtx e₁ => .app e₁ e
  | .unOpCtx op => .unOp op e
  | .binOpLCtx op v => .binOp op e v.toExpr
  | .binOpRCtx op e₁ => .binOp op e₁ e
  | .ifCtx e₁ e₂ => .ite e e₁ e₂
  | .tAppCtx => .tApp e
  | .packCtx => .pack e
  | .unpackCtx x e₂ => .unpack x e e₂
  | .pairLCtx v => .pair e v.toExpr
  | .pairRCtx e₁ => .pair e₁ e
  | .fstCtx => .fst e
  | .sndCtx => .snd e
  | .injLCtx => .injL e
  | .injRCtx => .injR e
  | .caseCtx e₁ e₂ => .case e e₁ e₂

/-- Plugs an expression into a context, applying the frames from the inside out. -/
def fill (K : Ectx) (e : Expr) : Expr :=
  K.foldl (fun acc ki => fillItem ki acc) e

/-- A single reduction of a redex. -/
inductive BaseStep : Expr → Expr → Prop where
  | betaS x e₁ e₂ :
      Expr.isVal e₂ →
      BaseStep (.app (.lam x e₁) e₂) (subst' x e₂ e₁)
  | tBetaS e :
      BaseStep (.tApp (.tLam e)) e
  | unpackS x e₁ e₂ :
      Expr.isVal e₁ →
      BaseStep (.unpack x (.pack e₁) e₂) (subst' x e₁ e₂)
  | unOpS op e v v' :
      Expr.toVal? e = some v →
      unOpEval op v = some v' →
      BaseStep (.unOp op e) v'.toExpr
  | binOpS op e₁ e₂ v₁ v₂ v' :
      Expr.toVal? e₁ = some v₁ →
      Expr.toVal? e₂ = some v₂ →
      binOpEval op v₁ v₂ = some v' →
      BaseStep (.binOp op e₁ e₂) v'.toExpr
  | ifTrueS e₁ e₂ :
      BaseStep (.ite (.lit (.litBool true)) e₁ e₂) e₁
  | ifFalseS e₁ e₂ :
      BaseStep (.ite (.lit (.litBool false)) e₁ e₂) e₂
  | fstS e₁ e₂ :
      Expr.isVal e₁ → Expr.isVal e₂ →
      BaseStep (.fst (.pair e₁ e₂)) e₁
  | sndS e₁ e₂ :
      Expr.isVal e₁ → Expr.isVal e₂ →
      BaseStep (.snd (.pair e₁ e₂)) e₂
  | caseLS e e₁ e₂ :
      Expr.isVal e →
      BaseStep (.case (.injL e) e₁ e₂) (.app e₁ e)
  | caseRS e e₁ e₂ :
      Expr.isVal e →
      BaseStep (.case (.injR e) e₁ e₂) (.app e₂ e)

/-- A reduction step of a whole program: a `BaseStep` under an evaluation context. -/
inductive ContextualStep : Expr → Expr → Prop where
  | ectxStep (K : Ectx) (e₁ e₂ : Expr) :
      BaseStep e₁ e₂ →
      ContextualStep (fill K e₁) (fill K e₂)

def reducible (e : Expr) : Prop := ∃ e', ContextualStep e e'

def irreducible (e : Expr) : Prop := ¬ reducible e

/-- The reflexive-transitive closure of `ContextualStep`. -/
inductive ContextualSteps : Expr → Expr → Prop where
  | refl {e} : ContextualSteps e e
  | step {e₁ e₂ e₃} : ContextualStep e₁ e₂ → ContextualSteps e₂ e₃ → ContextualSteps e₁ e₃

theorem ContextualSteps.trans {e₁ e₂ e₃ : Expr}
    (h₁ : ContextualSteps e₁ e₂) (h₂ : ContextualSteps e₂ e₃) : ContextualSteps e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem ContextualSteps.single {e₁ e₂ : Expr} (h : ContextualStep e₁ e₂) :
    ContextualSteps e₁ e₂ := .step h .refl

/-! ## Closedness -/

/-- `e.isClosed X` holds when every free term variable of `e` occurs in `X`. -/
def Expr.isClosed (X : List String) : Expr → Bool
  | .lit _ => true
  | .var x => x ∈ X
  | .lam x e => e.isClosed (x :b: X)
  | .app e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .unOp _ e => e.isClosed X
  | .binOp _ e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .ite e₀ e₁ e₂ => e₀.isClosed X && e₁.isClosed X && e₂.isClosed X
  | .tApp e => e.isClosed X
  | .tLam e => e.isClosed X
  | .pack e => e.isClosed X
  | .unpack x e₁ e₂ => e₁.isClosed X && e₂.isClosed (x :b: X)
  | .pair e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .fst e => e.isClosed X
  | .snd e => e.isClosed X
  | .injL e => e.isClosed X
  | .injR e => e.isClosed X
  | .case e₀ e₁ e₂ => e₀.isClosed X && e₁.isClosed X && e₂.isClosed X

/-- `Prop`-valued form of `Expr.isClosed`, for use as a hypothesis. -/
abbrev closed (X : List String) (e : Expr) : Prop := e.isClosed X = true

end SystemF
