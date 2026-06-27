/-
  System F with recursive types and mutable state - Language Definition
  Defines syntax, values, substitution, and operational semantics.
  Ported from semantics-2025/theories/type_systems/systemf_mu_state/lang.v
-/

namespace SystemFMuState

-- Locations (heap addresses)
structure Loc where
  loc : Int
  deriving Repr, DecidableEq, Hashable

instance : Inhabited Loc := ⟨⟨0⟩⟩

def Loc.add (l : Loc) (off : Int) : Loc := ⟨l.loc + off⟩
instance : HAdd Loc Int Loc := ⟨Loc.add⟩

-- Base literals
inductive BaseLit where
  | litInt (n : Int)
  | litBool (b : Bool)
  | litUnit
  | litLoc (l : Loc)
  deriving Repr, DecidableEq

-- Unary operators
inductive UnOp where
  | negOp
  | minusUnOp
  deriving Repr, DecidableEq

-- Binary operators
inductive BinOp where
  | plusOp | minusOp | multOp
  | ltOp | leOp | eqOp
  deriving Repr, DecidableEq

-- Binders (like stdpp binder)
inductive Binder where
  | bNamed : String → Binder
  | bAnon : Binder
  deriving Repr, DecidableEq

def Binder.cons (b : Binder) (ss : List String) : List String :=
  match b with
  | Binder.bAnon => ss
  | Binder.bNamed s => s :: ss

notation :90 b " :b: " ss => Binder.cons b ss

-- Expressions
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
  -- Isorecursive types
  | roll (e : Expr)
  | unroll (e : Expr)
  -- Mutable state
  | load (e : Expr)
  | store (e₁ e₂ : Expr)
  | new (e : Expr)
  deriving Repr

-- Values
inductive Val where
  | litV (l : BaseLit)
  | lamV (x : Binder) (e : Expr)
  | tLamV (e : Expr)
  | packV (v : Val)
  | pairV (v₁ v₂ : Val)
  | injLV (v : Val)
  | injRV (v : Val)
  | rollV (v : Val)
  deriving Repr

-- Convert value to expression
def Val.toExpr : Val → Expr
  | .litV l => .lit l
  | .lamV x e => .lam x e
  | .tLamV e => .tLam e
  | .packV v => .pack v.toExpr
  | .pairV v₁ v₂ => .pair v₁.toExpr v₂.toExpr
  | .injLV v => .injL v.toExpr
  | .injRV v => .injR v.toExpr
  | .rollV v => .roll v.toExpr

-- Try to convert expression to value
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
  | .roll e => e.toVal?.map Val.rollV
  | _ => none

-- Check if expression is a value
def Expr.isVal : Expr → Prop
  | .lit _ => True
  | .lam _ _ => True
  | .tLam _ => True
  | .pack e => e.isVal
  | .pair e₁ e₂ => e₁.isVal ∧ e₂.isVal
  | .injL e => e.isVal
  | .injR e => e.isVal
  | .roll e => e.isVal
  | _ => False

-- Substitution
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
  | .roll e => .roll (subst x es e)
  | .unroll e => .unroll (subst x es e)
  | .load e => .load (subst x es e)
  | .store e₁ e₂ => .store (subst x es e₁) (subst x es e₂)
  | .new e => .new (subst x es e)

def subst' (b : Binder) (es : Expr) : Expr → Expr :=
  match b with
  | .bNamed x => subst x es
  | .bAnon => id

-- Heaps
abbrev Heap := Loc → Option Val

def Heap.empty : Heap := fun _ => none

-- Unary operator evaluation
def unOpEval (op : UnOp) (v : Val) : Option Val :=
  match op, v with
  | .negOp, .litV (.litBool b) => some (.litV (.litBool (!b)))
  | .minusUnOp, .litV (.litInt n) => some (.litV (.litInt (-n)))
  | _, _ => none

-- Binary operator evaluation
def binOpEval (op : BinOp) (v₁ v₂ : Val) : Option Val :=
  match op, v₁, v₂ with
  | .plusOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litInt (n₁ + n₂)))
  | .minusOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litInt (n₁ - n₂)))
  | .multOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litInt (n₁ * n₂)))
  | .ltOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litBool (n₁ < n₂)))
  | .leOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litBool (n₁ ≤ n₂)))
  | .eqOp, .litV (.litInt n₁), .litV (.litInt n₂) =>
    some (.litV (.litBool (n₁ = n₂)))
  | _, _, _ => none

-- Evaluation contexts (right-to-left evaluation)
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
  | rollCtx
  | unrollCtx
  | loadCtx
  | storeLCtx (v : Val)
  | storeRCtx (e : Expr)
  | newCtx

abbrev Ectx := List EctxItem

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
  | .rollCtx => .roll e
  | .unrollCtx => .unroll e
  | .loadCtx => .load e
  | .storeLCtx v => .store e v.toExpr
  | .storeRCtx e₁ => .store e₁ e
  | .newCtx => .new e

def fill (K : Ectx) (e : Expr) : Expr :=
  K.foldl (fun acc ki => fillItem ki acc) e

-- Base reduction (single step, with heap)
inductive BaseStep : Expr × Heap → Expr × Heap → Prop where
  | betaS x e₁ e₂ h :
      Expr.isVal e₂ →
      BaseStep (.app (.lam x e₁) e₂, h) (subst' x e₂ e₁, h)
  | tBetaS e h :
      BaseStep (.tApp (.tLam e), h) (e, h)
  | unpackS x e₁ e₂ h :
      Expr.isVal e₁ →
      BaseStep (.unpack x (.pack e₁) e₂, h) (subst' x e₁ e₂, h)
  | unOpS op e v v' h :
      Expr.toVal? e = some v →
      unOpEval op v = some v' →
      BaseStep (.unOp op e, h) (v'.toExpr, h)
  | binOpS op e₁ e₂ v₁ v₂ v' h :
      Expr.toVal? e₁ = some v₁ →
      Expr.toVal? e₂ = some v₂ →
      binOpEval op v₁ v₂ = some v' →
      BaseStep (.binOp op e₁ e₂, h) (v'.toExpr, h)
  | ifTrueS e₁ e₂ h :
      BaseStep (.ite (.lit (.litBool true)) e₁ e₂, h) (e₁, h)
  | ifFalseS e₁ e₂ h :
      BaseStep (.ite (.lit (.litBool false)) e₁ e₂, h) (e₂, h)
  | fstS e₁ e₂ h :
      Expr.isVal e₁ → Expr.isVal e₂ →
      BaseStep (.fst (.pair e₁ e₂), h) (e₁, h)
  | sndS e₁ e₂ h :
      Expr.isVal e₁ → Expr.isVal e₂ →
      BaseStep (.snd (.pair e₁ e₂), h) (e₂, h)
  | caseLΞ e e₁ e₂ h :
      Expr.isVal e →
      BaseStep (.case (.injL e) e₁ e₂, h) (.app e₁ e, h)
  | caseRS e e₁ e₂ h :
      Expr.isVal e →
      BaseStep (.case (.injR e) e₁ e₂, h) (.app e₂ e, h)
  | unrollS e h :
      Expr.isVal e →
      BaseStep (.unroll (.roll e), h) (e, h)
  | newS e v l h :
      Expr.toVal? e = some v →
      h l = none →
      BaseStep (.new e, h) (.lit (.litLoc l), fun l' => if l' = l then some v else h l')
  | loadS l v h :
      h l = some v →
      BaseStep (.load (.lit (.litLoc l)), h) (v.toExpr, h)
  | storeS l v e₂ h :
      h l ≠ none →
      Expr.toVal? e₂ = some v →
      BaseStep (.store (.lit (.litLoc l)) e₂, h) (.lit .litUnit, fun l' => if l' = l then some v else h l')

-- Contextual step
inductive ContextualStep : Expr × Heap → Expr × Heap → Prop where
  | ectxStep (K : Ectx) (e₁ e₂ : Expr) (h₁ h₂ : Heap) :
      BaseStep (e₁, h₁) (e₂, h₂) →
      ContextualStep (fill K e₁, h₁) (fill K e₂, h₂)

def reducible (e : Expr) (h : Heap) : Prop :=
  ∃ e' h', ContextualStep (e, h) (e', h')

def irreducible (e : Expr) (h : Heap) : Prop :=
  ¬ reducible e h

-- Closedness
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
  | .roll e => e.isClosed X
  | .unroll e => e.isClosed X
  | .load e => e.isClosed X
  | .store e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .new e => e.isClosed X

abbrev closed (X : List String) (e : Expr) : Prop := e.isClosed X = true

end SystemFMuState
