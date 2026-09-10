/-!
# Extended STLC: language definition

The simply typed λ-calculus of `TypeSystems.Stlc` extended with products and sums. Syntax, values,
substitution and closedness live here; the two operational semantics get their own files
(`BigStep` and `CtxStep`) so that they can be compared side by side.
-/

namespace StlcExtended

/-! ## Syntax -/

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

@[inherit_doc] notation:90 b " :b: " ss => Binder.cons b ss

inductive Expr where
  -- Base lambda calculus
  | var (x : String)
  | lam (x : Binder) (e : Expr)
  | app (e₁ e₂ : Expr)
  -- Base types and their operations
  | litInt (n : Int)
  | plus (e₁ e₂ : Expr)
  -- Products
  | pair (e₁ e₂ : Expr)
  | fst (e : Expr)
  | snd (e : Expr)
  -- Sums
  | injL (e : Expr)
  | injR (e : Expr)
  | case (e₀ e₁ e₂ : Expr)
  deriving Repr, DecidableEq

inductive Val where
  | litIntV (n : Int)
  | lamV (x : Binder) (e : Expr)
  | pairV (v₁ v₂ : Val)
  | injLV (v : Val)
  | injRV (v : Val)
  deriving Repr, DecidableEq

/-- Injects a value into the expressions. -/
def Val.toExpr : Val → Expr
  | .litIntV n => .litInt n
  | .lamV x e => .lam x e
  | .pairV v₁ v₂ => .pair v₁.toExpr v₂.toExpr
  | .injLV v => .injL v.toExpr
  | .injRV v => .injR v.toExpr

/-- Partial inverse of `Val.toExpr`: returns `some v` exactly when the expression is a value. -/
def Expr.toVal? : Expr → Option Val
  | .litInt n => some (.litIntV n)
  | .lam x e => some (.lamV x e)
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
  | .litInt _ => True
  | .lam _ _ => True
  | .pair e₁ e₂ => e₁.isVal ∧ e₂.isVal
  | .injL e => e.isVal
  | .injR e => e.isVal
  | _ => False

/-! ### Values and the two views of them -/

@[simp] theorem toVal?_toExpr : ∀ v : Val, v.toExpr.toVal? = some v
  | .litIntV _ | .lamV _ _ => rfl
  | .pairV v₁ v₂ => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v₁, toVal?_toExpr v₂]
  | .injLV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]
  | .injRV v => by simp [Val.toExpr, Expr.toVal?, toVal?_toExpr v]

theorem toVal?_eq {e : Expr} {v : Val} (h : e.toVal? = some v) : e = v.toExpr := by
  induction e generalizing v with
  | litInt _ | lam _ _ => cases h; rfl
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.toVal?] at h
    cases h₁ : e₁.toVal? with
    | none => rw [h₁] at h; simp at h
    | some v₁ =>
      cases h₂ : e₂.toVal? with
      | none => rw [h₁, h₂] at h; simp at h
      | some v₂ =>
        rw [h₁, h₂] at h
        injection h with heq
        subst heq
        simp [Val.toExpr, ih₁ h₁, ih₂ h₂]
  | injL e ih | injR e ih =>
    simp only [Expr.toVal?] at h
    cases h₁ : e.toVal? with
    | none => rw [h₁] at h; simp at h
    | some v₁ =>
      rw [h₁] at h
      injection h with heq
      subst heq
      simp [Val.toExpr, ih h₁]
  | _ => simp [Expr.toVal?] at h

@[simp] theorem val_isVal : ∀ v : Val, Expr.isVal v.toExpr
  | .litIntV _ | .lamV _ _ => trivial
  | .pairV v₁ v₂ => ⟨val_isVal v₁, val_isVal v₂⟩
  | .injLV v | .injRV v => val_isVal v

/-- Every value is in the image of `Val.toExpr`. -/
theorem isVal_exists {e : Expr} (h : e.isVal) : ∃ v : Val, e = v.toExpr := by
  induction e with
  | litInt n => exact ⟨.litIntV n, rfl⟩
  | lam x e => exact ⟨.lamV x e, rfl⟩
  | pair e₁ e₂ ih₁ ih₂ =>
    obtain ⟨v₁, rfl⟩ := ih₁ h.1
    obtain ⟨v₂, rfl⟩ := ih₂ h.2
    exact ⟨.pairV v₁ v₂, rfl⟩
  | injL e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.injLV v, rfl⟩
  | injR e ih => obtain ⟨v, rfl⟩ := ih h; exact ⟨.injRV v, rfl⟩
  | _ => exact h.elim

theorem isVal_toVal? {e : Expr} (h : e.isVal) : ∃ v, e.toVal? = some v := by
  obtain ⟨v, rfl⟩ := isVal_exists h
  exact ⟨v, toVal?_toExpr v⟩

theorem toVal?_isVal {e : Expr} {v : Val} (h : e.toVal? = some v) : e.isVal := by
  rw [toVal?_eq h]; exact val_isVal v

/-! ## Substitution -/

/-- `subst x es e` replaces every free occurrence of `x` in `e` by `es`. -/
def subst (x : String) (es : Expr) : Expr → Expr
  | .litInt n => .litInt n
  | .var y => if x = y then es else .var y
  | .lam y e => .lam y (if Binder.bNamed x = y then e else subst x es e)
  | .app e₁ e₂ => .app (subst x es e₁) (subst x es e₂)
  | .plus e₁ e₂ => .plus (subst x es e₁) (subst x es e₂)
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

@[inherit_doc] notation:90 e "[" x " := " es "]" => subst x es e

/-! ## Closedness -/

/-- `e.isClosed X` holds when every free variable of `e` occurs in `X`. -/
def Expr.isClosed (X : List String) : Expr → Bool
  | .var x => x ∈ X
  | .lam x e => e.isClosed (x :b: X)
  | .litInt _ => true
  | .app e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .plus e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .pair e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .fst e => e.isClosed X
  | .snd e => e.isClosed X
  | .injL e => e.isClosed X
  | .injR e => e.isClosed X
  | .case e₀ e₁ e₂ => e₀.isClosed X && e₁.isClosed X && e₂.isClosed X

/-- `Prop`-valued form of `Expr.isClosed`, for use as a hypothesis. -/
abbrev closed (X : List String) (e : Expr) : Prop := e.isClosed X = true

/-- Extending the variable list preserves inclusion under a binder. -/
theorem cons_subset {b : Binder} {X Y : List String}
    (hsub : ∀ x, x ∈ X → x ∈ Y) : ∀ x, x ∈ (b :b: X) → x ∈ (b :b: Y) := by
  cases b with
  | bAnon => exact hsub
  | bNamed y =>
    intro z hz
    cases hz with
    | head => exact .head _
    | tail _ hz' => exact .tail _ (hsub z hz')

/-- Closedness is monotone in the list of names in scope. -/
theorem closed_weaken {X Y : List String} {e : Expr}
    (h : closed X e) (hsub : ∀ x, x ∈ X → x ∈ Y) : closed Y e := by
  induction e generalizing X Y with
  | var x =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at h ⊢
    exact hsub x h
  | lam _ _ ih => exact ih h (cons_subset hsub)
  | litInt _ => rfl
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at h ⊢
    exact ⟨ih₁ h.1 hsub, ih₂ h.2 hsub⟩
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih => exact ih h hsub
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ih₀ h.1.1 hsub, ih₁ h.1.2 hsub⟩, ih₂ h.2 hsub⟩

theorem closed_weaken_nil {X : List String} {e : Expr} (h : closed [] e) : closed X e :=
  closed_weaken h (by simp)

/-- Substituting for a name that is not free changes nothing. -/
theorem subst_closed_notmem {X : List String} {e : Expr} {x : String} {es : Expr}
    (h : closed X e) (hx : x ∉ X) : subst x es e = e := by
  induction e generalizing X with
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq] at h
    simp only [subst, ite_eq_right_iff]
    rintro rfl; exact (hx h).elim
  | lam b e ih =>
    cases b with
    | bAnon =>
      simp only [subst, if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))]
      exact congrArg _ (ih h hx)
    | bNamed y =>
      simp only [subst]
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg (by simp [hxy])]
        refine congrArg _ (ih h fun hc => ?_)
        simp only [Binder.cons, List.mem_cons] at hc
        exact hc.elim (fun he => hxy he) hx
  | litInt _ => rfl
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at h
    simp only [subst, ih₁ h.1 hx, ih₂ h.2 hx]
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih => simp only [subst, ih h hx]
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, Expr.isClosed, Bool.and_eq_true] at h
    simp only [subst, ih₀ h.1.1 hx, ih₁ h.1.2 hx, ih₂ h.2 hx]

theorem subst_closed_nil {e : Expr} {x : String} {es : Expr} (h : closed [] e) :
    subst x es e = e :=
  subst_closed_notmem h (by simp)

theorem subst'_closed_nil {e : Expr} {b : Binder} {es : Expr} (h : closed [] e) :
    subst' b es e = e := by
  cases b with
  | bAnon => rfl
  | bNamed x => exact subst_closed_nil h

/-- Substituting a closed term removes the substituted name from the free ones. -/
theorem closed_subst_nil {X : List String} {e es : Expr} {x : String}
    (hes : closed [] es) (he : closed (x :: X) e) : closed X (subst x es e) := by
  induction e generalizing X with
  | var y =>
    simp only [closed, Expr.isClosed, decide_eq_true_eq, List.mem_cons] at he
    simp only [subst]
    by_cases hxy : x = y
    · rw [if_pos hxy]; exact closed_weaken_nil hes
    · rw [if_neg hxy]
      simpa [closed, Expr.isClosed] using he.resolve_left (Ne.symm hxy)
  | lam b e ih =>
    cases b with
    | bAnon =>
      simp only [subst, closed, Expr.isClosed, Binder.cons,
        if_neg (by simp : ¬ (Binder.bNamed x = Binder.bAnon))] at he ⊢
      exact ih he
    | bNamed y =>
      simp only [subst, closed, Expr.isClosed, Binder.cons] at he ⊢
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl]
        refine closed_weaken he fun z hz => ?_
        simp only [List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact hz
      · rw [if_neg (by simp [hxy])]
        refine ih (closed_weaken he fun z hz => ?_)
        simp only [List.mem_cons] at hz ⊢
        rcases hz with hz | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz)
  | litInt _ => rfl
  | app _ _ ih₁ ih₂ | plus _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closed, subst, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih₁ he.1, ih₂ he.2⟩
  | fst _ ih | snd _ ih | injL _ ih | injR _ ih => exact ih he
  | case _ _ _ ih₀ ih₁ ih₂ =>
    simp only [closed, subst, Expr.isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih₀ he.1.1, ih₁ he.1.2⟩, ih₂ he.2⟩

theorem closed_do_subst' {X : List String} {e es : Expr} {b : Binder}
    (hes : closed [] es) (he : closed (b :b: X) e) : closed X (subst' b es e) := by
  cases b with
  | bAnon => exact he
  | bNamed x => exact closed_subst_nil hes he

end StlcExtended
