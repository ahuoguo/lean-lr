import LeanLR.TypeSystems.SystemF.Tactics
import LeanLR.TypeSystems.SystemF.LogRel
import LeanLR.TypeSystems.SystemF.BinaryLogRel
import LeanLR.TypeSystems.SystemF.ExistentialInvariants

/-!
# System F, exercise sheet 4

`systemf/exercises04_sol.v`. An abstract type of integer sets behind an existential; an
instrumented implementation of "the even numbers" whose safety comes from the logical relation;
an abstract sum type; and a contextual equivalence between the abstract sum type and the
primitive one.
-/

open Iris.Std

namespace SystemF

/-! ## Exercise 1 (LN 23): existential fun

Records are encoded as nested pairs, associating to the left. The language has no recursion, so
the section assumes a fixpoint combinator and its typing rule. -/

section Existential

variable (Fix : String → String → Expr → Val)
variable (fix_typing : ∀ (n : Nat) (Γ : TypingContext) (f x : String) (A B : Ty) (e : Expr),
  TypeWf n A → TypeWf n B → f ≠ x →
  SynTyped n (insert (M := TyMapStr) (insert (M := TyMapStr) Γ f (.fn A B)) x A) e B →
  SynTyped n Γ (Fix f x e).toExpr (.fn A B))

/-- `∃ α. α × (Int → α) × (α → α → α) × (α → α → Bool)`: empty, singleton, union, subset. -/
def ISET : Ty :=
  .exist (.prod (.prod (.prod (.tVar 0) (.fn .int (.tVar 0)))
    (.fn (.tVar 0) (.fn (.tVar 0) (.tVar 0)))) (.fn (.tVar 0) (.fn (.tVar 0) .bool)))

/-- The representation: a membership test together with the least and greatest element. -/
def setRep : Ty := .prod (.prod (.fn .int .bool) .int) .int

def mini : Val :=
  λᵥ: x y, Expr.ite (.binOp .ltOp (.var "x") (.var "y")) (.var "x") (.var "y")

/-- Rocq's `maxi` is a copy of `mini`; the port keeps it as it is. -/
def maxi : Val :=
  λᵥ: x y, Expr.ite (.binOp .ltOp (.var "x") (.var "y")) (.var "x") (.var "y")

def iterupiv : Val :=
  λᵥ: f max,
    (Fix "rec" "acc"
      (let: i := Expr.fst (.var "acc") in
        let: b := Expr.snd (.var "acc") in
          Expr.ite (.binOp .ltOp (.var "max") (.var "i")) (.var "b")
            (Expr.app (.var "rec")
              (Expr.pair (.binOp .plusOp (.var "i") (.lit (.litInt 1)))
                (Expr.app (Expr.app (.var "f") (.var "i")) (.var "b")))))).toExpr

def iterupv : Val :=
  λᵥ: f init min max,
    Expr.app (Expr.app (Expr.app (iterupiv Fix).toExpr (.var "f")) (.var "max"))
      (Expr.pair (.var "min") (.var "init"))

include fix_typing in
/-- Not in the Rocq file: the typing of the inner fixpoint, split out because Lean cannot guess
the argument type of a `Fix` the way `solve_typing`'s `econstructor` loop can. -/
theorem iterupiv_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ (iterupiv Fix).toExpr
      (.fn (.fn .int (.fn .bool .bool)) (.fn .int (.fn (.prod .int .bool) .bool))) := by
  refine .typed_lam n Γ "f" _ (.fn .int (.fn .bool .bool)) _ (by solve_type_wf) ?_
  refine .typed_lam n _ "max" _ .int _ .int_wf ?_
  refine fix_typing n _ "rec" "acc" (.prod .int .bool) .bool _
    (by solve_type_wf) .bool_wf (by decide) ?_
  solve_typing

include fix_typing in
theorem iterupv_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ (iterupv Fix).toExpr
      (.fn (.fn .int (.fn .bool .bool)) (.fn .bool (.fn .int (.fn .int .bool)))) := by
  refine .typed_lam n Γ "f" _ (.fn .int (.fn .bool .bool)) _ (by solve_type_wf) ?_
  refine .typed_lam n _ "init" _ .bool _ .bool_wf ?_
  refine .typed_lam n _ "min" _ .int _ .int_wf ?_
  refine .typed_lam n _ "max" _ .int .bool .int_wf ?_
  exact .typed_app n _ _ _ (.prod .int .bool) .bool
    (.typed_app n _ _ _ .int (.fn (.prod .int .bool) .bool)
      (.typed_app n _ _ _ (.fn .int (.fn .bool .bool))
        (.fn .int (.fn (.prod .int .bool) .bool))
        (iterupiv_typed Fix fix_typing n _)
        (.typed_var _ _ "f" _ (by solve_lookup)))
      (.typed_var _ _ "max" _ (by solve_lookup)))
    (.typed_pair n _ _ _ .int .bool
      (.typed_var _ _ "min" _ (by solve_lookup))
      (.typed_var _ _ "init" _ (by solve_lookup)))

/-- The set module: membership test, minimum and maximum, behind an existential. -/
def iset : Val :=
  .packV (.pairV (.pairV (.pairV
    -- empty
    (.pairV (.pairV (.lamV (.bNamed "x") (.lit (.litBool false))) (.litV (.litInt 0)))
      (.litV (.litInt 0)))
    -- singleton
    (λᵥ: n, Expr.pair (Expr.pair (λ: x, Expr.binOp .eqOp (.var "n") (.var "x")) (.var "n"))
      (.var "n")))
    -- union
    (λᵥ: s1 s2, Expr.pair (Expr.pair
      (λ: x, Expr.ite (Expr.app (Expr.fst (Expr.fst (.var "s1"))) (.var "x"))
        (.lit (.litBool true)) (Expr.app (Expr.fst (Expr.fst (.var "s2"))) (.var "x")))
      (Expr.app (Expr.app mini.toExpr (Expr.snd (Expr.fst (.var "s1"))))
        (Expr.snd (Expr.fst (.var "s1")))))
      (Expr.app (Expr.app maxi.toExpr (Expr.snd (.var "s1"))) (Expr.snd (.var "s1")))))
    -- subset
    (λᵥ: s1 s2,
      let: min := Expr.snd (Expr.fst (.var "s1")) in
        let: max := Expr.snd (.var "s1") in
          Expr.app (Expr.app (Expr.app (Expr.app (iterupv Fix).toExpr
            (λ: i acc, Expr.ite (Expr.app (Expr.fst (Expr.fst (.var "s2"))) (.var "i"))
              (.var "acc") (.lit (.litBool false))))
            (.lit (.litBool true))) (.var "min")) (.var "max")))

include fix_typing in
theorem iset_typed (n : Nat) (Γ : TypingContext) : SynTyped n Γ (iset Fix).toExpr ISET := by
  refine .typed_pack n Γ _ _ setRep (by solve_type_wf) (by solve_type_wf) ?_
  refine .typed_pair n Γ _ _
    (.prod (.prod setRep (.fn .int setRep)) (.fn setRep (.fn setRep setRep)))
    (.fn setRep (.fn setRep .bool)) (by solve_typing) ?_
  refine .typed_lam n Γ "s1" _ setRep _ (by solve_type_wf) ?_
  refine .typed_lam n _ "s2" _ setRep .bool (by solve_type_wf) ?_
  refine .typed_app n _ _ _ .int .bool ?_ (by solve_typing)
  refine .typed_lam n _ "min" _ .int .bool .int_wf ?_
  refine .typed_app n _ _ _ .int .bool ?_ (by solve_typing)
  refine .typed_lam n _ "max" _ .int .bool .int_wf ?_
  exact .typed_app n _ _ _ .int .bool
    (.typed_app n _ _ _ .int (.fn .int .bool)
      (.typed_app n _ _ _ .bool (.fn .int (.fn .int .bool))
        (.typed_app n _ _ _ (.fn .int (.fn .bool .bool))
          (.fn .bool (.fn .int (.fn .int .bool)))
          (iterupv_typed Fix fix_typing n _) (by solve_typing))
        (by solve_typing))
      (by solve_typing))
    (by solve_typing)

/-- `ISET` with an equality test added. -/
def ISETE : Ty :=
  .exist (.prod (.prod (.prod (.prod (.tVar 0) (.fn .int (.tVar 0)))
    (.fn (.tVar 0) (.fn (.tVar 0) (.tVar 0)))) (.fn (.tVar 0) (.fn (.tVar 0) .bool)))
    (.fn (.tVar 0) (.fn (.tVar 0) .bool)))

/-- Two sets are equal when each is a subset of the other. -/
def add_equality : Val :=
  λᵥ: is, unpackE (.bNamed "isi") (.var "is")
    (let: subset := Expr.snd (.var "isi") in
      Expr.pack (Expr.pair (.var "isi")
        (λ: s1 s2,
          Expr.ite (Expr.app (Expr.app (.var "subset") (.var "s1")) (.var "s2"))
            (Expr.app (Expr.app (.var "subset") (.var "s2")) (.var "s1"))
            (.lit (.litBool false)))))

theorem add_equality_typed (n : Nat) (Γ : TypingContext) :
    SynTyped n Γ add_equality.toExpr (.fn ISET ISETE) := by
  refine .typed_lam n Γ "is" _ ISET ISETE (by solve_type_wf) ?_
  refine .typed_unpack n _ "isi" _ _ _ ISETE (by solve_type_wf)
    (.typed_var _ _ "is" _ (by solve_lookup)) ?_
  rw [type_wf_closed_rename ISETE (· + 1) (by solve_type_wf)]
  refine .typed_app (n + 1) _ _ _ (.fn (.tVar 0) (.fn (.tVar 0) .bool)) ISETE ?_
    (by solve_typing)
  refine .typed_lam (n + 1) _ "subset" _ (.fn (.tVar 0) (.fn (.tVar 0) .bool)) ISETE
    (by solve_type_wf) ?_
  refine .typed_pack (n + 1) _ _ _ (.tVar 0) (by solve_type_wf) (by solve_type_wf) ?_
  solve_typing

end Existential

/-! ## Exercise 3 (LN 30): evenness -/

section Even

/-- `∃ α. α × (α → α) × (α → Int)`: zero, add two, and a projection to the integers. -/
def even_type : Ty :=
  .exist (.prod (.prod (.tVar 0) (.fn (.tVar 0) (.tVar 0))) (.fn (.tVar 0) .int))

def even_impl : Val :=
  .packV (.pairV (.pairV (.litV (.litInt 0))
    (λᵥ: z, Expr.binOp .plusOp (.lit (.litInt 2)) (.var "z")))
    (λᵥ: z, Expr.var "z"))

variable (even_dec : Val)
variable (even_dec_typed : ∀ (n : Nat) (Γ : TypingContext),
  SynTyped n Γ even_dec.toExpr (.fn .int .bool))

/-- The same module, with `toint` asserting evenness of its argument first. -/
def even_impl_instrumented : Val :=
  .packV (.pairV (.pairV (.litV (.litInt 0))
    (λᵥ: z, Expr.binOp .plusOp (.lit (.litInt 2)) (.var "z")))
    (λᵥ: z, seqE (assert (Expr.app even_dec.toExpr (.var "z"))) (.var "z")))

variable (even_spec : ∀ z : Int,
  BigStep (.app even_dec.toExpr (.lit (.litInt z))) (.litV (.litBool (z % 2 == 0))))
variable (even_closed : closed [] even_dec.toExpr)

include even_spec even_closed in
theorem even_impl_instrumented_safe (δ : TyVarInterp) :
    valRel δ even_type (even_impl_instrumented even_dec) := by
  simp only [even_type, even_impl_instrumented, valRel]
  refine ⟨_, rfl, ⟨fun v => ∃ z : Int, z % 2 = 0 ∧ v = .litV (.litInt z),
    fun v h => by obtain ⟨z, _, rfl⟩ := h; rfl⟩, ?_⟩
  refine ⟨_, _, rfl, ⟨_, _, rfl, ⟨0, by decide, rfl⟩, ?_⟩, ?_⟩
  · refine ⟨.bNamed "z", _, rfl, rfl, ?_⟩
    rintro v' ⟨z, hz, rfl⟩
    refine ⟨.litV (.litInt (2 + z)), ?_, 2 + z, by omega, rfl⟩
    simp only [subst', subst, Val.toExpr]
    exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl
  · refine ⟨.bNamed "z", _, rfl, ?_, ?_⟩
    · have hd : Expr.isClosed ["z"] even_dec.toExpr = true := closed_weaken_nil even_closed
      simp [closed, Expr.isClosed, seqE, assert, Binder.cons, hd]
    · rintro v' ⟨z, hz, rfl⟩
      refine ⟨.litV (.litInt z), ?_, z, rfl⟩
      simp only [subst', subst, Val.toExpr, seqE, assert, subst_closed_nil even_closed]
      refine .bs_app _ _ .bAnon (.lit (.litInt z)) (.litV .litUnit) _ (.bs_lam _ _) ?_
        (.bs_lit _)
      refine .bs_if_true _ _ _ _ ?_ (.bs_lit _)
      have := even_spec z
      rwa [show (z % 2 == 0) = true from by simp [hz]] at this

end Even

/-! ## Exercise 4 (LN 31): abstract sums -/

section AbstractSum

/-- `∃ α. (A → α) × (B → α) × (∀ β. α → (A → β) → (B → β) → β)`. -/
def sum_ex_type (A B : Ty) : Ty :=
  .exist (.prod (.prod (.fn (A.rename (· + 1)) (.tVar 0)) (.fn (B.rename (· + 1)) (.tVar 0)))
    (.all (.fn (.tVar 1)
      (.fn (.fn (A.rename (fun n => n + 2)) (.tVar 0))
        (.fn (.fn (B.rename (fun n => n + 2)) (.tVar 0)) (.tVar 0))))))

/-- The representation: a tag, `1` or `2`, paired with the payload. -/
def sum_ex_impl : Val :=
  .packV (.pairV
    (.pairV (λᵥ: x, Expr.pair (.lit (.litInt 1)) (.var "x"))
      (λᵥ: x, Expr.pair (.lit (.litInt 2)) (.var "x")))
    (.tLamV (λ: x f1 f2,
      Expr.ite (Expr.binOp .eqOp (Expr.fst (.var "x")) (.lit (.litInt 1)))
        (Expr.app (.var "f1") (Expr.snd (.var "x")))
        (Expr.app (.var "f2") (Expr.snd (.var "x"))))))

theorem sum_ex_safe (A B : Ty) (δ : TyVarInterp) : valRel δ (sum_ex_type A B) sum_ex_impl := by
  have hcl : ∀ v : Val,
      ((∃ v', valRel δ A v' ∧ v = .pairV (.litV (.litInt 1)) v') ∨
       (∃ v', valRel δ B v' ∧ v = .pairV (.litV (.litInt 2)) v')) → closed [] v.toExpr := by
    rintro v (⟨v', hv, rfl⟩ | ⟨v', hv, rfl⟩)
    · simpa [closed, Expr.isClosed, Val.toExpr] using val_rel_closed v' δ A hv
    · simpa [closed, Expr.isClosed, Val.toExpr] using val_rel_closed v' δ B hv
  let τ : SemType := ⟨_, hcl⟩
  simp only [sum_ex_type, sum_ex_impl, valRel]
  refine ⟨_, rfl, τ, ?_⟩
  refine ⟨_, _, rfl, ⟨_, _, rfl, ?_, ?_⟩, ?_⟩
  · -- the left injection
    refine ⟨.bNamed "x", _, rfl, rfl, fun v' hv' => ?_⟩
    refine ⟨.pairV (.litV (.litInt 1)) v', ?_, ?_⟩
    · simp only [subst', subst]
      exact .bs_pair _ _ _ _ (.bs_lit _) (big_step_of_val rfl)
    · exact Or.inl ⟨v', (sem_val_rel_cons A δ v' τ).mpr hv', rfl⟩
  · -- the right injection
    refine ⟨.bNamed "x", _, rfl, rfl, fun v' hv' => ?_⟩
    refine ⟨.pairV (.litV (.litInt 2)) v', ?_, ?_⟩
    · simp only [subst', subst]
      exact .bs_pair _ _ _ _ (.bs_lit _) (big_step_of_val rfl)
    · exact Or.inr ⟨v', (sem_val_rel_cons B δ v' τ).mpr hv', rfl⟩
  · -- the eliminator
    refine ⟨_, rfl, rfl, fun τ' => ⟨_, .bs_lam _ _, ?_⟩⟩
    refine ⟨.bNamed "x", _, rfl, rfl, fun v' hv' => ?_⟩
    have hv'cl : closed [] v'.toExpr := τ.closed_val v' hv'
    refine ⟨_, .bs_lam _ _, ?_⟩
    refine ⟨.bNamed "f1", _, rfl, closed_subst hv'cl (by decide), fun f hf => ?_⟩
    have hfcl : closed [] f.toExpr := by obtain ⟨_, _, rfl, hcl, _⟩ := hf; exact hcl
    refine ⟨_, .bs_lam _ _, ?_⟩
    refine ⟨.bNamed "f2", _, rfl,
      closed_subst hfcl (closed_subst hv'cl (by decide)), fun g hg => ?_⟩
    have hgcl : closed [] g.toExpr := by obtain ⟨_, _, rfl, hcl, _⟩ := hg; exact hcl
    simp +decide only [subst', subst, subst_closed_nil hv'cl, subst_closed_nil hfcl, reduceIte]
    obtain ⟨xf, ef, hfeq, _, hfbody⟩ := hf
    obtain ⟨xg, eg, hgeq, _, hgbody⟩ := hg
    rcases hv' with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · -- tag `1`: the first continuation runs
      have hshift : A.rename (fun n => n + 2) = (A.rename (· + 1)).rename (· + 1) :=
        (Ty.rename_rename A (· + 1) (· + 1)).symm
      obtain ⟨w, hbw, hw⟩ := hfbody v (by
        rw [hshift]
        exact (sem_val_rel_cons (A.rename (· + 1)) (τ .: δ) v τ').mp
          ((sem_val_rel_cons A δ v τ).mp hv))
      refine ⟨w, ?_, hw⟩
      refine .bs_if_true _ _ _ _ ?_ ?_
      · exact .bs_binop _ _ _ _ _ _ (.bs_fst _ _ _ (big_step_of_val rfl)) (.bs_lit _) rfl
      · exact .bs_app _ _ xf ef v w (big_step_of_val (congrArg Val.toExpr hfeq))
          (.bs_snd _ _ _ (big_step_of_val rfl)) hbw
    · -- tag `2`: the second continuation runs
      have hshift : B.rename (fun n => n + 2) = (B.rename (· + 1)).rename (· + 1) :=
        (Ty.rename_rename B (· + 1) (· + 1)).symm
      obtain ⟨w, hbw, hw⟩ := hgbody v (by
        rw [hshift]
        exact (sem_val_rel_cons (B.rename (· + 1)) (τ .: δ) v τ').mp
          ((sem_val_rel_cons B δ v τ).mp hv))
      refine ⟨w, ?_, hw⟩
      refine .bs_if_false _ _ _ _ ?_ ?_
      · exact .bs_binop _ _ _ _ _ _ (.bs_fst _ _ _ (big_step_of_val rfl)) (.bs_lit _) rfl
      · exact .bs_app _ _ xg eg v w (big_step_of_val (congrArg Val.toExpr hgeq))
          (.bs_snd _ _ _ (big_step_of_val rfl)) hbw

end AbstractSum

/-! ## Exercise 6 (LN 35): contextual equivalence -/

namespace Binary

/-- The primitive sum type, packaged behind the same interface as `sum_ex_impl`. -/
def sum_ex_impl' : Val :=
  .packV (.pairV
    (.pairV (λᵥ: x, Expr.injL (.var "x")) (λᵥ: x, Expr.injR (.var "x")))
    (.tLamV (λ: x f1 f2, Expr.case (.var "x") (.var "f1") (.var "f2"))))

theorem sum_ex_impl'_typed (n : Nat) (Γ : TypingContext) (A B : Ty)
    (hA : TypeWf n A) (hB : TypeWf n B) :
    SynTyped n Γ sum_ex_impl'.toExpr (sum_ex_type A B) := by
  refine .typed_pack n Γ _ _ (.sum A B) (by solve_type_wf) (by solve_type_wf) ?_
  simp only [Ty.subst1, Ty.substTy, Ty.rename_substTy, Ty.substTy_id, Ty.rename,
    ← Ty.rename_eq_substTy]
  solve_typing

theorem sum_ex_impl_equiv (n : Nat) (Γ : TypingContext) (A B : Ty) :
    ctx_equiv n Γ sum_ex_impl'.toExpr sum_ex_impl.toExpr (sum_ex_type A B) := by
  refine sem_typing_ctx_equiv (Δ := n) ⟨closed_weaken_nil (by decide),
    closed_weaken_nil (by decide), fun θ₁ θ₂ δ _ => ?_⟩
  rw [substMap_is_closed (X := []) (by decide) (by simp),
    substMap_is_closed (X := []) (by decide) (by simp)]
  refine ⟨_, _, big_step_of_val rfl, big_step_of_val rfl, ?_⟩
  have hRcl : ∀ v w : Val,
      ((∃ a b : Val, valRel δ A a b ∧ v = .injLV a ∧ w = .pairV (.litV (.litInt 1)) b) ∨
       (∃ a b : Val, valRel δ B a b ∧ v = .injRV a ∧ w = .pairV (.litV (.litInt 2)) b)) →
      closed [] v.toExpr ∧ closed [] w.toExpr := by
    rintro v w (⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩) <;>
      obtain ⟨h₁, h₂⟩ := val_rel_is_closed a b δ _ hab <;>
      exact ⟨h₁, by simpa [closed, Expr.isClosed, Val.toExpr] using h₂⟩
  let R : SemType := ⟨_, hRcl⟩
  simp only [sum_ex_type, sum_ex_impl', sum_ex_impl, valRel]
  refine ⟨_, _, rfl, rfl, R, ?_⟩
  refine ⟨_, _, _, _, rfl, rfl, ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩, ?_⟩
  · -- the left injection
    refine ⟨.bNamed "x", .bNamed "x", _, _, rfl, rfl, rfl, rfl, fun v' w' hvw => ?_⟩
    refine ⟨.injLV v', .pairV (.litV (.litInt 1)) w', ?_, ?_, ?_⟩
    · simpa +decide only [subst', subst, reduceIte] using
        BigStep.bs_injl _ _ (big_step_of_val rfl)
    · simpa +decide only [subst', subst, reduceIte] using
        BigStep.bs_pair _ _ _ _ (.bs_lit _) (big_step_of_val rfl)
    · exact Or.inl ⟨v', w', (sem_val_rel_cons A δ v' w' R).mpr hvw, rfl, rfl⟩
  · -- the right injection
    refine ⟨.bNamed "x", .bNamed "x", _, _, rfl, rfl, rfl, rfl, fun v' w' hvw => ?_⟩
    refine ⟨.injRV v', .pairV (.litV (.litInt 2)) w', ?_, ?_, ?_⟩
    · simpa +decide only [subst', subst, reduceIte] using
        BigStep.bs_injr _ _ (big_step_of_val rfl)
    · simpa +decide only [subst', subst, reduceIte] using
        BigStep.bs_pair _ _ _ _ (.bs_lit _) (big_step_of_val rfl)
    · exact Or.inr ⟨v', w', (sem_val_rel_cons B δ v' w' R).mpr hvw, rfl, rfl⟩
  · -- the eliminator
    refine ⟨_, _, rfl, rfl, rfl, rfl, fun R' => ⟨_, _, .bs_lam _ _, .bs_lam _ _, ?_⟩⟩
    refine ⟨.bNamed "x", .bNamed "x", _, _, rfl, rfl, rfl, rfl, fun v' w' hvw => ?_⟩
    obtain ⟨hv'cl, hw'cl⟩ := R.closed_val v' w' hvw
    refine ⟨_, _, .bs_lam _ _, .bs_lam _ _, ?_⟩
    refine ⟨.bNamed "f1", .bNamed "f1", _, _, rfl, rfl,
      closed_subst hv'cl (by decide), closed_subst hw'cl (by decide), fun f f' hf => ?_⟩
    have hfcl : closed [] f.toExpr := by obtain ⟨_, _, _, _, rfl, _, hcl, _⟩ := hf; exact hcl
    have hf'cl : closed [] f'.toExpr := by
      obtain ⟨_, _, _, _, _, rfl, _, hcl, _⟩ := hf; exact hcl
    refine ⟨_, _, .bs_lam _ _, .bs_lam _ _, ?_⟩
    refine ⟨.bNamed "f2", .bNamed "f2", _, _, rfl, rfl,
      closed_subst hfcl (closed_subst hv'cl (by decide)),
      closed_subst hf'cl (closed_subst hw'cl (by decide)), fun g g' hg => ?_⟩
    have hgcl : closed [] g.toExpr := by obtain ⟨_, _, _, _, rfl, _, hcl, _⟩ := hg; exact hcl
    have hg'cl : closed [] g'.toExpr := by
      obtain ⟨_, _, _, _, _, rfl, _, hcl, _⟩ := hg; exact hcl
    simp +decide only [subst', subst, subst_closed_nil hv'cl, subst_closed_nil hw'cl,
      subst_closed_nil hfcl, subst_closed_nil hf'cl, reduceIte]
    obtain ⟨xf, yf, ef, ef', hfeq, hf'eq, _, _, hfbody⟩ := hf
    obtain ⟨xg, yg, eg, eg', hgeq, hg'eq, _, _, hgbody⟩ := hg
    rcases hvw with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
    · have hshift : A.rename (fun n => n + 2) = (A.rename (· + 1)).rename (· + 1) :=
        (Ty.rename_rename A (· + 1) (· + 1)).symm
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hfbody a b (by
        rw [hshift]
        exact (sem_val_rel_cons (A.rename (· + 1)) (R .:₂ δ) a b R').mp
          ((sem_val_rel_cons A δ a b R).mp hab))
      refine ⟨u₁, u₂, ?_, ?_, hu⟩
      · exact .bs_casel _ _ _ a u₁ (big_step_of_val rfl)
          (.bs_app _ _ xf ef a u₁ (big_step_of_val (congrArg Val.toExpr hfeq))
            (big_step_of_val rfl) hb₁)
      · refine .bs_if_true _ _ _ _ ?_ ?_
        · exact .bs_binop _ _ _ _ _ _ (.bs_fst _ _ _ (big_step_of_val rfl)) (.bs_lit _) rfl
        · exact .bs_app _ _ yf ef' b u₂ (big_step_of_val (congrArg Val.toExpr hf'eq))
            (.bs_snd _ _ _ (big_step_of_val rfl)) hb₂
    · have hshift : B.rename (fun n => n + 2) = (B.rename (· + 1)).rename (· + 1) :=
        (Ty.rename_rename B (· + 1) (· + 1)).symm
      obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hgbody a b (by
        rw [hshift]
        exact (sem_val_rel_cons (B.rename (· + 1)) (R .:₂ δ) a b R').mp
          ((sem_val_rel_cons B δ a b R).mp hab))
      refine ⟨u₁, u₂, ?_, ?_, hu⟩
      · exact .bs_caser _ _ _ a u₁ (big_step_of_val rfl)
          (.bs_app _ _ xg eg a u₁ (big_step_of_val (congrArg Val.toExpr hgeq))
            (big_step_of_val rfl) hb₁)
      · refine .bs_if_false _ _ _ _ ?_ ?_
        · exact .bs_binop _ _ _ _ _ _ (.bs_fst _ _ _ (big_step_of_val rfl)) (.bs_lit _) rfl
        · exact .bs_app _ _ yg eg' b u₂ (big_step_of_val (congrArg Val.toExpr hg'eq))
            (.bs_snd _ _ _ (big_step_of_val rfl)) hb₂

end Binary

end SystemF
