import LeanLR.TypeSystems.SystemF.LogRel
import LeanLR.TypeSystems.SystemF.BinaryLogRel
import LeanLR.TypeSystems.SystemF.ChurchEncodings

/-!
# System F: existential types as invariants

`systemf/existential_invariants.v`. `MyBit_instrumented` asserts an invariant on its hidden
representation that the logical relation can carry, though no syntactic rule states it; the
`SystemF.Binary` section at the bottom relates the integer and boolean bit modules.
-/

open Iris.Std

namespace SystemF

/-! ## Assertions -/

theorem assert_true : ContextualSteps (assert (.lit (.litBool true))) (.lit .litUnit) :=
  .single (base_contextual_step (.ifTrueS _ _))

theorem assert_false :
    ContextualSteps (assert (.lit (.litBool false)))
      (.app (.lit (.litInt 0)) (.lit (.litInt 0))) :=
  .single (base_contextual_step (.ifFalseS _ _))

/-! ## A bit module -/

/-- `∃ α, (α × (α → α)) × (α → Bool)`. -/
def BIT : Ty :=
  .exist (.prod (.prod (.tVar 0) (.fn (.tVar 0) (.tVar 0))) (.fn (.tVar 0) .bool))

def MyBit : Val :=
  .packV (.pairV
    (.pairV (.litV (.litInt 0))
      (.lamV (.bNamed "x") (.binOp .minusOp (.lit (.litInt 1)) (.var "x"))))
    (.lamV (.bNamed "x") (.binOp .ltOp (.lit (.litInt 0)) (.var "x"))))

theorem MyBit_typed (n : Nat) (Γ : TypingContext) : SynTyped n Γ MyBit.toExpr BIT := by
  refine .typed_pack n Γ _ _ .int .int_wf ?_ ?_
  · exact .prod_wf (.prod_wf (.tVar_wf (by omega))
      (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))))
      (.fn_wf (.tVar_wf (by omega)) .bool_wf)
  · refine .typed_pair n Γ _ _ (.prod .int (.fn .int .int)) (.fn .int .bool) ?_ ?_
    · refine .typed_pair n Γ _ _ .int (.fn .int .int) (.typed_lit_int n Γ 0) ?_
      exact .typed_lam n Γ "x" _ .int .int .int_wf
        (.typed_binOp n _ .minusOp _ _ .int .int .int .minus_typed
          (.typed_lit_int n _ 1) (.typed_var _ _ "x" _ lookup_here))
    · exact .typed_lam n Γ "x" _ .int .bool .int_wf
        (.typed_binOp n _ .ltOp _ _ .int .int .bool .lt_typed
          (.typed_lit_int n _ 0) (.typed_var _ _ "x" _ lookup_here))

/-- The same module, with the representation invariant asserted at every entry point. -/
def MyBit_instrumented : Val :=
  .packV (.pairV
    (.pairV (.litV (.litInt 0))
      (.lamV (.bNamed "x")
        (seqE (assert (Or (.binOp .eqOp (.var "x") (.lit (.litInt 0)))
                          (.binOp .eqOp (.var "x") (.lit (.litInt 1)))))
          (.binOp .minusOp (.lit (.litInt 1)) (.var "x")))))
    (.lamV (.bNamed "x")
      (seqE (assert (Or (.binOp .eqOp (.var "x") (.lit (.litInt 0)))
                        (.binOp .eqOp (.var "x") (.lit (.litInt 1)))))
        (.binOp .ltOp (.lit (.litInt 0)) (.var "x")))))

def MyBoolBit : Val :=
  .packV (.pairV
    (.pairV (.litV (.litBool false)) (.lamV (.bNamed "x") (.unOp .negOp (.var "x"))))
    (.lamV (.bNamed "x") (.var "x")))

theorem MyBoolBit_typed (n : Nat) (Γ : TypingContext) : SynTyped n Γ MyBoolBit.toExpr BIT := by
  refine .typed_pack n Γ _ _ .bool .bool_wf ?_ ?_
  · exact .prod_wf (.prod_wf (.tVar_wf (by omega))
      (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))))
      (.fn_wf (.tVar_wf (by omega)) .bool_wf)
  · refine .typed_pair n Γ _ _ (.prod .bool (.fn .bool .bool)) (.fn .bool .bool) ?_ ?_
    · refine .typed_pair n Γ _ _ .bool (.fn .bool .bool) (.typed_lit_bool n Γ false) ?_
      exact .typed_lam n Γ "x" _ .bool .bool .bool_wf
        (.typed_unOp n _ .negOp _ .bool .bool .neg_typed (.typed_var _ _ "x" _ lookup_here))
    · exact .typed_lam n Γ "x" _ .bool .bool .bool_wf (.typed_var _ _ "x" _ lookup_here)

/-! ## The instrumented module is semantically typed -/

/-- The representation invariant: the hidden type holds only `0` and `1`. -/
def bitSemType : SemType where
  car v := v = .litV (.litInt 0) ∨ v = .litV (.litInt 1)
  closed_val v h := by rcases h with rfl | rfl <;> rfl

/-- The assertion in the instrumented module always succeeds on a value satisfying the
invariant. -/
private theorem assert_bit_bigstep {z : Int} (h : z = 0 ∨ z = 1) :
    BigStep (assert (Or (.binOp .eqOp (.lit (.litInt z)) (.lit (.litInt 0)))
      (.binOp .eqOp (.lit (.litInt z)) (.lit (.litInt 1))))) (.litV .litUnit) := by
  refine .bs_if_true _ _ _ _ ?_ (.bs_lit _)
  rcases h with rfl | rfl
  · exact .bs_if_true _ _ _ _
      (.bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl) (.bs_lit _)
  · refine .bs_if_false _ _ _ _
      (.bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl) ?_
    exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl

theorem MyBit_instrumented_sem_typed (δ : TyVarInterp) : valRel δ BIT MyBit_instrumented := by
  simp only [BIT, valRel]
  refine ⟨_, rfl, bitSemType, ?_⟩
  refine ⟨_, _, rfl, ⟨_, _, rfl, ?_, ?_⟩, ?_⟩
  · exact Or.inl rfl
  · refine ⟨.bNamed "x", _, rfl, rfl, fun v' hv' => ?_⟩
    rcases hv' with rfl | rfl
    · refine ⟨.litV (.litInt 1), ?_, Or.inr rfl⟩
      refine .bs_app _ _ .bAnon _ (.litV .litUnit) _ (.bs_lam _ _)
        (assert_bit_bigstep (Or.inl rfl)) ?_
      exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl
    · refine ⟨.litV (.litInt 0), ?_, Or.inl rfl⟩
      refine .bs_app _ _ .bAnon _ (.litV .litUnit) _ (.bs_lam _ _)
        (assert_bit_bigstep (Or.inr rfl)) ?_
      exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl
  · refine ⟨.bNamed "x", _, rfl, rfl, fun v' hv' => ?_⟩
    rcases hv' with rfl | rfl
    · refine ⟨.litV (.litBool false), ?_, ⟨false, rfl⟩⟩
      refine .bs_app _ _ .bAnon _ (.litV .litUnit) _ (.bs_lam _ _)
        (assert_bit_bigstep (Or.inl rfl)) ?_
      exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl
    · refine ⟨.litV (.litBool true), ?_, ⟨true, rfl⟩⟩
      refine .bs_app _ _ .bAnon _ (.litV .litUnit) _ (.bs_lam _ _)
        (assert_bit_bigstep (Or.inr rfl)) ?_
      exact .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl

/-! ## The integer and boolean bit modules are relationally equal -/

namespace Binary

/-- The relational representation invariant: `0` on the left stands for `false` on the right, and
`1` for `true`. -/
def bitRelSemType : SemType where
  car v w := (v = .litV (.litInt 0) ∧ w = .litV (.litBool false)) ∨
             (v = .litV (.litInt 1) ∧ w = .litV (.litBool true))
  closed_val v w h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem MyBit_MyBoolBit_sem_typed (δ : TyVarInterp) : valRel δ BIT MyBit MyBoolBit := by
  simp only [BIT, valRel]
  refine ⟨_, _, rfl, rfl, bitRelSemType, ?_⟩
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩
  · refine ⟨_, _, _, _, rfl, rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩
    refine ⟨.bNamed "x", .bNamed "x", _, _, rfl, rfl, rfl, rfl, fun v w hvw => ?_⟩
    rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.litV (.litInt 1), .litV (.litBool true),
        .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl,
        .bs_unop _ _ _ _ (.bs_lit _) rfl, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨.litV (.litInt 0), .litV (.litBool false),
        .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl,
        .bs_unop _ _ _ _ (.bs_lit _) rfl, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨.bNamed "x", .bNamed "x", _, _, rfl, rfl, rfl, rfl, fun v w hvw => ?_⟩
    rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.litV (.litBool false), .litV (.litBool false),
        .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl, .bs_lit _, false, rfl, rfl⟩
    · exact ⟨.litV (.litBool true), .litV (.litBool true),
        .bs_binop _ _ _ _ _ _ (.bs_lit _) (.bs_lit _) rfl, .bs_lit _, true, rfl, rfl⟩

end Binary

end SystemF
