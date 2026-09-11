import LeanLR.ProgramLogics.LogRel.LogRel
import LeanLR.ProgramLogics.LogRel.GhostState
import LeanLR.ProgramLogics.GhostTheories

/-!
# Semantically, but not syntactically, typed programs

The four `logrel_*` sections of `program_logics/logrel/ghost_state_sol.v`. Each program is safe
for a reason the type system cannot see, and the logical relation carries that reason as ghost
state behind an invariant.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode Iris.Std
open ProgramLogics.GhostTheories

namespace ProgramLogics.LogRel

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

/-- The course's `assert`: a failed assertion applies an integer to an integer and is stuck. -/
def assertE (e : Exp) : Exp := hl(if &e then #() else #(0 : Int) #(0 : Int))

/-! ## A symbol ADT -/

section Symbol

/-- `∃ α, ((Unit → α) × (α → Unit))`. -/
def symbolT : Ty := .exist (.prod (.fn .unit (.tVar 0)) (.fn (.tVar 0) .unit))

def mkSymbol : Exp :=
  hl(let c := ref(#(0 : Int));
     &(pack hl(((λ _, let x := !c; (c ← x + #(1 : Int); x)),
                (λ y, &(assertE hl(y ≤ !c)))))))

def symbolN : Namespace := nroot .@ "symbol"

variable [MonoNatG GF]

def monoNatInv (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ n : Nat, (l ↦ some hl_val(#(n : Int))) ∗ mono γ n)

/-- The hidden representation type: a symbol is an integer below the current counter. -/
def monoNatT (γ : GName) : SemType GF :=
  mkSemType (fun v => iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗ lb γ n))
    (fun _ => inferInstance)

@[simp] theorem monoNatT_car (γ : GName) (v : Val) :
    (monoNatT (GF := GF) γ).car v = iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗ lb γ n) := rfl

theorem mk_symbol_semtyped : semTyped GF 0 ∅ mkSymbol symbolT := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [Exp.substMap_empty (M := TyMapStr)]
  simp only [exprInterp, mkSymbol, pack]
  swp_enter Hcl
  wp_alloc l with Hl
  wp_pures
  imod mono_nat_new (GF := GF) 0 with ⟨%γ, Hauth⟩
  imod Iris.inv_alloc symbolN (∅ : CoPset) (monoNatInv γ l) $$ [Hl Hauth] with #Hinv
  · inext
    unfold monoNatInv
    iexists (0 : Nat)
    isplitl [Hl]
    · iexact Hl
    · iexact Hauth
  imod Hcl
  imodintro
  simp only [symbolT, typeInterp_exist, typeInterp_prod, typeInterp_fn, typeInterp_unit,
    typeInterp_tVar, existInterp_car]
  iexists _
  isplitr
  · ipureintro; rfl
  iexists (monoNatT γ)
  simp only [prodInterp_car, funInterp_car, varInterp, consEnv, unitInterp_car, monoNatT_car]
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %w !> %hw
    subst hw
    simp only [exprInterp]
    swp_pures
    iapply ImpredInvariants.inv_open (N := symbolN) (by simp) $$ Hinv
    iintro HI
    unfold monoNatInv
    swp_enter Hcl2
    icases HI with ⟨%m, >Hl, >Hauth⟩
    wp_load
    wp_pures
    wp_store
    icases mono_nat_get_bound $$ Hauth with ⟨Hauth, #Hbound⟩
    imod mono_nat_increase_val $$ Hauth with Hauth
    imod Hcl2
    imodintro
    isplitl [Hl Hauth]
    · inext
      iexists (m + 1)
      rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 from by omega]
      isplitl [Hl]
      · iexact Hl
      · iexact Hauth
    · simp only [monoNatT_car]
      iexists m
      isplitr
      · ipureintro; rfl
      · iexact Hbound
  · iintro %w !> ⟨%m, %hw, #Hlb⟩
    subst hw
    simp only [exprInterp, assertE]
    swp_pures
    iapply ImpredInvariants.inv_open (N := symbolN) (by simp) $$ Hinv
    iintro HI
    unfold monoNatInv
    swp_enter Hcl2
    icases HI with ⟨%k, >Hl, >Hauth⟩
    wp_expr_simp
    wp_bind (!_)
    wp_load
    icases mono_nat_use_bound' $$ [Hauth Hlb] with ⟨Hauth, %Hle⟩
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hlb
    wp_pures
    rw [show (decide ((m : Int) ≤ (k : Int))) = true from by simp; omega]
    wp_pures
    imod Hcl2
    imodintro
    isplitl [Hl Hauth]
    · inext
      iexists k
      isplitl [Hl]
      · iexact Hl
      · iexact Hauth
    · simp only [unitInterp_car]
      ipureintro
      trivial

end Symbol

/-! ## A one-shot invariant -/

section OneShot

def code : Exp :=
  hl(let x := ref(#(42 : Int));
     (λ f, (x ← #(1337 : Int); (f #(); &(assertE hl((!x = #(1337 : Int))))))))

def codeN : Namespace := nroot .@ "oneshot"

variable [GhostTheories.OneShotG GF Nat]

/-- Before the call the location holds `42` and the token is pending; afterwards it holds `1337`
and the token is spent. Only the second disjunct survives the store, and that is what rules out
the callback resetting the location. -/
def oneshotInv (γ : GName) (l : Loc) : IProp GF :=
  iprop(((l ↦ some hl_val(#(42 : Int))) ∗ osPending Nat γ) ∨
    ((l ↦ some hl_val(#(1337 : Int))) ∗ osShot γ (4 : Nat)))

theorem code_safe : semTyped GF 0 ∅ code (.fn (.fn .unit .unit) .unit) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [Exp.substMap_empty (M := TyMapStr)]
  simp only [exprInterp, code]
  swp_enter Hcl
  wp_alloc l with Hl
  wp_pures
  imod os_pending_alloc (A := Nat) (GF := GF) with ⟨%γ, Hpend⟩
  imod Iris.inv_alloc codeN (∅ : CoPset) (oneshotInv γ l) $$ [Hl Hpend] with #Hinv
  · inext
    unfold oneshotInv
    ileft
    isplitl [Hl]
    · iexact Hl
    · iexact Hpend
  imod Hcl
  imodintro
  simp only [typeInterp_fn, typeInterp_unit, funInterp_car, unitInterp_car]
  iintro %w !> Happ
  simp only [exprInterp]
  swp_pures
  iapply swp_bind_appR
  iapply ImpredInvariants.inv_open (N := codeN) (by simp) $$ Hinv
  iintro HI
  unfold oneshotInv
  swp_enter Hcl2
  icases HI with ⟨⟨>Hl, >Hpend⟩ | ⟨>Hl, >#Hshot⟩⟩
  · wp_store
    imod os_pending_shoot (4 : Nat) $$ Hpend with #Hshot
    imod Hcl2
    imodintro
    isplitl [Hl]
    · inext
      iright
      isplitl [Hl]
      · iexact Hl
      · iexact Hshot
    swp_pures
    iapply swp_bind_appR
    ispecialize Happ $$ %(hl_val(#()) : Val)
    iapply swp_wand $$ (Happ $$ %rfl)
    simp only [unitInterp_car]
    iintro %v %hv
    subst hv
    swp_pures
    iapply ImpredInvariants.inv_open (N := codeN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl3
    icases HI with ⟨⟨>Hl, >Hpend⟩ | ⟨>Hl, _⟩⟩
    · iexfalso
      iapply os_pending_shot_False $$ Hpend Hshot
    · simp only [assertE]
      wp_expr_simp
      wp_load
      wp_pures
      simp only [show ((hl_val(#(1337 : Int)) : Val) == hl_val(#(1337 : Int))) = true from rfl]
      wp_pures
      imod Hcl3
      imodintro
      isplitl [Hl]
      · inext
        iright
        isplitl [Hl]
        · iexact Hl
        · iexact Hshot
      · ipureintro
        trivial
  · wp_store
    imod Hcl2
    imodintro
    isplitl [Hl]
    · inext
      iright
      isplitl [Hl]
      · iexact Hl
      · iexact Hshot
    swp_pures
    iapply swp_bind_appR
    ispecialize Happ $$ %(hl_val(#()) : Val)
    iapply swp_wand $$ (Happ $$ %rfl)
    simp only [unitInterp_car]
    iintro %v %hv
    subst hv
    swp_pures
    iapply ImpredInvariants.inv_open (N := codeN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl3
    icases HI with ⟨⟨>Hl, >Hpend⟩ | ⟨>Hl, _⟩⟩
    · iexfalso
      iapply os_pending_shot_False $$ Hpend Hshot
    · simp only [assertE]
      wp_expr_simp
      wp_load
      wp_pures
      simp only [show ((hl_val(#(1337 : Int)) : Val) == hl_val(#(1337 : Int))) = true from rfl]
      wp_pures
      imod Hcl3
      imodintro
      isplitl [Hl]
      · inext
        iright
        isplitl [Hl]
        · iexact Hl
        · iexact Hshot
      · ipureintro
        trivial

end OneShot

/-! ## Agreement between the loop and its callback -/

section Agreement

def recCode : Exp :=
  hl(λ f,
     let l := ref(#(0 : Int));
     ((rec loop _ :=
        let x := !l;
        (if (f (λ _, !l))
         then (&(assertE hl((!l = x))); (l ← (x + #(1 : Int)); loop #()))
         else !l)) #()))

def agN : Namespace := nroot .@ "agreement"

variable [GhostVarG GF Int]

/-- The location and the loop's ghost half always agree; the callback can therefore only observe
the value the loop put there. -/
def agInv (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ n : Int, (l ↦ some hl_val(#n)) ∗ ghalf γ n)

theorem rec_code_safe :
    semTyped GF 0 ∅ recCode (.fn (.fn (.fn .unit .int) .bool) .int) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [Exp.substMap_empty (M := TyMapStr)]
  simp only [exprInterp, recCode]
  swp_pures
  iapply swp_value'
  simp only [typeInterp_fn, typeInterp_int, typeInterp_unit, typeInterp_bool, funInterp_car]
  iintro %w !> #Happ
  simp only [exprInterp]
  swp_pures
  iapply swp_bind_appR
  iapply swp_alloc hl_val(#(0 : Int))
  iintro %l Hl
  swp_pure
  swp_pure
  swp_pure
  iapply fupd_swp (E₂ := ⊤)
  imod ghalves_alloc (0 : Int) with ⟨%γ, Half1, Half2⟩
  imod Iris.inv_alloc agN ⊤ (agInv γ l) $$ [Hl Half2] with #Hinv
  · inext
    unfold agInv
    iexists (0 : Int)
    isplitl [Hl]
    · iexact Hl
    · iexact Half2
  imodintro
  generalize (0 : Int) = n
  iloeb as IH generalizing! %n
  swp_pure
  iapply swp_bind_appR
  iapply ImpredInvariants.inv_open (N := agN) (by simp) $$ Hinv
  iintro HI
  unfold agInv
  swp_enter Hcl
  icases HI with ⟨%m, >Hl, >Half2⟩
  wp_load
  icases ghalves_agree' $$ [Half1 Half2] with ⟨⟨Half1, Half2⟩, %hm⟩
  · isplitl [Half1]
    · iexact Half1
    · iexact Half2
  subst hm
  imod Hcl
  imodintro
  isplitl [Hl Half2]
  · inext
    iexists n
    isplitl [Hl]
    · iexact Hl
    · iexact Half2
  swp_pures
  iapply swp_bind_if
  swp_pure
  ispecialize Happ $$ %(hl_val(λ _, !#l) : Val)
  iapply swp_wand $$ (Happ $$ [#])
  · simp only [unitInterp_car]
    iintro %u !> %hu
    subst hu
    swp_pures
    iapply ImpredInvariants.inv_open (N := agN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl'
    icases HI with ⟨%k, >Hl, >Half⟩
    wp_load
    imod Hcl'
    imodintro
    isplitl [Hl Half]
    · inext
      iexists k
      isplitl [Hl]
      · iexact Hl
      · iexact Half
    · simp only [intInterp_car]
      iexists k
      ipureintro
      rfl
  simp only [boolInterp_car]
  iintro %v ⟨%b, %hv⟩
  subst hv
  cases b
  · swp_pures
    iapply ImpredInvariants.inv_open (N := agN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl2
    icases HI with ⟨%k, >Hl, >Half2⟩
    wp_load
    imod Hcl2
    imodintro
    isplitl [Hl Half2]
    · inext
      iexists k
      isplitl [Hl]
      · iexact Hl
      · iexact Half2
    · simp only [intInterp_car]
      iexists k
      ipureintro
      rfl
  · swp_pures
    iapply swp_bind_appR
    iapply ImpredInvariants.inv_open (N := agN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl2
    icases HI with ⟨%k, >Hl, >Half2⟩
    simp only [assertE]
    wp_expr_simp
    wp_load
    icases ghalves_agree' $$ [Half1 Half2] with ⟨⟨Half1, Half2⟩, %hk⟩
    · isplitl [Half1]
      · iexact Half1
      · iexact Half2
    subst hk
    wp_pures
    simp only [beq_self_eq_true]
    wp_pures
    imod Hcl2
    imodintro
    isplitl [Hl Half2]
    · inext
      iexists n
      isplitl [Hl]
      · iexact Hl
      · iexact Half2
    swp_pures
    iapply swp_bind_appR
    iapply ImpredInvariants.inv_open (N := agN) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl3
    icases HI with ⟨%k, >Hl, >Half2⟩
    wp_pures
    wp_store
    imod ghalves_update (n + 1) $$ Half1 Half2 with ⟨Half1, Half2⟩
    imod Hcl3
    imodintro
    isplitl [Hl Half2]
    · inext
      iexists (n + 1)
      isplitl [Hl]
      · iexact Hl
      · iexact Half2
    swp_pure
    swp_pure
    iapply IH $$ %(n + 1) Half1

end Agreement

/-! ## Two colours that never collide -/

section RedBlue

inductive Colour where
  | red
  | blue
  deriving DecidableEq, Repr

abbrev NatMap (V : Type) := Std.ExtTreeMap Nat V compare

def mkColourGen : Exp :=
  hl(let c := ref(#(0 : Int));
     (((λ _, let r := !c; (c ← (#(1 : Int) + r); r)),
       (λ _, let b := !c; (c ← (#(1 : Int) + b); b))),
      (λ r b, &(assertE hl(~(r = b))))))

def colourN : Namespace := nroot .@ "colour"

variable [GhostMapG GF Nat Colour NatMap]

/-- The counter hands out a fresh integer each time, and the ghost map records which generator
produced it. -/
def colourInv (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ (n : Nat) (M : NatMap Colour), (l ↦ some hl_val(#(n : Int))) ∗ agmapAuth γ M ∗
    ⌜∀ k : Nat, (get? M k).isSome → k < n⌝)

def redT (γ : GName) : SemType GF :=
  mkSemType (fun v => iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗
    agmapElem (H := NatMap) γ n Colour.red)) (fun _ => inferInstance)

def blueT (γ : GName) : SemType GF :=
  mkSemType (fun v => iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗
    agmapElem (H := NatMap) γ n Colour.blue)) (fun _ => inferInstance)

@[simp] theorem redT_car (γ : GName) (v : Val) :
    (redT (GF := GF) γ).car v = iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗
      agmapElem (H := NatMap) γ n Colour.red) := rfl

@[simp] theorem blueT_car (γ : GName) (v : Val) :
    (blueT (GF := GF) γ).car v = iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝ ∗
      agmapElem (H := NatMap) γ n Colour.blue) := rfl

theorem mkColourGen_safe :
    semTyped GF 0 ∅ mkColourGen
      (.exist (.exist (.prod (.prod (.fn .unit (.tVar 0)) (.fn .unit (.tVar 1)))
        (.fn (.tVar 0) (.fn (.tVar 1) .unit))))) := by
  unfold semTyped
  iintro %δ %γ #Hctx
  icases contextInterp_empty_inv γ δ $$ Hctx with %hγ
  subst hγ
  rw [Exp.substMap_empty (M := TyMapStr)]
  simp only [exprInterp, mkColourGen]
  swp_pures
  iapply swp_bind_appR
  iapply swp_alloc hl_val(#(0 : Int))
  iintro %l Hl
  swp_pures
  iapply fupd_swp (E₂ := ⊤)
  imod agmap_auth_alloc_empty (H := NatMap) (V := Colour) (GF := GF) with ⟨%γ, Hag⟩
  imod Iris.inv_alloc colourN ⊤ (colourInv (GF := GF) γ l) $$ [Hl Hag] with #Hinv
  · inext
    unfold colourInv
    iexists (0 : Nat), (∅ : NatMap Colour)
    isplitl [Hl]
    · iexact Hl
    isplitl [Hag]
    · iexact Hag
    · ipureintro
      intro k hk
      simp [LawfulPartialMap.get?_empty] at hk
  imodintro
  swp_enter Hcl
  wp_pures
  imod Hcl
  imodintro
  simp only [typeInterp_exist, typeInterp_prod, typeInterp_fn, typeInterp_unit, typeInterp_tVar,
    existInterp_car]
  iexists _
  isplitr
  · ipureintro; rfl
  iexists (blueT γ)
  iexists _
  isplitr
  · ipureintro; rfl
  iexists (redT γ)
  simp only [prodInterp_car, funInterp_car, varInterp, consEnv, unitInterp_car]
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · iexists _, _
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro %u !> %hu
      subst hu
      simp only [exprInterp]
      swp_pures
      iapply ImpredInvariants.inv_open (N := colourN) (by simp) $$ Hinv
      iintro HI
      unfold colourInv
      swp_enter Hcl2
      icases HI with ⟨%n, %M, >Hl, >Hauth, >%Hi⟩
      wp_load
      wp_pures
      wp_store
      have hnone : get? (M := NatMap) M n = none := by
        rcases h : get? (M := NatMap) M n with _ | c
        · rfl
        · exact absurd (Hi n (by simp [h])) (by omega)
      imod agmap_auth_insert (v := Colour.red) hnone $$ Hauth with ⟨Hauth, #Hred⟩
      imod Hcl2
      imodintro
      isplitl [Hl Hauth]
      · inext
        iexists (1 + n), (insert (M := NatMap) M n Colour.red)
        rw [show ((1 + n : Nat) : Int) = 1 + (n : Int) from by omega]
        isplitl [Hl]
        · iexact Hl
        isplitl [Hauth]
        · iexact Hauth
        · ipureintro
          intro k hk
          by_cases hkn : n = k
          · omega
          · rw [LawfulPartialMap.get?_insert_ne hkn] at hk
            exact Nat.lt_trans (Hi k hk) (by omega)
      · simp only [redT_car]
        iexists n
        isplitr
        · ipureintro; rfl
        · iexact Hred
    · iintro %u !> %hu
      subst hu
      simp only [exprInterp]
      swp_pures
      iapply ImpredInvariants.inv_open (N := colourN) (by simp) $$ Hinv
      iintro HI
      unfold colourInv
      swp_enter Hcl2
      icases HI with ⟨%n, %M, >Hl, >Hauth, >%Hi⟩
      wp_load
      wp_pures
      wp_store
      have hnone : get? (M := NatMap) M n = none := by
        rcases h : get? (M := NatMap) M n with _ | c
        · rfl
        · exact absurd (Hi n (by simp [h])) (by omega)
      imod agmap_auth_insert (v := Colour.blue) hnone $$ Hauth with ⟨Hauth, #Hblue⟩
      imod Hcl2
      imodintro
      isplitl [Hl Hauth]
      · inext
        iexists (1 + n), (insert (M := NatMap) M n Colour.blue)
        rw [show ((1 + n : Nat) : Int) = 1 + (n : Int) from by omega]
        isplitl [Hl]
        · iexact Hl
        isplitl [Hauth]
        · iexact Hauth
        · ipureintro
          intro k hk
          by_cases hkn : n = k
          · omega
          · rw [LawfulPartialMap.get?_insert_ne hkn] at hk
            exact Nat.lt_trans (Hi k hk) (by omega)
      · simp only [blueT_car]
        iexists n
        isplitr
        · ipureintro; rfl
        · iexact Hblue
  · simp only [redT_car]
    iintro %w !> ⟨%n, %hw, #Hred⟩
    subst hw
    simp only [exprInterp]
    swp_pures
    iapply swp_value'
    simp only [funInterp_car, varInterp, consEnv, blueT_car]
    iintro %u !> ⟨%m, %hu, #Hblue⟩
    subst hu
    simp only [exprInterp, assertE]
    swp_enter Hcl2
    wp_pures
    by_cases hnm : n = m
    · subst hnm
      icases agmap_elem_agree (H := NatMap) $$ Hred Hblue with %hc
      simp at hc
    · rw [show (!((hl_val(#(n : Int)) : Val) == hl_val(#(m : Int)))) = true from by
        simp [BEq.beq]; omega]
      wp_pures
      imod Hcl2
      imodintro
      simp only [unitInterp_car]
      ipureintro
      trivial

end RedBlue

end ProgramLogics.LogRel
