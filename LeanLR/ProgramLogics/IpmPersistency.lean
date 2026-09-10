import LeanLR.ProgramLogics.HoareLib
import LeanLR.ProgramLogics.Hoare
import LeanLR.ProgramLogics.InvariantLib
import LeanLR.ProgramLogics.HeapLang.NoLater

/-!
# Persistency, and Hoare triples as propositions

`program_logics/ipm_persistency.v`. The Hoare triple of `HoareLib.lean` is a Lean `Prop`; here it
is internalised as `□ (P -∗ SWP e {{ Φ }})`, which is what lets a triple appear *inside* a
specification — as it must for a module whose operations are themselves described by triples
(`MutBit`, `SafeCounter`, `FlipInt` below).

It has to be the *sequential* WP: `SafeCounter`'s getter reads two cells and asserts they agree,
which is only provable if the invariant stays open across both reads. Each proof therefore opens
its invariant with `inv_open_swp` and then crosses to an ordinary mask-`∅` `wp` with
`wp_empty_swp`, after which `iris-lean`'s heap_lang tactics apply unchanged.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics.IpmPersistency

section Persistency

variable {GF : BundledGFunctors} {P : IProp GF}

/-- Duplication, derived from `ent_pers_and_sep` rather than assumed. -/
theorem ent_pers_dup' : iprop(□ P) ⊢ iprop(□ P ∗ □ P) :=
  (and_intro .rfl .rfl).trans (ent_pers_and_sep P iprop(□ P))

end Persistency

section Hoare

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {P : IProp GF} {Φ : Val → IProp GF}

/-- The internalised Hoare triple. Rocq writes it `{{ P }} e {{ Φ }}`; that notation is not
reproduced, since `{{`/`}}` are `iris-lean`'s texan-triple brackets. -/
def hoare (P : IProp GF) (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ swp .NotStuck ⊤ ⊤ e Φ))

/-! ### Peeling a projection off a module

Every specification below describes an operation as `fst(v) #()` or `snd(v) #()`, so every proof
starts by reducing the projection and the application. Those are pure steps, and the sequential WP
takes them with no later left over. -/

variable {s : Stuckness} {E : CoPset}

theorem swp_fst_app (v₁ v₂ w : Val) :
    swp s E E hl(v(&v₁) &w) Φ ⊢ swp s E E hl(fst(v((&v₁, &v₂))) &w) Φ :=
  swp_pure_step (pure_step_fill (ProgramLogic.fill [ECtxItem.appL w]) (pure_step_fst v₁ v₂))

theorem swp_snd_app (v₁ v₂ w : Val) :
    swp s E E hl(v(&v₂) &w) Φ ⊢ swp s E E hl(snd(v((&v₁, &v₂))) &w) Φ :=
  swp_pure_step (pure_step_fill (ProgramLogic.fill [ECtxItem.appL w]) (pure_step_snd v₁ v₂))

/-- `iapply swp_bind` needs the context as a function; these say that the two operand positions of
a binary operator are ones. -/
private instance ctx_binOpR (op : BinOp) (e₁ : Exp) :
    Language.Context (fun e => Exp.binop op e₁ e) :=
  show Language.Context (ProgramLogic.fill [ECtxItem.binOpR op e₁]) from inferInstance

private instance ctx_binOpL (op : BinOp) (v₂ : Val) :
    Language.Context (fun e => Exp.binop op e (Exp.ofVal v₂)) :=
  show Language.Context (ProgramLogic.fill [ECtxItem.binOpL op v₂]) from inferInstance

/-! ## An example: two calls, one specification

The triple is used *as a hypothesis* here, so this proof stays at the sequential-WP level and
sequences the two calls with `swp_bind`. -/

theorem double_int (f : Val) :
    hoare (GF := GF) iprop(True) hl(&f #())
        (fun v => iprop(∃ z : Int, ⌜v = hl_val(#z)⌝)) ⊢
      hoare iprop(True) hl(&f #() + &f #())
        (fun v => iprop(∃ z : Int, ⌜v = hl_val(#z)⌝)) := by
  unfold hoare
  iintro #Hf
  imodintro
  iintro _
  iapply swp_bind (fun e => Exp.binop .plus hl(&f #()) e)
  iapply swp_wand
  · iapply Hf
    itrivial
  iintro %v ⟨%z, %hz⟩
  subst hz
  iapply swp_bind (fun e => Exp.binop .plus e (Exp.ofVal hl_val(#z)))
  iapply swp_wand
  · iapply Hf
    itrivial
  iintro %w ⟨%z₂, %hz₂⟩
  subst hz₂
  iapply wp_empty_swp
  wp_pures
  iexists (z₂ + z)
  itrivial

/-! ## A mutable bit -/

def MyMutBit : Exp := hl(
  let x := ref(#(0 : Int));
  ((λ y, x ← #(1 : Int) - !x), (λ y, #(0 : Int) < !x)))

def MutBit (v : Val) : IProp GF :=
  iprop(hoare (iprop(True)) hl(fst(v(&v)) #()) (fun w => iprop(⌜w = hl_val(#())⌝)) ∗
    hoare (iprop(True)) hl(snd(v(&v)) #())
      (fun w => iprop(⌜w = hl_val(#true)⌝ ∨ ⌜w = hl_val(#false)⌝)))

def mutbitN : Namespace := nroot .@ "mutbit"

theorem MyMutBit_proof : ⊢ hoare (GF := GF) iprop(True) MyMutBit (fun v => MutBit v) := by
  unfold hoare MyMutBit
  imodintro
  iintro _
  iapply wp_empty_swp
  wp_alloc l with Hl
  wp_pures
  imod (Iris.inv_alloc mutbitN ∅
    iprop((l ↦ some hl_val(#(0 : Int))) ∨ (l ↦ some hl_val(#(1 : Int))))) $$ [Hl] with #Hinv
  · ileft
    iexact Hl
  imodintro
  unfold MutBit
  isplitl []
  · unfold hoare
    imodintro
    iintro _
    iapply swp_fst_app
    iapply inv_open_swp (N := mutbitN) (by simp) $$ Hinv
    iintro Hl
    iapply wp_empty_swp
    icases Hl with (Hl | Hl)
    · wp_pures
      wp_load
      wp_store
      simp only [show (1 : Int) - 0 = 1 from by decide]
      isplitl [Hl]
      · iright; iexact Hl
      · itrivial
    · wp_pures
      wp_load
      wp_store
      simp only [show (1 : Int) - 1 = 0 from by decide]
      isplitl [Hl]
      · ileft; iexact Hl
      · itrivial
  · unfold hoare
    imodintro
    iintro _
    iapply swp_snd_app
    iapply inv_open_swp (N := mutbitN) (by simp) $$ Hinv
    iintro Hl
    iapply wp_empty_swp
    icases Hl with (Hl | Hl)
    · wp_pures
      wp_load
      wp_pures
      isplitl [Hl]
      · ileft; iexact Hl
      · iright; ipureintro; decide
    · wp_pures
      wp_load
      wp_pures
      isplitl [Hl]
      · iright; iexact Hl
      · ileft; ipureintro; decide

/-! ## A safe counter

Two cells kept in step. The getter reads both and asserts they agree, which is why the invariant
has to stay open across both reads — the point of the sequential WP. -/

private theorem int_beq_self (a : Int) : (hl_val(#a) == hl_val(#a)) = true := by
  simp [BEq.beq]

def SafeCounter : Exp := hl(
  let c1 := ref(#(0 : Int));
  let c2 := ref(#(0 : Int));
  ((λ u, c1 ← !c1 + #(1 : Int); c2 ← !c2 + #(1 : Int)),
   (λ u, let v1 := !c1; let v2 := !c2; &(assertE hl(v1 = v2)); v1)))

def SafeCounter_safe (v : Val) : IProp GF :=
  iprop(hoare (iprop(True)) hl(fst(v(&v)) #()) (fun _ => iprop(True)) ∗
    hoare (iprop(True)) hl(snd(v(&v)) #()) (fun _ => iprop(True)))

def counterN : Namespace := nroot .@ "counter"

theorem SafeCounter_proof :
    ⊢ hoare (GF := GF) iprop(True) SafeCounter (fun v => SafeCounter_safe v) := by
  unfold hoare SafeCounter
  imodintro
  iintro _
  iapply wp_empty_swp
  wp_alloc l₁ with Hl₁
  wp_pures
  wp_alloc l₂ with Hl₂
  wp_pures
  imod (Iris.inv_alloc counterN ∅
    iprop(∃ n : Int, (l₁ ↦ some hl_val(#n)) ∗ (l₂ ↦ some hl_val(#n)))) $$ [Hl₁ Hl₂] with #Hinv
  · iexists (0 : Int)
    isplitl [Hl₁]
    · iexact Hl₁
    · iexact Hl₂
  imodintro
  unfold SafeCounter_safe
  isplitl []
  · unfold hoare
    imodintro
    iintro _
    iapply swp_fst_app
    iapply inv_open_swp (N := counterN) (by simp) $$ Hinv
    iintro ⟨%n, Hl₁, Hl₂⟩
    iapply wp_empty_swp
    wp_pures
    wp_load
    wp_pures
    wp_store
    wp_pures
    wp_load
    wp_pures
    wp_store
    isplitl [Hl₁ Hl₂]
    · iexists (n + 1)
      isplitl [Hl₁]
      · iexact Hl₁
      · iexact Hl₂
    · itrivial
  · unfold hoare
    imodintro
    iintro _
    iapply swp_snd_app
    iapply inv_open_swp (N := counterN) (by simp) $$ Hinv
    iintro ⟨%n, Hl₁, Hl₂⟩
    iapply wp_empty_swp
    unfold assertE
    wp_pures
    wp_load
    wp_pures
    wp_load
    wp_pures
    rw [int_beq_self n]
    wp_pures
    isplitl [Hl₁ Hl₂]
    · iexists n
      isplitl [Hl₁]
      · iexact Hl₁
      · iexact Hl₂
    · itrivial

/-! ## An abstract integer

The representation is a pair of non-negative integers standing for their difference; flipping the
pair negates the integer. The invariant carries a *pure* fact about the representation, which is
what the asserts consume. -/

private theorem int_le_true {a b : Int} (h : a ≤ b) : (decide (a ≤ b)) = true := by simp [h]

/-- The representation invariant: the cell holds a pair of non-negative integers. -/
def pureInv (v : Val) : Prop :=
  ∃ z₁ z₂ : Int, 0 ≤ z₁ ∧ 0 ≤ z₂ ∧ v = hl_val((#z₁, #z₂))

def MyInt : Val := hl_val(
  λ z, let x := ref(if #(0 : Int) < z then (#(0 : Int), z) else (-z, #(0 : Int)));
    ((λ y, let xv := !x; (if #(0 : Int) ≤ fst(xv) then #() else #(0 : Int) #(0 : Int));
        (if #(0 : Int) ≤ snd(xv) then #() else #(0 : Int) #(0 : Int)); snd(xv) - fst(xv)),
     (λ y, let xv := !x; x ← (snd(xv), fst(xv)))))

def FlipInt (v : Val) : IProp GF :=
  iprop(hoare (iprop(True)) hl(fst(v(&v)) #())
      (fun w => iprop(∃ z : Int, ⌜w = hl_val(#z)⌝)) ∗
    hoare (iprop(True)) hl(snd(v(&v)) #()) (fun w => iprop(⌜w = hl_val(#())⌝)))

def flipintN : Namespace := nroot .@ "flipint"

/-- The module body, once the representation has been chosen. Factored out so that the two
branches of the initial `if` share it. -/
private theorem MyInt_tail (u : Val) (hu : pureInv u) :
    iprop(True) ⊢ (WP hl(let x := ref(v(&u));
        ((λ y, let xv := !x; (if #(0 : Int) ≤ fst(xv) then #() else #(0 : Int) #(0 : Int));
            (if #(0 : Int) ≤ snd(xv) then #() else #(0 : Int) #(0 : Int)); snd(xv) - fst(xv)),
         (λ y, let xv := !x; x ← (snd(xv), fst(xv)))))
      @ Stuckness.NotStuck ; (∅ : CoPset) {{ (fun v => FlipInt v) }} : IProp GF) := by
  iintro _
  wp_alloc l with Hl
  wp_pures
  imod (Iris.inv_alloc flipintN ∅
    iprop(∃ w : Val, (l ↦ some w) ∗ ⌜pureInv w⌝)) $$ [Hl] with #Hinv
  · iexists u
    isplitl [Hl]
    · iexact Hl
    · ipureintro; exact hu
  imodintro
  unfold FlipInt
  isplitl []
  · unfold hoare
    imodintro
    iintro _
    iapply swp_fst_app
    iapply inv_open_swp (N := flipintN) (by simp) $$ Hinv
    iintro ⟨%w, Hl, %hw⟩
    obtain ⟨z₁, z₂, hz₁, hz₂, rfl⟩ := hw
    iapply wp_empty_swp
    wp_pures
    wp_load
    wp_pures
    rw [int_le_true hz₁]
    wp_pures
    rw [int_le_true hz₂]
    wp_pures
    isplitl [Hl]
    · iexists hl_val((#z₁, #z₂))
      isplitl [Hl]
      · iexact Hl
      · ipureintro; exact ⟨z₁, z₂, hz₁, hz₂, rfl⟩
    · iexists (z₂ - z₁)
      itrivial
  · unfold hoare
    imodintro
    iintro _
    iapply swp_snd_app
    iapply inv_open_swp (N := flipintN) (by simp) $$ Hinv
    iintro ⟨%w, Hl, %hw⟩
    obtain ⟨z₁, z₂, hz₁, hz₂, rfl⟩ := hw
    iapply wp_empty_swp
    wp_pures
    wp_load
    wp_pures
    wp_store
    isplitl [Hl]
    · iexists hl_val((#z₂, #z₁))
      isplitl [Hl]
      · iexact Hl
      · ipureintro; exact ⟨z₂, z₁, hz₂, hz₁, rfl⟩
    · itrivial

theorem MyInt_proof (z : Int) :
    ⊢ hoare (GF := GF) iprop(True) hl(v(&MyInt) #z) (fun v => FlipInt v) := by
  unfold hoare MyInt
  imodintro
  iintro _
  iapply wp_empty_swp
  wp_pures
  by_cases hz : (0 : Int) < z
  · rw [show (decide ((0 : Int) < z)) = true from by simp [hz]]
    wp_pures
    iapply MyInt_tail hl_val((#(0 : Int), #z)) ⟨0, z, by omega, by omega, rfl⟩
    itrivial
  · rw [show (decide ((0 : Int) < z)) = false from by simp [hz]]
    wp_pures
    iapply MyInt_tail hl_val((#((-z : Int)), #(0 : Int))) ⟨-z, 0, by omega, by omega, rfl⟩
    itrivial

end Hoare

end ProgramLogics.IpmPersistency
