import LeanLR.ProgramLogics.HoareLib

/-!
# Program logics: Hoare logic

The port of `program_logics/hoare.v` (whose proofs live in `hoare_sol.v`): the rules derived from
the `HoareLib` interface, and the worked examples.

Where Rocq drives a proof by an explicit chain of `hoare_pure_step`s, the Lean proofs use
`iris-lean`'s `wp_pures` / `wp_rec` / `wp_bind` tactics, which do the same work. The
`hoare_pure_step` route is still available (`HoareLib` exports the whole `pure_step_*` family) and
`hoare_rec`, `hoare_if_true`, … below are proved that way, so the rule-based development the course
teaches is still what the file rests on.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic

namespace ProgramLogics

section Derived

variable {GF : BundledGFunctors}
variable {P Q R : IProp GF} {φ : Prop}

/-! ## Derived entailment rules -/

theorem ent_weakening (Q : IProp GF) (h : P ⊢ R) : iprop(P ∧ Q) ⊢ R := and_elim_l.trans h

theorem ent_true (P : IProp GF) : P ⊢ iprop(True) := true_intro

theorem ent_false (P : IProp GF) : (iprop(False) : IProp GF) ⊢ P := false_elim

theorem ent_and_comm (P Q : IProp GF) : iprop(P ∧ Q) ⊢ iprop(Q ∧ P) :=
  and_intro and_elim_r and_elim_l

theorem ent_or_comm (P Q : IProp GF) : iprop(P ∨ Q) ⊢ iprop(Q ∨ P) :=
  or_elim or_intro_r or_intro_l

theorem ent_all_comm {X : Type} (Φ : X → X → IProp GF) :
    iprop(∀ x, ∀ y, Φ x y) ⊢ iprop(∀ y, ∀ x, Φ x y) := by
  iintro H %y %x
  iapply H

theorem ent_exist_comm {X : Type} (Φ : X → X → IProp GF) :
    iprop(∃ x, ∃ y, Φ x y) ⊢ iprop(∃ y, ∃ x, Φ x y) := by
  iintro ⟨%x, %y, H⟩
  iexists y, x
  iexact H

end Derived

/-! ## Derived Hoare rules -/

section DerivedHoare

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {P Q : IProp GF} {Φ Ψ : Val → IProp GF} {φ : Prop}

theorem hoare_con_pre {e : Exp} (hpre : P ⊢ Q) (h : hoare Q e Φ) : hoare P e Φ :=
  hoare_con hpre (fun _ => ent_refl _) h

theorem hoare_con_post {e : Exp} (hpost : ∀ v, Ψ v ⊢ Φ v) (h : hoare P e Ψ) : hoare P e Φ :=
  hoare_con (ent_refl _) hpost h

theorem hoare_value_con (v : Val) (h : P ⊢ Φ v) : hoare P (Exp.val v) Φ :=
  hoare_con_pre h (hoare_value v Φ)

theorem hoare_value' (P : IProp GF) (v : Val) :
    hoare P (Exp.val v) (fun w => iprop(P ∗ ⌜w = v⌝)) := by
  refine hoare_value_con v ?_
  iintro H
  isplitl [H]
  · iexact H
  · ipureintro; rfl

/-- `rec: f x := e` applied to a value beta-reduces. -/
theorem hoare_rec (f x : Binder) (e : Exp) (v : Val)
    (h : hoare P ((e.subst f (.rec_ f x e)).subst x v) Φ) :
    hoare P hl(v(rec &f &x := &e) &v) Φ :=
  hoare_pure_step' (pure_step_beta f x e v) h

/-- `let: x := v in e`, i.e. an anonymous-recursion application. -/
theorem hoare_let (x : Binder) (e : Exp) (v : Val)
    (h : hoare P (e.subst x v) Φ) :
    hoare P hl(v(λ &x, &e) &v) Φ :=
  hoare_rec .anon x e v h

theorem hoare_if_true (e₁ e₂ : Exp) (h : hoare P e₁ Φ) :
    hoare P hl(if #true then &e₁ else &e₂) Φ :=
  hoare_pure_step' (pure_step_if_true e₁ e₂) h

theorem hoare_if_false (e₁ e₂ : Exp) (h : hoare P e₂ Φ) :
    hoare P hl(if #false then &e₁ else &e₂) Φ :=
  hoare_pure_step' (pure_step_if_false e₁ e₂) h

theorem hoare_add (z₁ z₂ : Int) :
    hoare (GF := GF) iprop(True) hl(#z₁ + #z₂)
      (fun v => iprop(⌜v = hl_val(#(z₁ + z₂))⌝)) := by
  refine hoare_pure_step' (pure_step_add z₁ z₂) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

theorem hoare_sub (z₁ z₂ : Int) :
    hoare (GF := GF) iprop(True) hl(#z₁ - #z₂)
      (fun v => iprop(⌜v = hl_val(#(z₁ - z₂))⌝)) := by
  refine hoare_pure_step' (pure_step_sub z₁ z₂) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

theorem hoare_mul (z₁ z₂ : Int) :
    hoare (GF := GF) iprop(True) hl(#z₁ * #z₂)
      (fun v => iprop(⌜v = hl_val(#(z₁ * z₂))⌝)) := by
  refine hoare_pure_step' (pure_step_mul z₁ z₂) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

/-- A pure precondition may be moved into the meta level. -/
theorem hoare_pure_pre {e : Exp} : hoare iprop(⌜φ⌝) e Φ ↔ (φ → hoare iprop(True) e Φ) := by
  constructor
  · intro h hφ
    exact hoare_con_pre (ent_prove_pure _ hφ) h
  · intro h
    refine hoare_pure (ent_refl _) fun hφ => ?_
    exact hoare_con_pre (ent_true _) (h hφ)

/-! ## Example: Fibonacci -/

def fib : Val := hl_val(
  rec fib n :=
    if n = #0 then #0
    else if n = #1 then #1
    else fib (n - #1) + fib (n - #2))

/-- The Lean-level Fibonacci function that `fib` is proved to compute. -/
def Fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => Fib (n + 1) + Fib n

theorem fib_zero :
    hoare (GF := GF) iprop(True) hl(&fib #(0 : Int))
      (fun v => iprop(⌜v = hl_val(#(0 : Int))⌝)) := by
  unfold hoare
  iintro _
  wp_rec
  wp_pures
  simp
  wp_pures
  ipureintro; rfl

theorem fib_one :
    hoare (GF := GF) iprop(True) hl(&fib #(1 : Int))
      (fun v => iprop(⌜v = hl_val(#(1 : Int))⌝)) := by
  unfold hoare
  iintro _
  wp_rec
  wp_pures
  rw [show (hl_val(#(1 : Int)) == hl_val(#(0 : Int))) = false from by decide]
  wp_pures
  simp
  wp_pures
  ipureintro; rfl

/-! ## Separation logic -/

/-- Two points-to assertions for the same location are contradictory, so separated points-to
assertions are for distinct locations. -/
theorem ent_pointsto_disj (l l' : Loc) (v w : Val) :
    iprop((l ↦ some v) ∗ (l' ↦ some w)) ⊢ iprop(⌜l ≠ l'⌝) := by
  iintro ⟨H1, H2⟩
  icases pointsTo_ne $$ H1 H2 with %hne
  ipureintro; exact hne

theorem ent_sep_exists' {X : Type} (Φ : X → IProp GF) (P : IProp GF) :
    iprop((∃ x, Φ x) ∗ P) ⊣⊢ iprop(∃ x, Φ x ∗ P) := by
  constructor
  · exact ent_exists_sep Φ P
  · iintro ⟨%x, HΦ, HP⟩
    isplitl [HΦ]
    · iexists x; iexact HΦ
    · iexact HP

theorem hoare_pure_pre_sep_l {e : Exp} (h : φ → hoare Q e Φ) :
    hoare iprop(⌜φ⌝ ∗ Q) e Φ := by
  refine hoare_pure (ent_sep_weaken _ _) fun hφ => ?_
  exact hoare_con_pre (sep_comm.mp.trans (ent_sep_weaken _ _)) (h hφ)

/-! ### Example: chains -/

/-- `chainPre n l r` is a chain of exactly `n` pointers from `l` to `r`. -/
def chainPre : Nat → Loc → Loc → IProp GF
  | 0, l, r => iprop(⌜l = r⌝)
  | n + 1, l, r => iprop(∃ t : Loc, (l ↦ some hl_val(#t)) ∗ chainPre n t r)

/-- `chain l r` is a non-empty chain of pointers from `l` to `r`. -/
def chain (l r : Loc) : IProp GF := iprop(∃ n : Nat, ⌜n > 0⌝ ∗ chainPre n l r)

theorem chain_single (l r : Loc) : iprop(l ↦ some hl_val(#r)) ⊢ chain (GF := GF) l r := by
  unfold chain
  iintro Hl
  iexists 1
  isplitr [Hl]
  · ipureintro; omega
  · simp only [chainPre]
    iexists r
    isplitl [Hl]
    · iexact Hl
    · ipureintro; rfl

theorem chain_cons (l r t : Loc) :
    iprop((l ↦ some hl_val(#r)) ∗ chain r t) ⊢ chain (GF := GF) l t := by
  unfold chain
  iintro ⟨Hl, %n, %hn, Hc⟩
  iexists (n + 1)
  isplitr [Hl Hc]
  · ipureintro; omega
  · simp only [chainPre]
    iexists r
    isplitl [Hl]
    · iexact Hl
    · iexact Hc

theorem chainPre_trans (n m : Nat) (l r t : Loc) :
    iprop(chainPre n l r ∗ chainPre m r t) ⊢ chainPre (GF := GF) (n + m) l t := by
  induction n generalizing l with
  | zero =>
    simp only [chainPre, Nat.zero_add]
    iintro ⟨%heq, Hc⟩
    subst heq
    iexact Hc
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 from by omega]
    simp only [chainPre]
    iintro ⟨⟨%u, Hl, Hc₁⟩, Hc₂⟩
    iexists u
    isplitl [Hl]
    · iexact Hl
    · iapply ih
      isplitl [Hc₁]
      · iexact Hc₁
      · iexact Hc₂

theorem chain_trans (l r t : Loc) :
    iprop(chain l r ∗ chain r t) ⊢ chain (GF := GF) l t := by
  unfold chain
  iintro ⟨⟨%n, %hn, Hc₁⟩, ⟨%m, %hm, Hc₂⟩⟩
  iexists (n + m)
  isplitr [Hc₁ Hc₂]
  · ipureintro; omega
  · iapply chainPre_trans
    isplitl [Hc₁]
    · iexact Hc₁
    · iexact Hc₂

/-- A cycle is a chain from a location back to itself. -/
def cycle (l : Loc) : IProp GF := chain l l

theorem chain_cycle (l r : Loc) :
    iprop(chain l r ∗ chain r l) ⊢ cycle (GF := GF) l := chain_trans l r l

/-! ### Assertions -/

/-- `assertE e` gets stuck unless `e` evaluates to `#true`. -/
def assertE (e : Exp) : Exp := hl(if &e then #() else (#(0 : Int) #(0 : Int)))

theorem hoare_assert {e : Exp} (h : hoare P e (fun v => iprop(⌜v = hl_val(#true)⌝))) :
    hoare P (assertE e) (fun v => iprop(⌜v = hl_val(#())⌝)) := by
  refine hoare_bind
    (EvContext.fill (Ectx := List ECtxItem)
      [ECtxItem.if hl(#()) hl(#(0 : Int) #(0 : Int))]) h fun v => ?_
  refine hoare_pure_pre.mpr fun hv => ?_
  subst hv
  refine hoare_if_true _ _ (hoare_value_con _ ?_)
  iintro _
  ipureintro; rfl

/-! ### Example: swap -/

def swap : Val := hl_val(λ l r, let t := !r; r ← !l; l ← t)

theorem swap_correct (l r : Loc) (v w : Val) :
    hoare iprop((l ↦ some v) ∗ (r ↦ some w)) hl(&swap #l #r)
      (fun _ => iprop((l ↦ some w) ∗ (r ↦ some v))) := by
  unfold hoare swap
  iintro ⟨Hl, Hr⟩
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_store
  wp_pures
  wp_store
  isplitl [Hl]
  · iexact Hl
  · iexact Hr

/-- Deciding a comparison of integer literals against a symbolic operand. -/
theorem val_int_beq_false {a b : Int} (h : a ≠ b) :
    (hl_val(#a) == hl_val(#b)) = false := by
  simp [BEq.beq]; omega

/-- The positive counterpart of `val_int_beq_false`. -/
theorem val_int_beq_true {a b : Int} (h : a = b) :
    (hl_val(#a) == hl_val(#b)) = true := by
  simp [BEq.beq]; omega

/-- Unfolding `fib` at a `z` that is neither `0` nor `1`. This is the pure-reduction half of
Rocq's `fib_succ`, split off so that the rest of the proof can stay at the level of Hoare
triples. -/
private theorem fib_unfold {P : IProp GF} {Φ : Val → IProp GF} (z : Int)
    (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (h : hoare P hl(&fib (#z - #(1 : Int)) + &fib (#z - #(2 : Int))) Φ) :
    hoare P hl(&fib #z) Φ := by
  unfold hoare at h ⊢
  refine h.trans ?_
  iintro H
  wp_rec
  wp_pures
  rw [val_int_beq_false hz₀]
  wp_if_false
  wp_pures
  rw [val_int_beq_false hz₁]
  wp_if_false
  iexact H

theorem fib_succ (z n m : Int)
    (h₁ : hoare (GF := GF) iprop(True) hl(&fib #(z - (1 : Int)))
      (fun v => iprop(⌜v = hl_val(#n)⌝)))
    (h₂ : hoare (GF := GF) iprop(True) hl(&fib #(z - (2 : Int)))
      (fun v => iprop(⌜v = hl_val(#m)⌝))) :
    hoare (GF := GF) iprop(⌜z > 1⌝) hl(&fib #z)
      (fun v => iprop(⌜v = hl_val(#(n + m))⌝)) := by
  refine hoare_pure_pre.mpr fun hz => ?_
  refine fib_unfold z (by omega) (by omega) ?_
  refine hoare_bind (EvContext.fill (Ectx := List ECtxItem)
      [.binOpR .plus hl(&fib (#z - #(1 : Int)))])
    (Ψ := fun v => iprop(⌜v = hl_val(#m)⌝)) ?_ ?_
  · refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.appR hl(&fib)])
      (Ψ := fun v => iprop(⌜v = hl_val(#(z - (2 : Int)))⌝)) (hoare_sub z 2) ?_
    intro v
    refine hoare_pure_pre.mpr fun hv => ?_
    subst hv
    exact h₂
  · intro v
    refine hoare_pure_pre.mpr fun hv => ?_
    subst hv
    refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.binOpL .plus hl_val(#m)])
      (Ψ := fun v => iprop(⌜v = hl_val(#n)⌝)) ?_ ?_
    · refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.appR hl(&fib)])
        (Ψ := fun v => iprop(⌜v = hl_val(#(z - (1 : Int)))⌝)) (hoare_sub z 1) ?_
      intro v
      refine hoare_pure_pre.mpr fun hv => ?_
      subst hv
      exact h₁
    · intro v
      refine hoare_pure_pre.mpr fun hv => ?_
      subst hv
      exact hoare_add n m

theorem fib_computes_Fib (n : Nat) :
    hoare (GF := GF) iprop(True) hl(&fib #((n : Int)))
      (fun v => iprop(⌜v = hl_val(#(Fib n))⌝)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact fib_zero
    | 1 => exact fib_one
    | (k + 2) =>
      have e₁ : ((k + 2 : Nat) : Int) - (1 : Int) = ((k + 1 : Nat) : Int) := by omega
      have e₂ : ((k + 2 : Nat) : Int) - (2 : Int) = ((k : Nat) : Int) := by omega
      have h₁ := e₁ ▸ ih (k + 1) (by omega)
      have h₂ := e₂ ▸ ih k (by omega)
      exact hoare_pure_pre.mp (fib_succ _ _ _ h₁ h₂) (by omega)

theorem hoare_eq_num (n m : Int) :
    hoare (GF := GF) iprop(⌜n = m⌝) hl(#n = #m) (fun u => iprop(⌜u = hl_val(#true)⌝)) := by
  refine hoare_pure_pre.mpr fun h => ?_
  refine hoare_pure_step' (pure_step_eq h) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

theorem hoare_neq_num (n m : Int) :
    hoare (GF := GF) iprop(⌜n ≠ m⌝) hl(#n = #m) (fun u => iprop(⌜u = hl_val(#false)⌝)) := by
  refine hoare_pure_pre.mpr fun h => ?_
  refine hoare_pure_step' (pure_step_neq h) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

/-! ## Example: factorial -/

def fac : Val :=
  hl_val(rec fac n := if n = #(0 : Int) then #(1 : Int) else n * fac (n - #(1 : Int)))

/-- The Lean-level factorial that `fac` is proved to compute. -/
def Fac : Nat → Int
  | 0 => 1
  | n + 1 => ((n + 1 : Nat) : Int) * Fac n

/-- Unfolding `fac` at a non-zero argument. -/
private theorem fac_unfold {P : IProp GF} {Φ : Val → IProp GF} (z : Int) (hz : z ≠ 0)
    (h : hoare P hl(#z * &fac (#z - #(1 : Int))) Φ) : hoare P hl(&fac #z) Φ := by
  unfold hoare at h ⊢
  refine h.trans ?_
  iintro H
  wp_rec
  wp_pures
  rw [val_int_beq_false hz]
  wp_if_false
  iexact H

theorem fac_computes_Fac (n : Nat) :
    hoare (GF := GF) iprop(True) hl(&fac #((n : Int)))
      (fun v => iprop(⌜v = hl_val(#(Fac n))⌝)) := by
  induction n with
  | zero =>
    unfold hoare
    iintro _
    wp_rec
    wp_pures
    rw [val_int_beq_true (show ((0 : Nat) : Int) = 0 from by omega)]
    wp_pures
    ipureintro; rfl
  | succ k ih =>
    refine fac_unfold _ (by omega) ?_
    refine hoare_bind (EvContext.fill (Ectx := List ECtxItem)
        [.binOpR .mult hl(#(((k + 1 : Nat) : Int)))])
      (Ψ := fun v => iprop(⌜v = hl_val(#(Fac k))⌝)) ?_ ?_
    · refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.appR hl(&fac)])
        (Ψ := fun v => iprop(⌜v = hl_val(#(((k + 1 : Nat) : Int) - (1 : Int)))⌝))
        (hoare_sub _ 1) ?_
      intro v
      refine hoare_pure_pre.mpr fun hv => ?_
      subst hv
      have e : ((k + 1 : Nat) : Int) - (1 : Int) = ((k : Nat) : Int) := by omega
      exact e ▸ ih
    · intro v
      refine hoare_pure_pre.mpr fun hv => ?_
      subst hv
      exact hoare_mul _ _

/-- With the subtraction on the left. -/
theorem ent_sep_exists {X : Type} (Φ : X → IProp GF) (P : IProp GF) :
    iprop(∃ x, Φ x ∗ P) ⊣⊢ iprop((∃ x, Φ x) ∗ P) := (ent_sep_exists' Φ P).symm

/-- A non-empty chain owns its first pointer. -/
private theorem chainPre_succ_pointsto (n : Nat) (l r : Loc) :
    chainPre (GF := GF) (n + 1) l r ⊢ iprop(∃ v : Val, l ↦ some v) := by
  simp only [chainPre]
  iintro ⟨%t, Hl, _⟩
  iexists hl_val(#t)
  iexact Hl

/-- Two chains cannot start at the same location. -/
theorem chain_sep_false (l r t : Loc) :
    iprop(chain (GF := GF) l r ∗ chain l t) ⊢ (False : IProp GF) := by
  unfold chain
  iintro ⟨⟨%n, %hn, H1⟩, ⟨%m, %hm, H2⟩⟩
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n =>
    cases m with
    | zero => exact absurd hm (by omega)
    | succ m =>
      icases chainPre_succ_pointsto n l r $$ H1 with ⟨%v, Hl1⟩
      icases chainPre_succ_pointsto m l t $$ H2 with ⟨%w, Hl2⟩
      iapply ent_pointsto_sep
      isplitl [Hl1]
      · iexact Hl1
      · iexact Hl2

/-- The frame rule in action — the second reference is untouched by `f`,
so its points-to survives the call and the assertion succeeds. -/
theorem frame_example (f : Val)
    (hf : ∀ l l' : Loc, hoare (GF := GF) iprop(l ↦ some hl_val(#(0 : Int)))
      hl(&f #l #l') (fun _ => iprop(l ↦ some hl_val(#(42 : Int))))) :
    hoare (GF := GF) iprop(True)
      hl(let x := ref(#(0 : Int)); let y := ref(#(42 : Int));
          &f x y; &(assertE hl(!x = !y)))
      (fun _ => iprop(True)) := by
  unfold hoare assertE
  unfold hoare at hf
  iintro _
  wp_alloc l with Hl
  wp_pures
  wp_alloc l' with Hl'
  wp_pures
  wp_bind (&f #l #l')
  ihave Hwp := hf l l' $$ Hl
  iapply ent_wp_wand $$ Hwp
  iintro %v Hl42
  wp_pures
  wp_load
  wp_load
  wp_pures
  rw [val_int_beq_true (show (42 : Int) = 42 from rfl)]
  wp_pures
  itrivial

/-- The triple form of `pure_step_quot`. -/
theorem hoare_quot (z₁ z₂ : Int) :
    hoare (GF := GF) iprop(True) hl(#z₁ / #z₂)
      (fun v => iprop(⌜v = hl_val(#(z₁.tdiv z₂))⌝)) := by
  refine hoare_pure_step' (pure_step_quot z₁ z₂) (hoare_value_con _ ?_)
  iintro _; ipureintro; rfl

/-! ## Example: Euclid's algorithm -/

def mod_val : Val := hl_val(λ a b, a - (a / b) * b)

def euclid : Val :=
  hl_val(rec euclid a b := if b = #(0 : Int) then a else euclid b (&mod_val a b))

theorem quot_diff (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a - a.tdiv b * b ∧ a - a.tdiv b * b < b := by
  rw [Int.tdiv_mul_self]
  refine ⟨?_, ?_⟩
  · have := Int.tmod_nonneg (a := a) b ha
    omega
  · have := Int.tmod_lt_of_pos a hb
    omega

/-- Strong induction on the non-negative integers. -/
theorem int_nonneg_ind {P : Int → Prop}
    (IH : ∀ x : Int, 0 ≤ x → (∀ y : Int, 0 ≤ y → y < x → P y) → P x) :
    ∀ x : Int, 0 ≤ x → P x := by
  suffices h : ∀ n : Nat, ∀ x : Int, 0 ≤ x → x.toNat = n → P x by
    intro x hx; exact h x.toNat x hx rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro x hx hxn
    refine IH x hx fun y hy hyx => ?_
    exact ihn y.toNat (by omega) y hy rfl

theorem gcd_step (b c k : Int) : Int.gcd b c = Int.gcd (b * k + c) b := by
  rw [Int.add_comm, Int.gcd_add_mul_left_left, Int.gcd_comm]

theorem mod_spec (a b : Int) :
    hoare (GF := GF) iprop(⌜b > 0⌝ ∧ ⌜a ≥ 0⌝) hl(&mod_val #a #b)
      (fun cv => iprop(∃ c k : Int,
        ⌜cv = hl_val(#c) ∧ 0 ≤ k ∧ a = b * k + c ∧ 0 ≤ c ∧ c < b⌝)) := by
  unfold hoare mod_val
  iintro ⟨%hb, %ha⟩
  wp_pures
  iexists (a - a.tdiv b * b)
  iexists (a.tdiv b)
  ipureintro
  obtain ⟨h₁, h₂⟩ := quot_diff a b (by omega) (by omega)
  refine ⟨rfl, ?_, ?_, h₁, h₂⟩
  · exact Int.tdiv_nonneg (by omega) (by omega)
  · rw [Int.mul_comm b (a.tdiv b)]
    omega

/-- Unfolding `euclid` at a non-zero second argument. -/
private theorem euclid_unfold {P : IProp GF} {Φ : Val → IProp GF} (a b : Int) (hb : b ≠ 0)
    (h : hoare P hl(&euclid #b (&mod_val #a #b)) Φ) : hoare P hl(&euclid #a #b) Φ := by
  unfold hoare at h ⊢
  refine h.trans ?_
  iintro H
  wp_rec
  wp_pures
  rw [val_int_beq_false hb]
  wp_if_false
  iexact H

theorem euclid_step_0 (a : Int) :
    hoare (GF := GF) iprop(True) hl(&euclid #a #(0 : Int))
      (fun v => iprop(⌜v = hl_val(#a)⌝)) := by
  unfold hoare euclid
  iintro _
  wp_rec
  wp_pures
  rw [val_int_beq_true (show (0 : Int) = 0 from rfl)]
  wp_pures
  ipureintro; rfl

theorem euclid_step_gt0 (a b : Int)
    (Ha : ∀ c : Int, hoare (GF := GF) iprop(⌜0 ≤ c ∧ c < b⌝) hl(&euclid #b #c)
      (fun d => iprop(⌜d = hl_val(#((Int.gcd b c : Nat) : Int))⌝))) :
    hoare (GF := GF) iprop(⌜b > 0⌝ ∧ ⌜a ≥ 0⌝) hl(&euclid #a #b)
      (fun c => iprop(⌜c = hl_val(#((Int.gcd a b : Nat) : Int))⌝)) := by
  refine hoare_pure (h := ?_) (φ := b > 0 ∧ a ≥ 0) ?_
  · iintro ⟨%hb, %ha⟩
    ipureintro
    exact ⟨hb, ha⟩
  intro ⟨hb, ha⟩
  refine hoare_con_pre (ent_true _) ?_
  refine euclid_unfold a b (by omega) ?_
  refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.appR hl(&euclid #b)])
    (Ψ := fun cv => iprop(∃ c k : Int,
      ⌜cv = hl_val(#c) ∧ 0 ≤ k ∧ a = b * k + c ∧ 0 ≤ c ∧ c < b⌝))
    (hoare_con_pre ?_ (mod_spec a b)) ?_
  · iintro _
    isplitl []
    · ipureintro; omega
    · ipureintro; omega
  · intro cv
    refine hoare_exist_pre fun c => ?_
    refine hoare_exist_pre fun k => ?_
    refine hoare_pure_pre.mpr fun ⟨hcv, hk, heq, hc0, hcb⟩ => ?_
    subst hcv
    refine hoare_con_post ?_ (hoare_con_pre ?_ (Ha c))
    · intro v
      iintro %hv
      ipureintro
      rw [hv, heq, ← gcd_step b c k]
    · iintro _
      ipureintro
      exact ⟨hc0, hcb⟩

theorem euclid_proof (a b : Int) :
    hoare (GF := GF) iprop(⌜0 ≤ a ∧ 0 ≤ b⌝) hl(&euclid #a #b)
      (fun c => iprop(⌜c = hl_val(#((Int.gcd a b : Nat) : Int))⌝)) := by
  refine hoare_pure_pre.mpr fun ⟨ha, hb⟩ => ?_
  suffices h : ∀ b : Int, 0 ≤ b → ∀ a : Int, 0 ≤ a →
      hoare (GF := GF) iprop(True) hl(&euclid #a #b)
        (fun c => iprop(⌜c = hl_val(#((Int.gcd a b : Nat) : Int))⌝)) by
    exact h b hb a ha
  refine int_nonneg_ind fun b hb ihb a ha => ?_
  by_cases hb0 : b = 0
  · subst hb0
    refine hoare_con_post ?_ (euclid_step_0 a)
    intro v
    iintro %hv
    ipureintro
    rw [hv, Int.gcd_zero_right, Int.natAbs_of_nonneg ha]
  · refine hoare_con_pre ?_ (euclid_step_gt0 a b fun c => ?_)
    · iintro _
      isplitl []
      · ipureintro; omega
      · ipureintro; omega
    · refine hoare_pure_pre.mpr fun ⟨hc0, hcb⟩ => ?_
      exact ihb c hc0 hcb b hb

theorem fac_zero :
    hoare (GF := GF) iprop(True) hl(&fac #(0 : Int))
      (fun v => iprop(⌜v = hl_val(#(1 : Int))⌝)) := by
  unfold hoare
  iintro _
  wp_rec
  wp_pures
  rw [val_int_beq_true (show (0 : Int) = 0 from rfl)]
  wp_pures
  ipureintro; rfl

theorem fac_succ (n m : Int)
    (h : hoare (GF := GF) iprop(True) hl(&fac #(n - (1 : Int)))
      (fun v => iprop(⌜v = hl_val(#m)⌝))) :
    hoare (GF := GF) iprop(⌜n > 0⌝) hl(&fac #n)
      (fun v => iprop(⌜v = hl_val(#(n * m))⌝)) := by
  refine hoare_pure_pre.mpr fun hn => ?_
  refine fac_unfold n (by omega) ?_
  refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.binOpR .mult hl(#n)])
    (Ψ := fun v => iprop(⌜v = hl_val(#m)⌝)) ?_ ?_
  · refine hoare_bind (EvContext.fill (Ectx := List ECtxItem) [.appR hl(&fac)])
      (Ψ := fun v => iprop(⌜v = hl_val(#(n - (1 : Int)))⌝)) (hoare_sub n 1) ?_
    intro v
    refine hoare_pure_pre.mpr fun hv => ?_
    subst hv
    exact h
  · intro v
    refine hoare_pure_pre.mpr fun hv => ?_
    subst hv
    exact hoare_mul n m

/-- Which is an `Instance` there so that `rewrite` can use it; Lean has no
setoid rewriting for entailment, so it is a plain lemma. -/
theorem hoare_proper {P₁ P₂ : IProp GF} {e : Exp} {Φ₁ Φ₂ : Val → IProp GF}
    (hP : P₁ ⊣⊢ P₂) (hΦ : ∀ v, Φ₁ v ⊢ Φ₂ v) (h : hoare P₁ e Φ₁) : hoare P₂ e Φ₂ :=
  hoare_con_post hΦ (hoare_con_pre hP.mpr h)

end DerivedHoare

end ProgramLogics
