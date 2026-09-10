import LeanLR.ProgramLogics.Hoare

/-!
# Program logics: the Iris Proof Mode

The port of `program_logics/ipm.v`: the same separation-logic reasoning, first done by hand from
the rules of `HoareLib` (the `Primitive` section) and then with the proof mode.

`iris-lean`'s proof mode is the Lean counterpart of Rocq's IPM; the tactic names differ by an
`i`-prefixed lowercase convention (`iIntros`/`iSplitL`/`iDestruct` become `iintro`/`isplitl`/
`icases`), and `iFrame` becomes `iframe`. Nothing else about the file changes.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic

namespace ProgramLogics

/-! ## Without the proof mode

These are proved from the rules of `HoareLib` alone, as the exercise asks. -/

section Primitive

variable {GF : BundledGFunctors} {P Q R : IProp GF}

theorem ent_or_sep_dist (P Q R : IProp GF) :
    iprop((P ∨ Q) ∗ R) ⊢ iprop((P ∗ R) ∨ (Q ∗ R)) :=
  ent_wand_elim (ent_or_elim
    (ent_wand_intro (ent_or_introl _ _))
    (ent_wand_intro (ent_or_intror _ _)))

theorem ent_carry_res (P Q : IProp GF) : P ⊢ iprop(Q -∗ P ∗ Q) :=
  ent_wand_intro (ent_refl _)

theorem ent_comm_premise (P Q R : IProp GF) :
    iprop(Q -∗ P -∗ R) ⊢ iprop(P -∗ Q -∗ R) :=
  ent_wand_intro (ent_wand_intro
    ((((ent_sep_assoc iprop(Q -∗ P -∗ R) P Q).mpr.trans
        (ent_sep_split (ent_refl _) (ent_sep_comm P Q).mp)).trans
      (ent_sep_assoc iprop(Q -∗ P -∗ R) Q P).mp).trans
      (ent_wand_elim (ent_wand_elim (ent_refl iprop(Q -∗ P -∗ R))))))

theorem ent_sep_or_disj2 (P Q R : IProp GF) :
    iprop((P ∨ R) ∗ (Q ∨ R)) ⊢ iprop((P ∗ Q) ∨ R) :=
  (ent_or_sep_dist P R iprop(Q ∨ R)).trans
    (ent_or_elim
      (((ent_sep_comm P iprop(Q ∨ R)).mp.trans (ent_or_sep_dist Q R P)).trans
        (ent_or_elim
          ((ent_sep_comm Q P).mp.trans (ent_or_introl iprop(P ∗ Q) R))
          ((ent_sep_weaken R P).trans (ent_or_intror iprop(P ∗ Q) R))))
      ((ent_sep_weaken R iprop(Q ∨ R)).trans (ent_or_intror iprop(P ∗ Q) R)))

/-! ### Exercise 2, without the proof mode -/

theorem ent_lem1 (P Q : IProp GF) : (iprop(True) : IProp GF) ⊢ iprop(P -∗ Q -∗ P ∗ Q) :=
  ent_wand_intro (ent_wand_intro
    (ent_sep_split ((ent_sep_comm _ _).mp.trans (ent_sep_weaken P iprop(True))) (ent_refl Q)))

theorem ent_lem2 (P Q : IProp GF) : iprop(P ∗ (P -∗ Q)) ⊢ Q :=
  (ent_sep_comm _ _).mp.trans (ent_wand_elim (ent_refl iprop(P -∗ Q)))

theorem ent_lem3 (P Q R : IProp GF) : iprop(P ∨ Q) ⊢ iprop(R -∗ (P ∗ R) ∨ (Q ∗ R)) :=
  ent_wand_intro (ent_or_sep_dist P Q R)

end Primitive

/-! ## With the proof mode -/

section WithIpm

variable {GF : BundledGFunctors} {P Q R : IProp GF}

theorem or_elim' (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : iprop(P ∨ Q) ⊢ R := by
  iintro (HP | HQ)
  · iapply h₁ $$ HP
  · iapply h₂ $$ HQ

theorem or_intro_l' (P Q : IProp GF) : P ⊢ iprop(P ∨ Q) := by
  iintro HP
  ileft
  iexact HP

theorem or_sep (P Q R : IProp GF) : iprop((P ∨ Q) ∗ R) ⊢ iprop((P ∗ R) ∨ (Q ∗ R)) := by
  iintro ⟨(HP | HQ), HR⟩
  · ileft; isplitl [HP]
    · iexact HP
    · iexact HR
  · iright; isplitl [HQ]
    · iexact HQ
    · iexact HR

/-- Proving a pure Lean proposition inside the logic. -/
theorem prove_pure (P : IProp GF) : P ⊢ iprop(⌜42 > 0⌝) := by
  iintro _
  ipureintro
  omega

/-- Destructing an existential with a pure component. -/
theorem destruct_ex {X : Type} (p : X → Prop) (Φ : X → IProp GF)
    (hp : ∀ x, ¬ p x) : iprop(∃ x, ⌜p x⌝ ∗ Φ x) ⊢ (iprop(False) : IProp GF) := by
  iintro ⟨%x, %hx, _⟩
  exact (hp x hx).elim

theorem specialize_assum (P Q R : IProp GF) :
    ⊢ iprop(P -∗ R -∗ (P ∗ R -∗ (P ∗ R) ∨ (Q ∗ R)) -∗ (P ∗ R) ∨ (Q ∗ R)) := by
  iintro HP HR HW
  iapply HW
  isplitl [HP]
  · iexact HP
  · iexact HR

theorem specialize_nested (P Q R : IProp GF) :
    ⊢ iprop(P -∗ (P -∗ R) -∗ (R -∗ Q) -∗ Q) := by
  iintro HP HPR HRQ
  iapply HRQ
  iapply HPR $$ HP

theorem prove_existential (Φ : Nat → IProp GF) :
    ⊢ iprop(Φ 1337 -∗ ∃ n, ∃ m, ⌜n > 41⌝ ∗ Φ m) := by
  iintro HΦ
  iexists 42, 1337
  isplitr [HΦ]
  · ipureintro; omega
  · iexact HΦ

theorem specialize_universal (Φ : Nat → IProp GF) :
    ⊢ iprop((∀ n, ⌜n = 42⌝ -∗ Φ n) -∗ Φ 42) := by
  iintro HΦ
  iapply HΦ
  ipureintro; rfl

/-! ### The three entailment exercises, with the proof mode -/

theorem ent_lem1_ipm (P Q : IProp GF) : (iprop(True) : IProp GF) ⊢ iprop(P -∗ Q -∗ P ∗ Q) := by
  iintro _ HP HQ
  isplitl [HP]
  · iexact HP
  · iexact HQ

theorem ent_lem2_ipm (P Q : IProp GF) : iprop(P ∗ (P -∗ Q)) ⊢ Q := by
  iintro ⟨HP, HW⟩
  iapply HW $$ HP

theorem ent_lem3_ipm (P Q R : IProp GF) :
    iprop(P ∨ Q) ⊢ iprop(R -∗ (P ∗ R) ∨ (Q ∗ R)) := by
  iintro (HP | HQ) HR
  · ileft; isplitl [HP]
    · iexact HP
    · iexact HR
  · iright; isplitl [HQ]
    · iexact HQ
    · iexact HR

end WithIpm

/-! ## Linked lists

`ipm.v`'s linked-list library (its `Exercise 5` and `Exercise 6`), which `hoare_sol.v` also carries
in a proof-mode-free form. The representation predicate `is_ll xs v` says the heap holds the list
`xs` as a `none`/`some`-tagged chain of pairs starting at `v`. -/

section LinkedList

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

def is_ll : List Val → Val → IProp GF
  | [], v => iprop(⌜v = hl_val(none())⌝)
  | x :: xs, v => iprop(∃ (l : Loc) (w : Val),
      ⌜v = hl_val(some(#l))⌝ ∗ (l ↦ some hl_val((&x, &w))) ∗ is_ll xs w)

def new_ll : Val := hl_val(λ _, none())

def cons_ll : Val := hl_val(λ h l, some(ref((h, l))))

def head_ll : Val := hl_val(λ x, match x with | none() => #() | some(r) => fst(!r))

def tail_ll : Val := hl_val(λ x, match x with | none() => #() | some(r) => snd(!r))

def len_ll : Val :=
  hl_val(rec len x := match x with | none() => #(0 : Int) | some(r) => #(1 : Int) + len (snd(!r)))

def app_ll : Val :=
  hl_val(rec app x y :=
    match x with
    | none() => y
    | some(r) => let rs := !r; r ← (fst(rs), app (snd(rs)) y); some(r))

theorem new_ll_correct :
    hoare (GF := GF) iprop(True) hl(&new_ll #()) (fun v => is_ll [] v) := by
  unfold hoare new_ll is_ll
  iintro _
  wp_pures
  ipureintro; rfl

theorem cons_ll_correct (v x : Val) (xs : List Val) :
    hoare (GF := GF) (is_ll xs v) hl(&cons_ll &x &v) (fun u => is_ll (x :: xs) u) := by
  unfold hoare cons_ll
  iintro Hv
  wp_pures
  wp_alloc l with Hl
  wp_pures
  simp only [is_ll]
  iexists l
  iexists v
  isplitl []
  · ipureintro; rfl
  · isplitl [Hl]
    · iexact Hl
    · iexact Hv

theorem head_ll_correct (v x : Val) (xs : List Val) :
    hoare (GF := GF) (is_ll (x :: xs) v) hl(&head_ll &v) (fun w => iprop(⌜w = x⌝)) := by
  unfold hoare head_ll
  simp only [is_ll]
  iintro ⟨%l, %w, %hv, Hl, Hw⟩
  subst hv
  wp_pures
  wp_load
  wp_pures
  ipureintro; rfl

theorem tail_ll_correct (v x : Val) (xs : List Val) :
    hoare (GF := GF) (is_ll (x :: xs) v) hl(&tail_ll &v) (fun w => is_ll xs w) := by
  unfold hoare tail_ll
  simp only [is_ll]
  iintro ⟨%l, %w, %hv, Hl, Hw⟩
  subst hv
  wp_pures
  wp_load
  wp_pures
  iexact Hw

theorem len_ll_correct (xs : List Val) : ∀ v : Val,
    hoare (GF := GF) (is_ll xs v) hl(&len_ll &v)
      (fun w => iprop(⌜w = hl_val(#((xs.length : Int)))⌝ ∗ is_ll xs v)) := by
  induction xs with
  | nil =>
    intro v
    unfold hoare
    simp only [is_ll]
    iintro %hv
    subst hv
    wp_rec
    wp_pures
    isplitl []
    · ipureintro; rfl
    · ipureintro; rfl
  | cons x xs ih =>
    intro v
    unfold hoare at ih ⊢
    simp only [is_ll]
    iintro ⟨%l, %w, %hv, Hl, Hw⟩
    subst hv
    wp_rec
    wp_pures
    wp_load
    wp_pures
    wp_bind (&len_ll &w)
    ihave Hrec := ih w $$ Hw
    iapply ent_wp_wand $$ Hrec
    iintro %u ⟨%hu, Hw⟩
    subst hu
    wp_pures
    isplitl []
    · ipureintro
      simp
      omega
    · iexists l
      iexists w
      isplitl []
      · ipureintro; rfl
      · isplitl [Hl]
        · iexact Hl
        · iexact Hw

/-- The cell holding the head is handed back too. -/
theorem tail_ll_strengthened (v x : Val) (xs : List Val) :
    hoare (GF := GF) (is_ll (x :: xs) v) hl(&tail_ll &v)
      (fun w => iprop((∃ l : Loc, ⌜v = hl_val(some(#l))⌝ ∗ (l ↦ some hl_val((&x, &w)))) ∗
        is_ll xs w)) := by
  unfold hoare tail_ll
  simp only [is_ll]
  iintro ⟨%l, %w, %hv, Hl, Hw⟩
  subst hv
  wp_pures
  wp_load
  wp_pures
  isplitl [Hl]
  · iexists l
    isplitl []
    · ipureintro; rfl
    · iexact Hl
  · iexact Hw

theorem app_ll_correct (xs : List Val) : ∀ (ys : List Val) (v w : Val),
    hoare (GF := GF) iprop(is_ll xs v ∗ is_ll ys w) hl(&app_ll &v &w)
      (fun u => is_ll (xs ++ ys) u) := by
  induction xs with
  | nil =>
    intro ys v w
    unfold hoare
    simp only [is_ll]
    iintro ⟨%hv, Hw⟩
    subst hv
    wp_rec
    wp_pures
    simp only [List.nil_append]
    imodintro
    iexact Hw
  | cons x xs ih =>
    intro ys v w
    unfold hoare at ih ⊢
    simp only [is_ll]
    iintro ⟨⟨%l, %w', %hv, Hl, Hxs⟩, Hw⟩
    subst hv
    wp_rec
    wp_pures
    wp_load
    wp_pures
    wp_bind (&app_ll &w' &w)
    ihave Hrec := ih ys w' w $$ [Hxs Hw]
    · isplitl [Hxs]
      · iexact Hxs
      · iexact Hw
    iapply ent_wp_wand $$ Hrec
    iintro %u Hu
    wp_pures
    wp_store
    wp_pures
    simp only [is_ll, List.cons_append]
    iexists l
    iexists u
    isplitl []
    · ipureintro; rfl
    · isplitl [Hl]
      · iexact Hl
      · iexact Hu

/-! ### Pure steps under a weakest precondition -/

/-- The `rtc` closure of `ent_wp_pure_step`. -/
theorem ent_wp_pure_steps {e e' : Exp} {Φ : Val → IProp GF} (h : PureSteps e e') :
    WP e' {{ Φ }} ⊢ WP e {{ Φ }} := by
  induction h with
  | refl => exact ent_refl _
  | step hp _ ih => exact (ih.trans later_intro).trans (ent_later_wp_pure_step' hp Φ)

/-! ### Accessors: `lookup_ll`

`ipm.v`'s Exercise 6. The postcondition hands out the cell holding the `n`-th element together
with a *magic wand* that gives the list back once the cell has been written to — the accessor
pattern. -/

def lookup_ll : Val :=
  hl_val(rec lookup l i :=
    match l with
    | none() => none()
    | some(l) =>
        if i = #(0 : Int) then some(l)
        else let lv := !l; lookup (snd(lv)) (i - #(1 : Int)))

def lookup_ll_unsafe : Val :=
  hl_val(λ l i, match &lookup_ll l i with | none() => none() | some(l) => l)

theorem lookup_ll_correct (xs : List Val) : ∀ (lv : Val) (n : Nat),
    hoare (GF := GF) iprop(is_ll xs lv ∗ ⌜n < xs.length⌝) hl(&lookup_ll &lv #((n : Int)))
      (fun v => iprop(∃ (l : Loc) (next : Val), ⌜v = hl_val(some(#l))⌝ ∗
        (l ↦ some hl_val((&(xs[n]!), &next))) ∗
        (∀ w' : Val, (l ↦ some hl_val((&w', &next))) -∗ is_ll (xs.set n w') lv))) := by
  induction xs with
  | nil =>
    intro lv n
    unfold hoare
    iintro ⟨_, %hn⟩
    exact absurd hn (by simp)
  | cons x xs ih =>
    intro lv n
    unfold hoare at ih ⊢
    simp only [is_ll]
    iintro ⟨⟨%l, %w, %hlv, Hl, Hxs⟩, %hn⟩
    subst hlv
    cases n with
    | zero =>
      wp_rec
      wp_pures
      rw [val_int_beq_true (show ((0 : Nat) : Int) = 0 from by omega)]
      wp_pures
      rw [show (x :: xs)[0]! = x from rfl]
      imodintro
      iexists l
      iexists w
      isplitl []
      · ipureintro; rfl
      · isplitl [Hl]
        · iexact Hl
        · iintro %w' Hl'
          simp only [is_ll, List.set]
          iexists l
          iexists w
          isplitl []
          · ipureintro; rfl
          · isplitl [Hl']
            · iexact Hl'
            · iexact Hxs
    | succ k =>
      wp_rec
      wp_pures
      rw [val_int_beq_false (show ((k + 1 : Nat) : Int) ≠ 0 from by omega)]
      wp_pures
      wp_load
      wp_pures
      rw [show ((k + 1 : Nat) : Int) - 1 = ((k : Nat) : Int) from by omega]
      wp_bind (&lookup_ll &w #((k : Int)))
      ihave Hrec := ih w k $$ [Hxs]
      · isplitl [Hxs]
        · iexact Hxs
        · ipureintro
          simp at hn
          omega
      iapply ent_wp_wand $$ Hrec
      iintro %v ⟨%l', %next, %hv, Hl', Hback⟩
      subst hv
      rw [show (x :: xs)[k + 1]! = xs[k]! from rfl]
      iexists l'
      iexists next
      isplitl []
      · ipureintro; rfl
      · isplitl [Hl']
        · iexact Hl'
        · iintro %w' Hcell
          simp only [is_ll, List.set]
          iexists l
          iexists w
          isplitl []
          · ipureintro; rfl
          · isplitl [Hl]
            · iexact Hl
            · iapply Hback $$ Hcell

theorem lookup_ll_unsafe_correct (xs : List Val) (lv : Val) (n : Nat) :
    hoare (GF := GF) iprop(is_ll xs lv ∗ ⌜n < xs.length⌝) hl(&lookup_ll_unsafe &lv #((n : Int)))
      (fun v => iprop(∃ (l : Loc) (next : Val), ⌜v = hl_val(#l)⌝ ∗
        (l ↦ some hl_val((&(xs[n]!), &next))) ∗
        (∀ w' : Val, (l ↦ some hl_val((&w', &next))) -∗ is_ll (xs.set n w') lv))) := by
  unfold hoare lookup_ll_unsafe
  iintro ⟨Hll, %hn⟩
  wp_pures
  wp_bind (&lookup_ll &lv #((n : Int)))
  have Hll_spec := lookup_ll_correct (GF := GF) xs lv n
  unfold hoare at Hll_spec
  ihave Hrec := Hll_spec $$ [Hll]
  · isplitl [Hll]
    · iexact Hll
    · ipureintro; exact hn
  iapply ent_wp_wand $$ Hrec
  iintro %v ⟨%l, %next, %hv, Hl, Hback⟩
  subst hv
  wp_pures
  iexists l
  iexists next
  isplitl []
  · ipureintro; rfl
  · isplitl [Hl]
    · iexact Hl
    · imodintro
      iexact Hback

end LinkedList

end ProgramLogics
