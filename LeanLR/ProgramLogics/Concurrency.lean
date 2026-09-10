import LeanLR.ProgramLogics.Hoare
import Iris.Instances.Lib.Invariants
import Iris.Instances.Lib.GhostVar
import Iris.Algebra.Auth
import Iris.Algebra.Numbers

/-!
# Concurrency

`program_logics/concurrency_sol.v`. Unlike the rest of the second half of the course, this file is
stated over *upstream* Iris's heap_lang weakest precondition rather than the sequential one — a
forking program is not sequential — so `iris-lean`'s tactics apply to it unchanged, and the
invariant-opening rule needs its expression to be `Atomic`.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode

namespace ProgramLogics.Concurrency

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

/-- The file's own Hoare triple: the same internalised triple as `IpmPersistency.hoare`, but over
the concurrent weakest precondition. -/
def hoare (P : IProp GF) (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ WP e {{ Φ }}))

/-! ## Compare-and-set, and forking -/

def cas_example : Exp :=
  hl(let x := ref(#(0 : Int)); (cas(x, #(0 : Int), #(42 : Int)); !x))

theorem cas_example_spec :
    ⊢ hoare (GF := GF) iprop(True) cas_example (fun v => iprop(⌜v = hl_val(#(42 : Int))⌝)) := by
  unfold hoare cas_example
  imodintro
  iintro _
  wp_alloc l with Hl
  wp_cmpxchg_suc
  wp_pures
  wp_load
  ipureintro
  rfl

def fork_example : Exp :=
  hl(let x := ref(#(0 : Int)); fork(x ← #(42 : Int)))

theorem fork_example_spec :
    ⊢ hoare (GF := GF) iprop(True) fork_example (fun _ => iprop(True)) := by
  unfold hoare fork_example
  imodintro
  iintro _
  wp_alloc l with Hl
  wp_pures
  iapply wp_fork
  · inext
    itrivial
  · inext
    wp_store
    itrivial

/-! ## Opening an invariant around an atomic step

The concurrent rule needs `e` to be atomic: no other thread may observe the invariant broken. -/

theorem wp_inv_open {E : CoPset} {N : Namespace} {e : Exp} {P : IProp GF} {Φ : Val → IProp GF}
    (HN : ↑N ⊆ E)
    [Language.Atomic (State := HeapLang.State) ↑Stuckness.NotStuck e] :
    inv N P ⊢ iprop((▷ P -∗ WP e @ (E \ ↑N) {{ v, ▷ P ∗ Φ v }}) -∗ WP e @ E {{ Φ }}) := by
  iintro #Hinv Hcont
  iinv Hinv with HP Hcl
  ispecialize Hcont $$ HP
  iapply wp_wand $$ Hcont
  iintro %v ⟨HP, Hv⟩
  imod Hcl $$ HP
  imodintro
  iexact Hv

/-! ## Flipping a coin

Forking a thread that races to overwrite a location is a source of nondeterminism, and an
invariant is what a specification can say about the result. -/

def flip_coin : Exp :=
  hl(let coin := ref(#(0 : Int)); (fork(coin ← #(1 : Int)); !coin))

def coinN : Namespace := nroot .@ "coin"

def coinInv (l : Loc) : IProp GF :=
  iprop((l ↦ some hl_val(#(0 : Int)) : IProp GF) ∨ l ↦ some hl_val(#(1 : Int)))

theorem flip_coin_spec :
    ⊢ hoare (GF := GF) iprop(True) flip_coin
      (fun v => iprop(⌜v = hl_val(#(0 : Int))⌝ ∨ ⌜v = hl_val(#(1 : Int))⌝)) := by
  unfold hoare flip_coin
  imodintro
  iintro _
  wp_alloc l with Hl
  wp_pures
  imod inv_alloc coinN ⊤ (coinInv (GF := GF) l) $$ [Hl] with #Hinv
  · unfold coinInv
    ileft
    iexact Hl
  wp_apply wp_fork $$ [] []
  · wp_pures
    iinv Hinv with H
    unfold coinInv
    icases H with ⟨>Hl | >Hl⟩
    · wp_load
      isplitl [Hl]
      · ileft
        iexact Hl
      · ileft
        ipureintro
        rfl
    · wp_load
      isplitl [Hl]
      · iright
        iexact Hl
      · iright
        ipureintro
        rfl
  · iinv Hinv with H
    unfold coinInv
    icases H with ⟨>Hl | >Hl⟩
    · wp_store
      isplitl [Hl]
      · iright
        iexact Hl
      · itrivial
    · wp_store
      isplitl [Hl]
      · iright
        iexact Hl
      · itrivial

/-! ## A spin lock -/

def newlock : Val := hl_val(λ _, ref(#false))
def try_acquire : Val := hl_val(λ l, cas(l, #false, #true))
def acquire : Val := hl_val(rec acq l := if v(&try_acquire) l then #() else acq l)
def release : Val := hl_val(λ l, l ← #false)

def lockN : Namespace := nroot .@ "lock"

/-- The lock is free and holds the resource, or it is taken and someone else has it. -/
def lock_inv (l : Loc) (P : IProp GF) : IProp GF :=
  iprop(((l ↦ some hl_val(#false)) ∗ P) ∨ (l ↦ some hl_val(#true)))

def is_lock (v : Val) (P : IProp GF) : IProp GF :=
  iprop(∃ l : Loc, ⌜v = hl_val(#l)⌝ ∗ inv lockN (lock_inv l P))

instance is_lock_pers (v : Val) (P : IProp GF) : Persistent (is_lock v P) := by
  unfold is_lock; infer_instance

theorem newlock_spec (P : IProp GF) :
    ⊢ hoare P hl(v(&newlock) #()) (fun v => is_lock v P) := by
  unfold hoare newlock
  imodintro
  iintro HP
  wp_pures
  wp_alloc l with Hl
  imod inv_alloc lockN ⊤ (lock_inv l P) $$ [Hl HP] with #Hinv
  · unfold lock_inv
    ileft
    isplitl [Hl]
    · iexact Hl
    · iexact HP
  imodintro
  unfold is_lock
  iexists l
  isplitr
  · ipureintro; rfl
  · iexact Hinv

theorem try_acquire_spec (v : Val) (P : IProp GF) :
    ⊢ hoare (is_lock v P) hl(v(&try_acquire) &v)
      (fun w => iprop((⌜w = hl_val(#true)⌝ ∗ P) ∨ ⌜w = hl_val(#false)⌝)) := by
  unfold hoare try_acquire
  imodintro
  iintro Hlock
  unfold is_lock
  icases Hlock with ⟨%l, %hv, #Hinv⟩
  subst hv
  wp_pures
  wp_bind (cmpXchg(#l, #false, #true))
  iapply wp_inv_open (N := lockN) (by simp) $$ Hinv
  iintro H
  unfold lock_inv
  icases H with ⟨⟨>Hl, HP⟩ | >Hl⟩
  · wp_cmpxchg_suc
    isplitl [Hl]
    · imodintro
      inext
      iright
      iexact Hl
    · imodintro
      wp_pures
      ileft
      isplitr
      · ipureintro; rfl
      · iexact HP
  · wp_cmpxchg_fail
    isplitl [Hl]
    · imodintro
      inext
      iright
      iexact Hl
    · imodintro
      wp_pures
      iright
      ipureintro; rfl

theorem acquire_spec (v : Val) (P : IProp GF) :
    ⊢ hoare (is_lock v P) hl(v(&acquire) &v)
      (fun w => iprop(⌜w = hl_val(#())⌝ ∗ P)) := by
  unfold hoare
  imodintro
  iintro #Hlock
  iloeb as IH
  unfold acquire
  wp_pures
  wp_bind (v(&try_acquire) v(&v))
  ihave Hta := try_acquire_spec v P
  unfold hoare
  ispecialize Hta $$ Hlock
  iapply wp_wand $$ Hta
  iintro %w Hw
  icases Hw with ⟨⟨%hw, HP⟩ | %hw⟩
  · subst hw
    wp_pures
    isplitr
    · ipureintro; rfl
    · iexact HP
  · subst hw
    wp_pure
    iexact IH

theorem release_spec (v : Val) (P : IProp GF) :
    ⊢ hoare iprop(is_lock v P ∗ P) hl(v(&release) &v) (fun _ => iprop(True)) := by
  unfold hoare release
  imodintro
  iintro ⟨#Hlock, HP⟩
  wp_pures
  unfold is_lock
  icases Hlock with ⟨%l, %hv, #Hinv⟩
  subst hv
  iapply wp_inv_open (N := lockN) (by simp) $$ Hinv
  iintro H
  unfold lock_inv
  icases H with ⟨⟨>Hl, _⟩ | >Hl⟩
  · wp_store
    isplitl [Hl HP]
    · imodintro
      inext
      ileft
      isplitl [Hl]
      · iexact Hl
      · iexact HP
    · itrivial
  · wp_store
    isplitl [Hl HP]
    · imodintro
      inext
      ileft
      isplitl [Hl]
      · iexact Hl
      · iexact HP
    · itrivial

/-! ## Running a critical section -/

def with_lock : Val := hl_val(λ l e, (v(&acquire) l; let x := e #(); (v(&release) l; x)))

def with_lock' (e₁ e₂ : Exp) : Exp := hl(v(&with_lock) &e₁ (λ _, &e₂))

theorem with_lock_spec (Φ : Val → IProp GF) (l c : Val) (P : IProp GF) :
    ⊢@{IProp GF} is_lock l P -∗ (P -∗ WP hl(v(&c) #()) {{ v, P ∗ Φ v }}) -∗
      WP hl(v(&with_lock) v(&l) v(&c)) {{ Φ }} := by
  iintro #Hl Hcont
  unfold with_lock
  wp_pures
  wp_bind (v(&acquire) v(&l))
  ihave Hacq := acquire_spec l P
  unfold hoare
  ispecialize Hacq $$ Hl
  iapply wp_wand $$ Hacq
  iintro %v ⟨%hv, HP⟩
  subst hv
  wp_pures
  wp_bind (v(&c) #())
  ispecialize Hcont $$ HP
  iapply wp_wand $$ Hcont
  iintro %w ⟨HP, Hw⟩
  wp_pures
  wp_bind (v(&release) v(&l))
  ihave Hrel := release_spec l P
  unfold hoare
  ispecialize Hrel $$ [$Hl $HP]
  iapply wp_wand $$ Hrel
  iintro %u _
  wp_pures
  iexact Hw

/-! ## An exclusive token, and locks that hand it out -/

abbrev LockRF : COFE.OFunctorPre := constOF (Excl Unit)

class LockG (GF : BundledGFunctors) where [elemG : ElemG GF LockRF]

attribute [reducible, instance] LockG.elemG

section LockLemmas

variable [LockG GF] {γ : GName}

/-- The token that says the lock is held. -/
def locked (γ : GName) : IProp GF := iOwn (F := LockRF) γ (Excl.excl ())

theorem locked_alloc : ⊢ (iprop(|==> ∃ γ, locked (GF := GF) γ) : IProp GF) :=
  iOwn_alloc _ trivial

instance locked_timeless : Timeless (locked (GF := GF) γ) := by unfold locked; infer_instance

theorem locked_exclusive : ⊢@{IProp GF} locked γ -∗ locked γ -∗ False := by
  unfold locked
  iintro H1 H2
  icombine H1 H2 gives %Hv
  exact Hv.elim

end LockLemmas

section ExclSpinLock

variable [LockG GF] {γ : GName}

def is_excl_lock (v : Val) (γ : GName) (P : IProp GF) : IProp GF :=
  is_lock v iprop(locked γ ∗ P)

instance is_excl_lock_pers (v : Val) (P : IProp GF) : Persistent (is_excl_lock v γ P) := by
  unfold is_excl_lock; infer_instance

theorem newlock_spec' (P : IProp GF) :
    ⊢ hoare P hl(v(&newlock) #()) (fun v => iprop(∃ γ, is_excl_lock v γ P)) := by
  unfold hoare
  imodintro
  iintro HP
  imod locked_alloc (GF := GF) with ⟨%γ, Hlocked⟩
  ihave Hnl := newlock_spec iprop(locked (GF := GF) γ ∗ P)
  unfold hoare
  ispecialize Hnl $$ [Hlocked HP]
  · isplitl [Hlocked]
    · iexact Hlocked
    · iexact HP
  iapply wp_wand $$ Hnl
  iintro %v Hlock
  iexists γ
  unfold is_excl_lock
  iexact Hlock

theorem acquire_spec' (v : Val) (P : IProp GF) :
    ⊢ hoare (is_excl_lock v γ P) hl(v(&acquire) &v)
      (fun w => iprop(⌜w = hl_val(#())⌝ ∗ locked γ ∗ P)) := by
  unfold hoare
  imodintro
  iintro #Hlock
  ihave Hacq := acquire_spec v iprop(locked (GF := GF) γ ∗ P)
  unfold hoare is_excl_lock
  ispecialize Hacq $$ Hlock
  iapply wp_wand $$ Hacq
  iintro %w ⟨%hw, Hlocked, HP⟩
  isplitr
  · ipureintro; exact hw
  isplitl [Hlocked]
  · iexact Hlocked
  · iexact HP

theorem release_spec' (v : Val) (P : IProp GF) :
    ⊢ hoare iprop(is_excl_lock v γ P ∗ locked γ ∗ P) hl(v(&release) &v)
      (fun _ => iprop(True)) := by
  unfold hoare
  imodintro
  iintro ⟨#Hlock, Hlocked, HP⟩
  ihave Hrel := release_spec v iprop(locked (GF := GF) γ ∗ P)
  unfold hoare is_excl_lock
  ispecialize Hrel $$ [$Hlock Hlocked HP]
  · isplitl [Hlocked]
    · iexact Hlocked
    · iexact HP
  iexact Hrel

/-- The token really is exclusive: holding it, the lock cannot also be free. -/
theorem really_exclusive (v : Val) (P : IProp GF) :
    ⊢ hoare iprop(is_excl_lock v γ P ∗ locked γ)
      (assertE hl(!&v = #true)) (fun _ => iprop(True)) := by
  unfold hoare is_excl_lock is_lock assertE
  imodintro
  iintro ⟨⟨%l, %hv, #Hinv⟩, Hlocked⟩
  subst hv
  wp_bind (!#l)
  iapply wp_inv_open (N := lockN) (by simp) $$ Hinv
  iintro H
  unfold lock_inv
  icases H with ⟨⟨>Hl, >Hexcl, HP⟩ | >Hl⟩
  · iapply BI.false_elim
    iapply locked_exclusive $$ Hlocked Hexcl
  · wp_load
    isplitl [Hl]
    · imodintro
      inext
      iright
      iexact Hl
    · imodintro
      wp_pures
      simp only [show (hl_val(#true) == hl_val(#true)) = true from rfl]
      wp_pures
      itrivial

end ExclSpinLock

/-! ## Parallel composition

`comp e₁ e₂` runs `e₂` in a forked thread and spins until it signals completion. The exclusive
token rules out the state in which the flag is set but the second thread's postcondition has
already been taken. -/

def await : Val := hl_val(rec aw x := if !x then #() else aw x)

def comp : Val := hl_val(λ e1 e2,
  let r := ref(#false);
  (fork((e2 #(); r ← #true)); (e1 #(); v(&await) r)))

def parN : Namespace := nroot .@ "par"

theorem parallel_spec [LockG GF] (e1 e2 : Val) (Q1 Q2 : IProp GF) :
    ⊢@{IProp GF} WP hl(v(&e1) #()) {{ _v, Q1 }} -∗ WP hl(v(&e2) #()) {{ _v, Q2 }} -∗
      WP hl(v(&comp) v(&e1) v(&e2)) {{ _v, Q1 ∗ Q2 }} := by
  iintro He1 He2
  unfold comp
  wp_pures
  wp_alloc l with Hl
  wp_pures
  imod locked_alloc (GF := GF) with ⟨%γ, Hlocked⟩
  imod inv_alloc parN ⊤
    (iprop((l ↦ some hl_val(#false) : IProp GF) ∨
      ((l ↦ some hl_val(#true)) ∗ Q2) ∨ ((l ↦ some hl_val(#true)) ∗ locked γ))) $$ [Hl]
    with #Hinv
  · ileft
    iexact Hl
  wp_apply wp_fork $$ [-He2] [He2]
  · wp_pures
    wp_bind (v(&e1) #())
    iapply wp_wand $$ He1
    iintro %v HQ1
    wp_pures
    iloeb as IH generalizing Hlocked HQ1
    unfold await
    wp_pures
    wp_bind (!#l)
    iinv Hinv with H Hcl
    icases H with ⟨>Hl | ⟨>Hl, HQ2⟩ | ⟨>Hl, >Hex⟩⟩
    · wp_load
      imod Hcl $$ [Hl]
      · inext
        ileft
        iexact Hl
      imodintro
      wp_pure
      iapply IH $$ Hlocked HQ1
    · wp_load
      imod Hcl $$ [Hl Hlocked]
      · inext
        iright
        iright
        isplitl [Hl]
        · iexact Hl
        · iexact Hlocked
      imodintro
      wp_pures
      isplitl [HQ1]
      · iexact HQ1
      · iexact HQ2
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hlocked Hex
  · wp_bind (v(&e2) #())
    iapply wp_wand $$ He2
    iintro %v HQ2
    wp_pures
    iinv Hinv with H Hcl
    icases H with ⟨>Hl | ⟨>Hl, _⟩ | ⟨>Hl, _⟩⟩
    · wp_store
      imod Hcl $$ [Hl HQ2]
      · inext
        iright
        ileft
        isplitl [Hl]
        · iexact Hl
        · iexact HQ2
      itrivial
    · wp_store
      imod Hcl $$ [Hl HQ2]
      · inext
        iright
        ileft
        isplitl [Hl]
        · iexact Hl
        · iexact HQ2
      itrivial
    · wp_store
      imod Hcl $$ [Hl HQ2]
      · inext
        iright
        ileft
        isplitl [Hl]
        · iexact Hl
        · iexact HQ2
      itrivial

/-! ## A counter incremented by two threads -/

def inc_counter : Val := hl_val(λ l r, v(&with_lock) l (λ _, r ← !r + #(1 : Int)))

def parallel_counter : Exp :=
  hl(let r := ref(#(0 : Int));
     let l := v(&newlock) #();
     (v(&comp) (λ _, v(&inc_counter) l r) (λ _, v(&inc_counter) l r);
      v(&with_lock) l (λ _, !r)))

section Counter

variable [GhostVarG GF Nat]

/-- A ghost variable splits into halves like any fractional assertion. -/
theorem gvar_split_halves (γ : GName) (a : Nat) :
    ⊢@{IProp GF} (γ ↪VAR a) -∗
      (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR{.own (1 : Qp).half} a) := by
  iintro H
  iapply ghost_var_split γ a (1 : Qp).half (1 : Qp).half
  ieval (rewrite [Qp.half_add_half])
  iexact H

/-- The lock's resource: the counter holds the sum of the two threads' contributions, each
tracked by half of a ghost variable. -/
def counterInv (r : Loc) (γ₁ γ₂ : GName) : IProp GF :=
  iprop(∃ n₁ n₂ : Nat, (r ↦ some hl_val(#((n₁ : Int) + (n₂ : Int)))) ∗
    (γ₁ ↪VAR{.own (1 : Qp).half} n₁) ∗ (γ₂ ↪VAR{.own (1 : Qp).half} n₂))

theorem parallel_counter_spec [LockG GF] :
    ⊢ hoare (GF := GF) iprop(True) parallel_counter
      (fun v => iprop(⌜v = hl_val(#(2 : Int))⌝)) := by
  unfold hoare parallel_counter
  imodintro
  iintro _
  wp_alloc r with Hr
  imod ghost_var_alloc (GF := GF) (0 : Nat) with ⟨%γ₁, Hv1⟩
  imod ghost_var_alloc (GF := GF) (0 : Nat) with ⟨%γ₂, Hv2⟩
  icases gvar_split_halves γ₁ 0 $$ Hv1 with ⟨Hv11, Hv12⟩
  icases gvar_split_halves γ₂ 0 $$ Hv2 with ⟨Hv21, Hv22⟩
  wp_pures
  wp_bind (v(&newlock) #())
  ihave Hnl := newlock_spec (counterInv (GF := GF) r γ₁ γ₂)
  unfold hoare
  ispecialize Hnl $$ [Hr Hv11 Hv21]
  · unfold counterInv
    iexists 0
    iexists 0
    simp only [show ((0 : Nat) : Int) + ((0 : Nat) : Int) = 0 from by decide]
    iframe Hv11 Hv21
    iexact Hr
  iapply wp_wand $$ Hnl
  iintro %lk #Hlock
  wp_pures
  ihave Hpar : WP hl(v(&comp) (v(λ _, v(&inc_counter) v(&lk) #r))
        (v(λ _, v(&inc_counter) v(&lk) #r)))
      {{ _v, (γ₁ ↪VAR{.own (1 : Qp).half} (1 : Nat)) ∗
        (γ₂ ↪VAR{.own (1 : Qp).half} (1 : Nat)) }} $$ [Hv12 Hv22]
  · iapply parallel_spec $$ [Hv12] [Hv22]
    · wp_pures
      unfold inc_counter
      wp_pures
      wp_apply with_lock_spec $$ [$Hlock] [Hv12]
      iintro HI
      unfold counterInv
      icases HI with ⟨%n₁, %n₂, Hr, Hg1, Hg2⟩
      wp_pures
      wp_load
      wp_store
      icases ghost_var_agree γ₁ 0 _ n₁ _ $$ Hv12 Hg1 with %heq
      subst heq
      imod ghost_var_update_halves (1 : Nat) γ₁ 0 0 $$ Hv12 Hg1 with ⟨Hv12, Hg1⟩
      imodintro
      isplitl [Hr Hg1 Hg2]
      · iexists 1
        iexists n₂
        simp only [show ((0 : Nat) : Int) + (n₂ : Int) + 1 = ((1 : Nat) : Int) + (n₂ : Int) from
          by omega]
        iframe Hg1 Hg2
        iexact Hr
      · iexact Hv12
    · wp_pures
      unfold inc_counter
      wp_pures
      wp_apply with_lock_spec $$ [$Hlock] [Hv22]
      iintro HI
      unfold counterInv
      icases HI with ⟨%n₁, %n₂, Hr, Hg1, Hg2⟩
      wp_pures
      wp_load
      wp_store
      icases ghost_var_agree γ₂ 0 _ n₂ _ $$ Hv22 Hg2 with %heq
      subst heq
      imod ghost_var_update_halves (1 : Nat) γ₂ 0 0 $$ Hv22 Hg2 with ⟨Hv22, Hg2⟩
      imodintro
      isplitl [Hr Hg1 Hg2]
      · iexists n₁
        iexists 1
        simp only [show (n₁ : Int) + ((0 : Nat) : Int) + 1 = (n₁ : Int) + ((1 : Nat) : Int) from
          by omega]
        iframe Hg1 Hg2
        iexact Hr
      · iexact Hv22
  wp_bind (v(&comp) (v(λ _, v(&inc_counter) v(&lk) #r)) (v(λ _, v(&inc_counter) v(&lk) #r)))
  iapply wp_wand $$ Hpar
  iintro %w ⟨H1, H2⟩
  wp_pures
  wp_apply with_lock_spec $$ [$Hlock] [H1 H2]
  iintro HI
  unfold counterInv
  icases HI with ⟨%n₁, %n₂, Hr, Hg1, Hg2⟩
  wp_pures
  wp_load
  icases ghost_var_agree γ₁ 1 _ n₁ _ $$ H1 Hg1 with %h1
  icases ghost_var_agree γ₂ 1 _ n₂ _ $$ H2 Hg2 with %h2
  subst h1
  subst h2
  isplitl [Hr Hg1 Hg2]
  · iexists 1
    iexists 1
    iframe Hg1 Hg2
    iexact Hr
  · ipureintro
    rfl

end Counter

/-! ## A mutex

A lock together with the cell it guards: acquiring hands back both the contents and the function
that releases it. -/

def mkmutex : Val := hl_val(λ d, (v(&newlock) #(), ref(d)))

def acquire_mutex : Val :=
  hl_val(λ m, (v(&acquire) (fst(m)); (snd(m), (λ _, v(&release) (fst(m))))))

/-- Rocq writes this `l ↦: P`. -/
def pointsToPred (d : Loc) (P : Val → IProp GF) : IProp GF :=
  iprop(∃ v : Val, (d ↦ some v) ∗ P v)

def is_mutex (v : Val) (P : Val → IProp GF) : IProp GF :=
  iprop(∃ (l : Val) (d : Loc), ⌜v = hl_val((&l, #d))⌝ ∗ is_lock l (pointsToPred d P))

instance is_mutex_pers (v : Val) (P : Val → IProp GF) : Persistent (is_mutex v P) := by
  unfold is_mutex; infer_instance

theorem mkmutex_spec (P : Val → IProp GF) (v : Val) :
    ⊢ hoare (P v) hl(v(&mkmutex) &v) (fun w => is_mutex w P) := by
  unfold hoare mkmutex
  imodintro
  iintro HP
  wp_pures
  wp_alloc d with Hd
  wp_bind (v(&newlock) #())
  ihave Hnl := newlock_spec (pointsToPred (GF := GF) d P)
  unfold hoare
  ispecialize Hnl $$ [HP Hd]
  · unfold pointsToPred
    iexists v
    isplitl [Hd]
    · iexact Hd
    · iexact HP
  iapply wp_wand $$ Hnl
  iintro %lk Hlock
  wp_pures
  unfold is_mutex
  iexists lk
  iexists d
  isplitr
  · ipureintro; rfl
  · iexact Hlock

theorem acquire_mutex_spec (P : Val → IProp GF) (v : Val) :
    ⊢ hoare (is_mutex v P) hl(v(&acquire_mutex) &v)
      (fun w => iprop(∃ (d : Loc) (rl : Val), ⌜w = hl_val((#d, &rl))⌝ ∗ pointsToPred d P ∗
        hoare (pointsToPred d P) hl(v(&rl) #()) (fun _ => iprop(True)))) := by
  unfold hoare acquire_mutex is_mutex
  imodintro
  iintro ⟨%lk, %d, %hv, #Hlock⟩
  subst hv
  wp_pures
  wp_bind (v(&acquire) v(&lk))
  ihave Hacq := acquire_spec lk (pointsToPred (GF := GF) d P)
  unfold hoare
  ispecialize Hacq $$ Hlock
  iapply wp_wand $$ Hacq
  iintro %w ⟨%hw, Hd⟩
  subst hw
  wp_pures
  iexists d
  iexists hl_val(λ _, v(&release) (fst(v((&lk, #d)))))
  isplitr
  · ipureintro; rfl
  isplitl [Hd]
  · iexact Hd
  iintro !> !> Hd
  wp_pures
  ihave Hrel := release_spec lk (pointsToPred (GF := GF) d P)
  unfold hoare
  ispecialize Hrel $$ [$Hlock $Hd]
  iexact Hrel

/-! ## Waiting, and unwrapping an option -/

def await'' : Val := hl_val(rec aw f := if f #() then #() else aw f)

def unwrap : Val := hl_val(λ o, match o with | injl(_) => &(assertE hl(#false)) | injr(a) => a)

theorem await'_spec (e : Exp) (P : IProp GF) (Q : Val → IProp GF) :
    hoare P e (fun v => iprop((⌜v = hl_val(#true)⌝ ∗ Q hl_val(#())) ∨ (⌜v = hl_val(#false)⌝ ∗ P)))
      ⊢ hoare P hl(v(&await'') (v(λ _, &e))) (fun v => Q v) := by
  unfold hoare
  iintro #Hh
  imodintro
  iintro HP
  iloeb as IH generalizing HP
  unfold await''
  wp_pures
  wp_bind (&e)
  ispecialize Hh $$ HP
  iapply wp_wand $$ Hh
  iintro %v Hv
  icases Hv with ⟨⟨%hv, HQ⟩ | ⟨%hv, HP⟩⟩
  · subst hv
    wp_pures
    iexact HQ
  · subst hv
    wp_pure
    iapply IH $$ HP

theorem unwrap_spec (v w : Val) (Φ : Val → IProp GF) (hv : v = hl_val(injr(&w))) :
    Φ w ⊢ WP hl(v(&unwrap) &v) {{ Φ }} := by
  subst hv
  unfold unwrap
  iintro HΦ
  wp_pures
  iexact HΦ

/-! ## Channels

A channel is a triple: a lock for the sending side, a lock for the receiving side, and a cell
holding the datum in flight. The `assert` is spelled out for the same reason as in
`LaterLoeb.lean`'s `E` — `Exp.subst` does not descend below a `Val`. -/

def newchan : Val := hl_val(λ _, ((v(&newlock) #(), v(&newlock) #()), ref(injl(#()))))

def send : Val := hl_val(λ c v,
  let l_s := fst(fst(c));
  let l_r := snd(fst(c));
  let data := snd(c);
  v(&with_lock) l_s (λ _,
    ((if !data = injl(#()) then #() else #(0 : Int) #(0 : Int));
      (data ← injr(v);
        v(&await'') (λ _, !data = injl(#()))))))

def receive : Val := hl_val(λ c,
  let l_s := fst(fst(c));
  let l_r := snd(fst(c));
  let data := snd(c);
  v(&with_lock) l_r (λ _,
    (v(&await'') (λ _, ~(!data = injl(#())));
      (let k := v(&unwrap) (!data);
        (data ← injl(#()); k)))))

section ChannelSpec

variable [LockG GF] (Pc : Val → IProp GF) [∀ v, Persistent (Pc v)]

def channelN : Namespace := nroot .@ "chan"

def is_sender (l_s : Val) (s1 : GName) : IProp GF := is_lock l_s (locked s1)
def is_receiver (l_r : Val) (r1 : GName) : IProp GF := is_lock l_r (locked r1)

/-- Four states: idle, the sender has written, the receiver has taken the datum, and the receiver
has acknowledged. -/
def channel_inv (data : Loc) (s1 s2 r1 r2 : GName) : IProp GF :=
  iprop((locked s2 ∗ locked r2 ∗ (data ↦ some hl_val(injl(#())))) ∨
    (locked s1 ∗ locked r2 ∗ (∃ v : Val, (data ↦ some hl_val(injr(&v))) ∗ Pc v)) ∨
    (locked s1 ∗ locked r1 ∗ (∃ v : Val, (data ↦ some hl_val(injr(&v))) ∗ Pc v)) ∨
    (locked s1 ∗ locked r2 ∗ (data ↦ some hl_val(injl(#())))))

instance is_sender_persistent (l_s : Val) (s1 : GName) :
    Persistent (is_sender (GF := GF) l_s s1) := by unfold is_sender; infer_instance
instance is_receiver_persistent (l_r : Val) (r1 : GName) :
    Persistent (is_receiver (GF := GF) l_r r1) := by unfold is_receiver; infer_instance

def is_channel (v : Val) : IProp GF :=
  iprop(∃ (l_s l_r : Val) (data : Loc) (s1 s2 r1 r2 : GName),
    ⌜v = hl_val(((&l_s, &l_r), #data))⌝ ∗ is_sender l_s s1 ∗ is_receiver l_r r1 ∗
      inv channelN (channel_inv Pc data s1 s2 r1 r2))

instance is_channel_persistent (v : Val) : Persistent (is_channel Pc v) := by
  unfold is_channel; infer_instance

omit [∀ v, Persistent (Pc v)] in
theorem newchan_spec :
    ⊢ hoare iprop(True) hl(v(&newchan) #()) (fun v => is_channel Pc v) := by
  unfold hoare newchan
  imodintro
  iintro _
  wp_pures
  wp_alloc data with Hdata
  imod locked_alloc (GF := GF) with ⟨%s1, Hs1⟩
  imod locked_alloc (GF := GF) with ⟨%s2, Hs2⟩
  imod locked_alloc (GF := GF) with ⟨%r1, Hr1⟩
  imod locked_alloc (GF := GF) with ⟨%r2, Hr2⟩
  imod inv_alloc channelN ⊤ (channel_inv Pc data s1 s2 r1 r2) $$ [Hdata Hs2 Hr2] with #Hinv
  · unfold channel_inv
    ileft
    iframe Hs2 Hr2
    iexact Hdata
  wp_bind (v(&newlock) #())
  ihave Hnl2 := newlock_spec (locked (GF := GF) r1)
  unfold hoare
  ispecialize Hnl2 $$ [Hr1]
  · iexact Hr1
  iapply wp_wand $$ Hnl2
  iintro %l_r #Lrecv
  wp_bind (v(&newlock) #())
  ihave Hnl1 := newlock_spec (locked (GF := GF) s1)
  unfold hoare
  ispecialize Hnl1 $$ [Hs1]
  · iexact Hs1
  iapply wp_wand $$ Hnl1
  iintro %l_s #Lsend
  wp_pures
  unfold is_channel
  iexists l_s
  iexists l_r
  iexists data
  iexists s1
  iexists s2
  iexists r1
  iexists r2
  isplitr
  · ipureintro; rfl
  unfold is_sender is_receiver
  iframe Lsend Lrecv Hinv

omit [∀ v, Persistent (Pc v)] in
theorem send_spec (v d : Val) :
    ⊢ hoare iprop(is_channel Pc v ∗ Pc d) hl(v(&send) &v &d)
      (fun w => iprop(⌜w = hl_val(#())⌝)) := by
  unfold hoare send is_channel
  imodintro
  iintro ⟨⟨%l_s, %l_r, %data, %s1, %s2, %r1, %r2, %hv, #Lsend, #Lrecv, #Hinv⟩, HP⟩
  subst hv
  wp_pures
  unfold is_sender
  wp_apply with_lock_spec $$ [$Lsend] [HP]
  iintro Hs1
  wp_pures
  wp_bind (!#data)
  iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
  iintro H
  unfold channel_inv
  icases H with ⟨⟨>Hs2, >Hr2, >Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩ | ⟨>Hs1', >Hr1, Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩⟩
  · wp_load
    isplitl [Hs2 Hr2 Hd]
    · imodintro
      inext
      ileft
      iframe Hs2 Hr2
      iexact Hd
    imodintro
    wp_pures
    simp only [show (hl_val(injl(#())) == hl_val(injl(#()))) = true from rfl]
    wp_pures
    wp_bind (#data ← v(injr(&d)))
    iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
    iintro H
    icases H with ⟨⟨>Hs2, >Hr2, >Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩ | ⟨>Hs1', >Hr1, Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩⟩
    · wp_store
      isplitl [Hs1 Hr2 Hd HP]
      · imodintro
        inext
        iright
        ileft
        iframe Hs1 Hr2
        iexists d
        isplitl [Hd]
        · iexact Hd
        · iexact HP
      imodintro
      wp_pures
      ihave Haw : hoare (locked (GF := GF) s2)
          hl(v(&await'') (v(λ _, (!#data = injl(#())))))
          (fun w => iprop(locked (GF := GF) s1 ∗ ⌜w = hl_val(#())⌝)) $$ []
      · iapply await'_spec
        unfold hoare
        imodintro
        iintro Hs2
        wp_pures
        wp_bind (!#data)
        iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
        iintro H
        icases H with ⟨⟨>Hs2', >Hr2, >Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩ | ⟨>Hs1', >Hr1, Hd⟩ |
          ⟨>Hs1', >Hr2, >Hd⟩⟩
        · iapply BI.false_elim
          iapply locked_exclusive $$ Hs2 Hs2'
        · icases Hd with ⟨%w, >Hd, Hpw⟩
          wp_load
          isplitl [Hs1' Hr2 Hd Hpw]
          · imodintro
            inext
            iright
            ileft
            iframe Hs1' Hr2
            iexists w
            isplitl [Hd]
            · iexact Hd
            · iexact Hpw
          imodintro
          wp_pure
          · simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
          iright
          isplitr
          · ipureintro
            trivial
          · iexact Hs2
        · icases Hd with ⟨%w, >Hd, Hpw⟩
          wp_load
          isplitl [Hs1' Hr1 Hd Hpw]
          · imodintro
            inext
            iright
            iright
            ileft
            iframe Hs1' Hr1
            iexists w
            isplitl [Hd]
            · iexact Hd
            · iexact Hpw
          imodintro
          wp_pure
          · simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
          iright
          isplitr
          · ipureintro
            trivial
          · iexact Hs2
        · wp_load
          isplitl [Hs2 Hr2 Hd]
          · imodintro
            inext
            ileft
            iframe Hs2 Hr2
            iexact Hd
          imodintro
          wp_pures
          simp only [show (hl_val(injl(#())) == hl_val(injl(#()))) = true from rfl]
          ileft
          isplitr
          · ipureintro
            trivial
          · isplitl [Hs1']
            · iexact Hs1'
            · ipureintro
              trivial
      unfold hoare
      iapply Haw $$ Hs2
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hs1 Hs1'
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hs1 Hs1'
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hs1 Hs1'
  · iapply BI.false_elim
    iapply locked_exclusive $$ Hs1 Hs1'
  · iapply BI.false_elim
    iapply locked_exclusive $$ Hs1 Hs1'
  · iapply BI.false_elim
    iapply locked_exclusive $$ Hs1 Hs1'

theorem receive_spec (v : Val) :
    ⊢ hoare (is_channel Pc v) hl(v(&receive) &v) (fun d => Pc d) := by
  unfold hoare receive is_channel
  imodintro
  iintro ⟨%l_s, %l_r, %data, %s1, %s2, %r1, %r2, %hv, #Lsend, #Lrecv, #Hinv⟩
  subst hv
  wp_pures
  unfold is_receiver
  wp_apply with_lock_spec $$ [$Lrecv] []
  iintro Hr1
  wp_pures
  wp_bind (v(&await'') (v(λ _, ~(!#data = injl(#())))))
  iloeb as IH generalizing Hr1
  unfold await''
  wp_pures
  wp_bind (!#data)
  iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
  iintro H
  unfold channel_inv
  icases H with ⟨⟨>Hs2', >Hr2', >Hd⟩ | ⟨>Hs1', >Hr2, Hd⟩ | ⟨>Hs1', >Hr1', Hd⟩ |
    ⟨>Hs1', >Hr2', >Hd⟩⟩
  · wp_load
    isplitl [Hs2' Hr2' Hd]
    · imodintro
      inext
      ileft
      iframe Hs2' Hr2'
      iexact Hd
    imodintro
    wp_pures
    simp only [show (!(hl_val(injl(#())) == hl_val(injl(#())))) = false from rfl]
    wp_pure
    iapply IH $$ Hr1
  · icases Hd with ⟨%w, >Hd, #Hpw⟩
    wp_load
    isplitl [Hs1' Hr1 Hd]
    · imodintro
      inext
      iright
      iright
      ileft
      iframe Hs1' Hr1
      iexists w
      isplitl [Hd]
      · iexact Hd
      · iexact Hpw
    imodintro
    wp_pure
    · simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    wp_pures
    simp only [show (!(hl_val(injr(&w)) == hl_val(injl(#())))) = true from rfl]
    wp_pures
    wp_bind (!#data)
    iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
    iintro H
    icases H with ⟨⟨>Hs2'', >Hr2'', >Hd⟩ | ⟨>Hs1'', >Hr2'', Hd⟩ | ⟨>Hs1'', >Hr1'', Hd⟩ |
      ⟨>Hs1'', >Hr2'', >Hd⟩⟩
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hr2 Hr2''
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hr2 Hr2''
    · icases Hd with ⟨%u, >Hd, #Hpu⟩
      wp_load
      isplitl [Hs1'' Hr1'' Hd]
      · imodintro
        inext
        iright
        iright
        ileft
        iframe Hs1'' Hr1''
        iexists u
        isplitl [Hd]
        · iexact Hd
        · iexact Hpu
      imodintro
      wp_bind (v(&unwrap) v(injr(&u)))
      iapply unwrap_spec (hl_val(injr(&u))) u _ rfl
      wp_pures
      wp_bind (#data ← v(injl(#())))
      iapply wp_inv_open (N := channelN) (by simp) $$ Hinv
      iintro H
      icases H with ⟨⟨>Hs2₃, >Hr2₃, >Hd⟩ | ⟨>Hs1₃, >Hr2₃, Hd⟩ | ⟨>Hs1₃, >Hr1₃, Hd⟩ |
        ⟨>Hs1₃, >Hr2₃, >Hd⟩⟩
      · iapply BI.false_elim
        iapply locked_exclusive $$ Hr2 Hr2₃
      · iapply BI.false_elim
        iapply locked_exclusive $$ Hr2 Hr2₃
      · icases Hd with ⟨%z, >Hd, _⟩
        wp_store
        isplitl [Hs1₃ Hr2 Hd]
        · imodintro
          inext
          iright
          iright
          iright
          iframe Hs1₃ Hr2
          iexact Hd
        imodintro
        wp_pures
        isplitl [Hr1₃]
        · iexact Hr1₃
        · iexact Hpu
      · iapply BI.false_elim
        iapply locked_exclusive $$ Hr2 Hr2₃
    · iapply BI.false_elim
      iapply locked_exclusive $$ Hr2 Hr2''
  · iapply BI.false_elim
    iapply locked_exclusive $$ Hr1 Hr1'
  · wp_load
    isplitl [Hs1' Hr2' Hd]
    · imodintro
      inext
      iright
      iright
      iright
      iframe Hs1' Hr2'
      iexact Hd
    imodintro
    wp_pures
    simp only [show (!(hl_val(injl(#())) == hl_val(injl(#())))) = false from rfl]
    wp_pure
    iapply IH $$ Hr1

end ChannelSpec

end ProgramLogics.Concurrency
