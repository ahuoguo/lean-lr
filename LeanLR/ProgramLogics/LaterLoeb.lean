import LeanLR.ProgramLogics.IpmPersistency
import LeanLR.ProgramLogics.HeapLang.SwpTactics

/-!
# Later and Löb induction

`program_logics/later_loeb_sol.v` and `later_playground_sol.v`.
-/

open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProofMode
open ProgramLogics.IpmPersistency

namespace ProgramLogics.LaterLoeb

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

/-- Löb induction gives a recursive function its own specification while verifying its body. -/
theorem ent_wp_rec (v : Val) (Φ : Val → IProp GF) (Ψ : Val → Val → IProp GF) (e : Exp)
    (h : ∀ v : Val,
      iprop(Φ v ∗ ∀ u : Val, IpmPersistency.hoare (Φ u) hl(v(rec f x := &e) &u) (Ψ u)) ⊢
        swp .NotStuck ⊤ ⊤ ((e.subst (.named "f") hl_val(rec f x := &e)).subst (.named "x") v)
          (Ψ v)) :
    Φ v ⊢ swp .NotStuck ⊤ ⊤ hl(v(rec f x := &e) &v) (Ψ v) := by
  iintro Hv
  iloeb as IH generalizing! %v
  swp_pure_later
  inext
  iapply h v
  isplitl [Hv]
  · iexact Hv
  iintro %u
  unfold IpmPersistency.hoare
  iintro !> Hu
  iapply IH $$ Hu

/-- `later_playground.v`'s form of the recursion rule: hypothesis and conclusion are both
internalised triples. -/
theorem ent_wp_rec' (Φ : Val → IProp GF) (Ψ : Val → Val → IProp GF) (e : Exp)
    (h : ⊢ ∀ v : Val, IpmPersistency.hoare
      iprop(Φ v ∗ ∀ u : Val, IpmPersistency.hoare (Φ u) hl(v(rec f x := &e) &u) (Ψ u))
      ((e.subst (.named "f") hl_val(rec f x := &e)).subst (.named "x") v) (Ψ v)) :
    ⊢ ∀ v : Val, IpmPersistency.hoare (Φ v) hl(v(rec f x := &e) &v) (Ψ v) := by
  have h' : ∀ v : Val,
      iprop(Φ v ∗ ∀ u : Val, IpmPersistency.hoare (Φ u) hl(v(rec f x := &e) &u) (Ψ u)) ⊢
        swp .NotStuck ⊤ ⊤ ((e.subst (.named "f") hl_val(rec f x := &e)).subst (.named "x") v)
          (Ψ v) := by
    intro v
    iintro HP
    ihave Hh := h
    ispecialize Hh $$ %v
    unfold IpmPersistency.hoare
    iapply Hh $$ HP
  iintro %v
  unfold IpmPersistency.hoare
  imodintro
  iintro Hv
  iapply ent_wp_rec v Φ Ψ e h'
  iexact Hv

/-! ## The Z combinator

Recursion without a recursive binder: `Z_com` ties the knot by self-application. -/

section Z

variable (e : Exp)

/-- The self-applying core of the Z combinator. -/
def g : Val := hl_val(λ f, let f := (λ x, f f x); λ x, &e)

/-- `Z_com` in Rocq. -/
def zCom : Val := hl_val(λ x, v(&(g e)) v(&(g e)) x)

theorem Z_spec (v : Val) (Φ : Val → IProp GF) (Ψ : Val → Val → IProp GF)
    (h : ∀ v : Val,
      iprop(Φ v ∗ ∀ u : Val, IpmPersistency.hoare (Φ u) hl(v(&(zCom e)) &u) (Ψ u)) ⊢
        swp .NotStuck ⊤ ⊤ ((e.subst (.named "f") (zCom e)).subst (.named "x") v) (Ψ v)) :
    Φ v ⊢ swp .NotStuck ⊤ ⊤ hl(v(&(zCom e)) &v) (Ψ v) := by
  simp only [zCom, g] at h ⊢
  iintro Hv
  iloeb as IH generalizing! %v
  swp_enter Hcl
  wp_pures
  iapply swp_to_wp $$ Hcl
  iapply h v
  isplitl [Hv]
  · iexact Hv
  iintro %u
  unfold IpmPersistency.hoare
  iintro !> Hu
  iapply IH $$ Hu

end Z

/-! ## Landin's knot

Recursion through the store: `landins_knot t` allocates a reference, ties it to a function that
reads itself back, and hands the result to `t`. The specification is proved by Löb induction, with
the reference's contents held in an invariant. -/

def landinN : Namespace := nroot .@ "landin"

def landinsKnot : Val := hl_val(λ f,
  let x := ref(v(λ x, #(0 : Int)));
  let g := (λ z, f (λ y, (!x) y) z);
  (x ← g; g))

/-! ## Impredicative invariants

Deriving the timeless opening rule from the impredicative one. -/

theorem inv_open_timeless {N : Namespace} {E : CoPset} {F : IProp GF} [Timeless F] {e : Exp}
    {Φ : Val → IProp GF} {s : Stuckness} (Hsub : ↑N ⊆ E) :
    inv N F ⊢ iprop((F -∗ swp s (E \ ↑N) (E \ ↑N) e (fun v => iprop(▷ F ∗ Φ v))) -∗
      swp s E E e Φ) := by
  iintro #Hinv Hc
  iapply ImpredInvariants.inv_open Hsub $$ Hinv
  iintro >HF
  iapply Hc $$ HF

theorem landins_knot_spec (t : Val) (Φ Ψ : Val → IProp GF)
    (Ht : ∀ f : Val, ⊢ IpmPersistency.hoare
      iprop(∀ v : Val, IpmPersistency.hoare (Φ v) hl(v(&f) &v) Ψ) hl(v(&t) v(&f))
      (fun g => iprop(∀ v : Val, IpmPersistency.hoare (Φ v) hl(v(&g) &v) Ψ))) :
    ⊢ IpmPersistency.hoare (GF := GF) iprop(True) hl(v(&landinsKnot) v(&t))
      (fun g => iprop(∀ v : Val, IpmPersistency.hoare (Φ v) hl(v(&g) &v) Ψ)) := by
  unfold IpmPersistency.hoare
  imodintro
  iintro _
  simp only [landinsKnot]
  swp_enter Hcl
  wp_pures
  wp_alloc l with Hl
  wp_pures
  wp_store
  imod Hcl
  imod Iris.inv_alloc landinN ⊤
    (iprop(l ↦ some hl_val(λ z, v(&t) (λ y, (!v(#l)) y) z)) : IProp GF) $$ [Hl] with #Hinv
  · inext
    iexact Hl
  imodintro
  iintro %v
  iintro !> Hv
  iloeb as IH generalizing! %v
  swp_pure_later
  inext
  swp_pures
  iapply swp_bind_appL
  ihave Hts := Ht hl_val(λ y, (!v(#l)) y)
  unfold IpmPersistency.hoare
  ispecialize Hts $$ [#]
  · iintro %v'
    iintro !> Hv'
    swp_pures
    iapply swp_bind_appL
    iapply ImpredInvariants.inv_open (N := landinN) (by simp) $$ Hinv
    iintro Hl
    swp_enter Hcl2
    icases Hl with >Hl
    wp_load
    imod Hcl2
    imodintro
    isplitl [Hl]
    · inext
      iexact Hl
    iapply IH $$ Hv'
  iapply swp_wand $$ Hts
  iintro %g Hg
  ispecialize Hg $$ %v
  iapply Hg $$ Hv

/-! ## Lazy integers

A *lazy integer* is a thunk: a value `f` such that `f #()` evaluates to `n`. Nothing says it may
be forced twice, and `LazyInt` is not persistent, so a client that wants to force it repeatedly
has to cache the result. -/

/-- `f #()` evaluates to `n`. -/
def LazyInt (f : Val) (n : Int) : IProp GF :=
  swp .NotStuck ⊤ ⊤ hl(v(&f) #()) (fun w => iprop(⌜w = hl_val(#n)⌝))

def lazyintAdd : Val := hl_val(λ f g _, f #() + g #())

theorem add_spec (f g : Val) (n m : Int) :
    ⊢ IpmPersistency.hoare (GF := GF) iprop(LazyInt f n ∗ LazyInt g m)
        hl(v(&lazyintAdd) v(&f) v(&g)) (fun h => LazyInt h (n + m)) := by
  unfold IpmPersistency.hoare
  imodintro
  iintro ⟨Hf, Hg⟩
  simp only [lazyintAdd]
  swp_pures
  iapply swp_value'
  unfold LazyInt
  swp_pures
  iapply swp_bind (K := fun e => Exp.binop .plus hl(v(&f) #()) e)
  iapply swp_wand $$ Hg
  iintro %w %hw
  subst hw
  iapply swp_bind (K := fun e => Exp.binop .plus e hl_val(#m))
  iapply swp_wand $$ Hf
  iintro %w %hw
  subst hw
  swp_pures
  iapply swp_value'
  ipureintro
  rfl

/-! ## Caching a lazy integer

`cache f` forces `f` at most once and remembers the answer, so the result *is* duplicable. The
state of the cache is a location holding one of three things: the unforced thunk, the value it
produced, or a marker saying that forcing is in progress — which is a state no client can observe,
because reaching it diverges. -/

def lazyintN : Namespace := nroot .@ "lazyint"

def retrieve : Val := hl_val(λ c,
  match !c with
  | injl(cc) =>
      (match cc with
       | injl(f) => (c ← injr(#()); injl(f))
       | injr(y) => injr(y))
  | injr(cc) => (rec rc _ := rc #()) #())

def cache : Val := hl_val(λ f,
  let c := ref(injl(injl(f)));
  λ _, let r := v(&retrieve) c;
       (match r with
        | injl(f) => (let y := f #(); (c ← injl(injr(y)); y))
        | injr(y) => y))

/-- The cache invariant: the thunk is unforced, or its value is remembered, or forcing is in
progress. -/
def I (f : Val) (n : Int) (l : Loc) : IProp GF :=
  iprop((((l ↦ some hl_val(injl(injl(&f))) : IProp GF) ∗ LazyInt f n) ∨
      l ↦ some hl_val(injl(injr(#n)))) ∨ l ↦ some hl_val(injr(#())))

theorem retrieve_spec (f : Val) (n : Int) (l : Loc) (N : Namespace) :
    iprop(▷ I (GF := GF) f n l) ⊢ swp .NotStuck (⊤ \ ↑N) (⊤ \ ↑N) hl(v(&retrieve) #l)
      (fun r => iprop(I f n l ∗
        ((⌜r = hl_val(injl(&f))⌝ ∗ LazyInt f n) ∨ ⌜r = hl_val(injr(#n))⌝))) := by
  iintro HI
  simp only [retrieve]
  swp_enter Hcl
  wp_pure
  unfold I
  icases HI with ⟨⟨⟨Hl, Hlzy⟩ | Hl⟩ | Hl⟩
  · wp_load
    wp_pures
    wp_store
    wp_pures
    imod Hcl
    imodintro
    isplitl [Hl]
    · iright
      iexact Hl
    · ileft
      isplitr
      · ipureintro; rfl
      · iexact Hlzy
  · wp_load
    wp_pures
    imod Hcl
    imodintro
    isplitl [Hl]
    · ileft
      iright
      iexact Hl
    · iright
      ipureintro; rfl
  · wp_load
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    iclear Hl
    iclear Hcl
    iloeb as IH
    wp_pure
    iexact IH

theorem cache_spec (f : Val) (n : Int) :
    ⊢ IpmPersistency.hoare (GF := GF) (LazyInt f n) hl(v(&cache) v(&f))
        (fun g => iprop(□ LazyInt g n)) := by
  unfold IpmPersistency.hoare
  imodintro
  iintro Hlazy
  simp only [cache]
  swp_enter Hcl
  wp_pures
  wp_alloc l with Hc
  wp_pures
  imod Hcl
  imod Iris.inv_alloc (lazyintN .@ l) ⊤ (I f n l) $$ [Hc Hlazy] with #HInv
  · inext
    unfold I
    ileft
    ileft
    isplitl [Hc]
    · iexact Hc
    · iexact Hlazy
  imodintro
  imodintro
  unfold LazyInt
  swp_pures
  iapply swp_bind_appR
  iapply ImpredInvariants.inv_open (N := lazyintN .@ l) (by simp) $$ HInv
  iintro HI
  icases retrieve_spec f n l (lazyintN .@ l) $$ HI with HR
  iapply swp_wand $$ HR
  iintro %r ⟨HI, Hr⟩
  isplitl [HI]
  · inext
    iexact HI
  icases Hr with ⟨⟨%hr, Hlzy⟩ | %hr⟩
  · subst hr
    unfold LazyInt
    swp_pures
    iapply swp_bind_appR
    iapply swp_wand $$ Hlzy
    iintro %w %hw
    subst hw
    swp_pures
    iapply swp_bind_appR
    iapply ImpredInvariants.inv_open (N := lazyintN .@ l) (by simp) $$ HInv
    iintro HI
    swp_enter Hcl2
    unfold I
    icases HI with ⟨⟨⟨>Hl, Hlzy⟩ | >Hl⟩ | >Hl⟩
    · wp_store
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        ileft
        iright
        iexact Hl
      swp_pures
      iapply swp_value'
      ipureintro
      rfl
    · wp_store
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        ileft
        iright
        iexact Hl
      swp_pures
      iapply swp_value'
      ipureintro
      rfl
    · wp_store
      imod Hcl2
      imodintro
      isplitl [Hl]
      · inext
        ileft
        iright
        iexact Hl
      swp_pures
      iapply swp_value'
      ipureintro
      rfl
  · subst hr
    swp_pures
    iapply swp_value'
    ipureintro
    rfl

/-! ## Why the cache has to mark that forcing is in progress

`cache'` is `cache` without the third state: it stores either the thunk or its value, and never
records that forcing has begun. `E` is the program that breaks it — a thunk whose second forcing
gets stuck — so `cache'` cannot satisfy `cache`'s specification. `E_safe` is the contradiction:
*if* it did, `E` would be safe, and `E` is not. -/

def cache' : Val := hl_val(λ f,
  let c := ref(injl(f));
  λ _, match !c with
       | injl(g) => (let k := g #(); (c ← k; k))
       | injr(k) => k)

/-- Rocq writes the guard as `assert (!"r")`; `assert` is a `Val`, and `Exp.subst` does not
descend below one, so it is spelled out (`SwpTactics` normalises substitutions, and an opaque
`assert` would block that). -/
def E : Exp := hl(
  let z := ref(v(λ _, #(0 : Int)));
  let r := ref(#true);
  let z' := (λ _, ((if !r then #() else #(0 : Int) #(0 : Int)); (r ← #false; !z)) #());
  let c := v(&cache') z';
  (z ← c; c #()))

theorem E_safe :
    iprop(∀ f : Val, ∀ n : Int, IpmPersistency.hoare (LazyInt f n) hl(v(&cache') v(&f))
        (fun g => iprop(□ LazyInt g n))) ⊢
      IpmPersistency.hoare (GF := GF) iprop(True) E (fun _ => iprop(True)) := by
  unfold IpmPersistency.hoare
  iintro #Hcache
  imodintro
  iintro _
  simp only [E]
  iapply swp_bind_appR
  iapply swp_alloc
  iintro %z Hz
  swp_pures
  iapply swp_bind_appR
  iapply swp_alloc
  iintro %r Hr
  swp_pures
  iapply ImpredInvariants.inv_alloc (N := nroot)
    (F := iprop(∃ f : Val, (z ↦ some f) ∗ □ LazyInt f 0)) $$ [Hz]
  · iexists hl_val(λ _, #(0 : Int))
    isplitl [Hz]
    · iexact Hz
    · imodintro
      unfold LazyInt
      swp_pures
      iapply swp_value'
      ipureintro
      rfl
  iintro #Hinv
  swp_pures
  ihave Hh : LazyInt hl_val(λ _,
      ((if !v(#r) then #() else #(0 : Int) #(0 : Int)); (v(#r) ← #false; !v(#z))) #()) 0 $$ [Hr]
  · unfold LazyInt
    swp_pure
    iapply swp_bind_appL
    iapply ImpredInvariants.inv_open (N := nroot) (by simp) $$ Hinv
    iintro HI
    swp_enter Hcl2
    icases HI with ⟨%f, >Hz, #Hf⟩
    wp_load
    wp_pures
    wp_store
    wp_load
    imod Hcl2
    imodintro
    isplitl [Hz]
    · inext
      iexists f
      isplitl [Hz]
      · iexact Hz
      · iexact Hf
    iexact Hf
  iapply swp_bind_appR
  ispecialize Hcache $$ %_ %(0 : Int) Hh
  iapply swp_wand $$ Hcache
  iintro %c #Hc
  swp_pures
  iapply swp_bind_appR
  iapply ImpredInvariants.inv_open (N := nroot) (by simp) $$ Hinv
  iintro HI
  swp_enter Hcl3
  icases HI with ⟨%f, >Hz, Hlzy⟩
  wp_store
  imod Hcl3
  imodintro
  isplitl [Hz]
  · inext
    iexists c
    isplitl [Hz]
    · iexact Hz
    · iexact Hc
  swp_pures
  unfold LazyInt
  iapply swp_wand $$ Hc
  iintro %v _
  itrivial

def lazyintTwo : Val := hl_val(λ f1 f2 i, let c := v(&cache) i; f1 c + f2 c)

/-- Two clients may share one lazy integer, because caching made it duplicable. -/
theorem lazyint_two_spec (h1 h2 f : Val) (n : Int) :
    ⊢@{IProp GF}
      (∀ f' : Val, ∀ n' : Int, IpmPersistency.hoare (LazyInt f' n') hl(v(&h1) v(&f'))
          (fun v => iprop(∃ m : Int, ⌜v = hl_val(#m)⌝))) -∗
      (∀ f' : Val, ∀ n' : Int, IpmPersistency.hoare (LazyInt f' n') hl(v(&h2) v(&f'))
          (fun v => iprop(∃ m : Int, ⌜v = hl_val(#m)⌝))) -∗
      IpmPersistency.hoare (LazyInt f n) hl(v(&lazyintTwo) v(&h1) v(&h2) v(&f))
        (fun v => iprop(∃ m : Int, ⌜v = hl_val(#m)⌝)) := by
  unfold IpmPersistency.hoare
  iintro #H1 #H2
  imodintro
  iintro Hf
  simp only [lazyintTwo]
  swp_pures
  iapply swp_bind_appR
  ihave Hcs := cache_spec f n
  unfold IpmPersistency.hoare
  ispecialize Hcs $$ Hf
  iapply swp_wand $$ Hcs
  iintro %c #Hlazy
  swp_pures
  iapply swp_bind_binOpR
  ihave HB := H2 $$ %c %n Hlazy
  iapply swp_wand $$ HB
  iintro %v2 ⟨%m2, %hv2⟩
  subst hv2
  iapply swp_bind_binOpL
  ihave HA := H1 $$ %c %n Hlazy
  iapply swp_wand $$ HA
  iintro %v1 ⟨%m1, %hv1⟩
  subst hv1
  swp_pures
  iapply swp_value'
  iexists (m1 + m2)
  ipureintro
  rfl

end ProgramLogics.LaterLoeb
