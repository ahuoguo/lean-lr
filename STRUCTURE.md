# Structure of the Lean development

This document roughly maps the lecture notes and exercises to the Lean development. It is
`semantics-course@new`'s [`STRUCTURE.md`][upstream] with the Rocq entry points replaced by the
Lean ones.

[upstream]: https://gitlab.mpi-sws.org/FP/semantics-course/-/blob/new/STRUCTURE.md

## Basic structure

Chapters 1-4 are in the `LeanLr/TypeSystems` folder.
Chapters 5-10 are in the `LeanLr/ProgramLogics` folder.
All of the paths given below are to be understood relative to these folders.

## Chapter 1

* The `Warmup.lean` file contains a quick reminder of some concepts of Lean.
* The `Stlc` folder contains an implementation of the untyped lambda-calculus and the
  simply-typed lambda-calculus, with different reduction semantics, including syntactic and
  semantic type safety proofs.
* The `StlcExtended` folder features an extended version of our core calculus with products,
  sums, and more operators.

| Section | Lean entry point                        |
|---------|-----------------------------------------|
| 1.0     | `Stlc/Lang.lean`                        |
| 1.1     | `Stlc/Lang.lean`, `Stlc/Operational.lean` |
| 1.2     | `Stlc/Untyped.lean`                     |
| 1.3     | `Stlc/Types.lean`, `Stlc/TypeSafety.lean` |
| 1.4     | `Stlc/LogRel.lean`                      |

The exercise sheets for this chapter are `Stlc/Exercises01.lean` and `Stlc/Exercises02.lean`;
`Stlc/Lecture2.lean` holds the inversion operators shown in the second lecture.

Special notes on some exercises:
* Exercises 12, 13, and 15 are the `StlcExtended` folder.
* Exercise 16 (`stlc/cbn_logrel.v`) is `Stlc/CbnLogRel.lean`.

## Chapter 2

* The development for Chapter 2 is the `SystemF` folder.

| Section | Lean entry point                              |
|---------|-----------------------------------------------|
| 2.1     | `SystemF/Lang.lean`, `SystemF/BigStep.lean`   |
| 2.3     | `SystemF/Types.lean`, `SystemF/TypeSafety.lean` |
| 2.4     | `SystemF/TypeSafety.lean`                     |
| 2.5     | `SystemF/ChurchEncodings.lean`                |
| 2.6     | `SystemF/LogRel.lean`                         |
| 2.7     | `SystemF/FreeTheorems.lean`                   |
| 2.8     | `SystemF/ExistentialInvariants.lean`          |
| 2.9     | `SystemF/BinaryLogRel.lean`                   |

The exercise sheets for this chapter are `SystemF/Exercises03.lean` and
`SystemF/Exercises04.lean`.

Special notes on some exercises:
* Exercises from Sections 2.1 - 2.3 are not present, except for Exercises 18 and 19.
* Exercises 32 and 34 are not present.
* `SystemF/ChurchEncodingsFaithful.lean` (the faithfulness of the Church encodings, proved with the binary relation) has no section of its own in the notes; it follows Section 2.9.

## Chapter 3

* The development for Chapter 3 is the `SystemFMu` folder.

| Section | Lean entry point                                   |
|---------|----------------------------------------------------|
| 3.0     | `SystemFMu/Lang.lean`, `SystemFMu/Types.lean`, `SystemFMu/TypeSafety.lean` |
| 3.1     | `SystemFMu/UntypedEncoding.lean`                   |
| 3.3     | `SystemFMu/Pure.lean`, `SystemFMu/LogRel.lean`     |
| 3.4     | `SystemFMu/ZCombinator.lean`                        |

The exercise sheet for this chapter is `SystemFMu/Exercises05.lean` (which is also
`semantics-code`'s `exercises06.v`); `SystemFMu/Tactics.lean` is its `solve_typing`.

Special notes on some exercises:
* Exercises 36 and 39 are not present.
* Exercises 41 and 44 are already proved for you.

## Chapter 4

* The development for Chapter 4 is the `SystemFMuState` folder. Sections 4.7 and 4.8 are not
  treated.

| Section | Lean entry point                                                     |
|---------|----------------------------------------------------------------------|
| 4.0     | `SystemFMuState/Lang.lean`, `SystemFMuState/Types.lean`, `SystemFMuState/TypeSafety.lean` |
| 4.3     | `SystemFMuState/TypeSafety.lean`                                     |
| 4.6     | `SystemFMuState/LogRel.lean`, `SystemFMuState/MutBit.lean`           |
| 4.9     | `SystemFMuState/LogRel.lean`                                         |

`SystemFMuState/Execution.lean` and `SystemFMuState/ParallelSubst.lean` are the supporting
`red_nsteps` and substitution theory that Sections 4.6 and 4.9 rest on.

The exercise sheet for this chapter is `SystemFMuState/Exercises07.lean`, against the syntactic
type system of `SystemFMuState.Syn`; `SystemFMuState/Tactics.lean` is its `solve_typing`.

Special notes on some exercises:
* Exercises 51, 52, and 55 have already been proved for you.
* Exercise 56 is not present.

## Chapter 5

* The development for Chapter 5 is `Hoare.lean`, on the interface `HoareLib.lean` provides.
* Exercises are provided in-line with the material.

## Chapter 6

* The development for Chapter 6 is spread over three files.

| Section | Lean entry point                                     |
|---------|------------------------------------------------------|
| 6.1-6.3 | `Ipm.lean`                                           |
| 6.4     | `IpmPersistency.lean`                                |
| 6.5     | `LaterLoeb.lean`                                     |

* Exercises are provided in-line with the material.

## Chapter 7

* The development for Chapter 7 is the folder `LogRel/`, in files:
  + `LogRel/Syntactic.lean` defines a syntactic type system for our language.
  + `LogRel/LogRel.lean` defines the logical relation and proves the fundamental theorem.
  + `LogRel/Adequacy.lean` proves adequacy of the logical relation.
  + `LogRel/Notation.lean` encodes the polymorphic constructs in heap_lang, and
    `LogRel/PersistentPred.lean` is the domain of semantic types.
* Exercises are provided in-line with the material.

## Chapter 8

* The development for Chapter 8 is distributed over multiple files and folders.
* Exercises are provided in-line with the material.

| Section | Lean entry point                                     |
|---------|------------------------------------------------------|
| 8.0     | `LogRel/GhostState.lean`, `LogRel/GhostStateLib.lean` |
| 8.1     | `RaLib.lean`, `ResourceAlgebras1.lean`               |
| 8.2     | `ResourceAlgebras1.lean`                             |
| 8.3     | `GhostTheories.lean`                                 |
| 8.4     | `Reloc/` and `Fupd.lean`                             |

In particular, for ReLoC / the binary logical relation, the following files are of interest:
- `Reloc/GhostState.lean` defines the ghost theory (Section 8.4.3),
- `Fupd.lean` introduces the fancy update modality (Section 8.4.2),
- `Reloc/SrcRules.lean` proves the ghost program rules (Section 8.4.1/8.4.3),
- `Reloc/LogRel.lean` defines the logical relation (Section 8.4.1),
- `Reloc/Fundamental.lean` proves the fundamental property (Section 8.4.4),
- `Reloc/Adequacy.lean` and `Reloc/ContextualRefinement.lean` prove the contextual refinement
  result (Section 8.4.4).

`Reloc/PersistentBipred.lean` is the domain of relational semantic types, the binary counterpart
of `LogRel/PersistentPred.lean`.

Notes on exercises:
* Exercise 116 (coming up with an interesting refinement and proving it) is not present.

## Chapter 9

* Chapter 9 is not explicitly formalized. We recommend that you look at the `iris-lean` source
  code if you are interested.

## Chapter 10

* The development for Chapter 10 is distributed over multiple files and folders.

| Section | Lean entry point                                     |
|---------|------------------------------------------------------|
| 10.0    | `Concurrency.lean`                                   |
| 10.1    | `Concurrency.lean`                                   |
| 10.2    | `Concurrency.lean`                                   |
| 10.3    | — not ported (`concurrent_logrel/`)                  |

Notes on exercises:
* The exercise for verifying the channel implementation (Section 10.3) is in `Concurrency.lean`.
* `Arc.lean` (an atomically reference-counted pointer) follows Chapter 10 but has no section of
  its own in the notes.

## Infrastructure with no chapter of its own

Most of the course's `program_logic/` and `heap_lang/` folders are lightly-edited forks of
upstream Iris and are replaced by the corresponding `Iris.*` module rather than ported
(`CORRESPONDENCE.md` §5.4). What the course *adds* on top is here:

| Lean file | What it is |
|---|---|
| `SequentialWp.lean` | the sequential, two-mask weakest precondition `swp` (`program_logic/sequential_wp.v`) |
| `SeqAdequacy.lean` | adequacy for `swp` (`program_logic/adequacy.v`, `heap_lang/adequacy.v`) |
| `HeapLang/NoLater.lean` | the later-free heap laws over `swp` (`heap_lang/primitive_laws_nolater.v`) |
| `HeapLang/SwpTactics.lean` | `swp_pures`, `swp_bind_*`, `swp_enter` — the tactic layer the `swp` proofs are written with; new in the port (`CORRESPONDENCE.md` §5.11) |
| `InvariantLib.lean` | impredicative invariants over `swp` (`invariant_lib.v`) |
| `Oplss.lean`, `Oplss2.lean` | the two OPLSS lectures (`oplss1.v`, `oplss2.v`), which are not part of the notes |

## Not in this port

* **`concurrent_logrel/`** (Section 10.3), the concurrent logical relation — three files
  (`syntactic.v`, `logrel_sol.v`, `adequacy.v`) that redevelop Chapter 7's logical relation over
  the concurrent language. This is the only part of the course that has no Lean counterpart.
