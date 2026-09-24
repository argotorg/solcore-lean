# ADR-0009: M1a Core machine and evaluation order

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M1 Semantic Core

## Reader summary / Current implementation

- **Decision:** The first closed Core has unit, booleans, bounded words,
  immutable de Bruijn bindings, and condition-first selected-branch-only
  conditionals, with a fuelled CEK machine matching declarative evaluation.
- **Current implementation:** The syntax, checker, big-step semantics, CEK
  executor, correspondence, progress, preservation, and fuel theorems are
  implemented and remain the foundation of the current Core.
- **Boundary:** Functions, mutation, ADTs, primitives, source parsing, and
  lowering are not part of M1a.
- **Suggested reading:** Read “Decision” and “Not decided here” first, then use
  “Conformance requirements” as the proof checklist.

## Context

The first Semantic Core must support type checking and evaluation without passing
through the source parser, name resolver, specializer, or Hull/Yul backend.
Normatively specifying unresolved functions, mutation, ADTs, and primitive
operations all at once would risk confusing implementation behavior with the
language specification.

The Haskell implementation at
`1d490d8bb5f374356f06e0720655496482eb1fb4` and the Rust implementation at
`38f4778ea461edfe59106bdb1f9f08c3307b0fc0` both process a `let` initializer
before introducing its binder and lower eager operands in source order. Their
handling of conditionals differs materially.

- Rust's Yul lowering evaluates the condition and then executes only the selected
  branch inside a `switch`.
- The Haskell partial evaluator and some Hull-lowering paths precompute both
  branches and can therefore execute effects in the unselected branch.

The latter behavior is not adopted as the reference semantics. An independent
rule is needed so that direct evaluation can expose this backend defect.

## Decision

The M1a kernel begins with the following closed fragment.

- Types, literals, and values for `unit`, `bool`, and 256-bit `word`
- Local variables represented by de Bruijn indices
- Initialized immutable `let`
- Conditional expressions

A `word` is represented in Lean as `Fin (2^256)`. A word passed to Core must
already be in range; Core does not silently reduce an out-of-range value modulo
`2^256`. Polymorphic source integer literals and their modulo elaboration into
words are the responsibility of M2.

Binding and evaluation order are fixed as follows.

1. `var 0` refers to the most recently introduced binding.
2. `let value body` evaluates `value` exactly once in the current environment.
3. The resulting value is prepended to the environment at index 0, and `body` is
   evaluated in that environment.
4. `if condition then else` evaluates `condition` first.
5. If the condition is true, only the then branch is evaluated; if it is false,
   only the else branch is evaluated.

Dynamic semantics are defined by an environment-based CEK machine. One unit of
runner fuel corresponds to one CEK transition. Final-state detection precedes fuel
consumption, so a run succeeds with exactly as much fuel as its transition count.
Fuel exhaustion is not a language-level rejection.

The unchecked machine can represent unbound variables and non-boolean conditions
as faults. Progress and preservation are proved for well-typed states, making the
unreachability of those faults a theorem of the semantic kernel.

## Not decided here

- Word arithmetic, division by zero, shifts, and comparisons
- Functions, closures, recursion, and return
- Mutable cells, assignment, and uninitialized locals
- Products, sums, ADTs, and pattern matching
- `&&` and `||`

In particular, the eager function calls used for `&&` and `||` by current
compilers are not made normative. When introduced, these operators will be
specified in a separate ADR as short-circuiting forms derived from conditionals.

## Consequences

- Declarative typing and the executable inferencer are defined separately, with
  proofs of soundness and completeness.
- Declarative big-step evaluation and CEK transitions are defined separately,
  with correspondence proved in both directions.
- CEK transitions are deterministic.
- Progress and preservation are proved for machine-state typing.
- Every well-typed closed term terminates with some finite amount of fuel and
  cannot produce a machine fault for any fuel amount.
- This M1a fragment alone does not complete the aggregate primitive boundary;
  it implements only the listed Core forms.

## Conformance requirements

- Include a nested-`let` test in which index 0 refers to the most recent binding.
- Include a test showing that the unselected conditional branch is not evaluated.
- Include negative tests for an unbound index, a non-boolean condition, a branch
  type mismatch, and a declared-result mismatch.
- For a witness requiring a known number of transitions, test `outOfFuel`
  immediately before that count and `done` at the boundary.
- Use neither `sorry` nor additional axioms in correspondence theorems among the
  checker, big-step relation, and CEK runner.
