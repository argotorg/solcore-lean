# ADR-0245: Runtime-world safety for actual local applications

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Proof-only safety above exact original-call correspondence

## Evidence and decision

The independent original-call relations now retain actual closure bodies,
captures, values, stores and exact costs. Their conditional correspondence needs
ordered runtime IDs, not runtime typing. That deliberately permits raw success
with differently typed actual values and structurally typed references to
unallocated cells. Neither case supplies a safety theorem.

Use the existing Core runtime world rather than weakening this boundary.
`Core.RuntimeEnvironmentHasTypes` checks all supplied values and captured values
against one world; its cell-reference rule requires the location's type in that
world. `Core.StoreHasTypes` requires the same world/store length and a correctly
typed allowed payload at every location. Structural `ValueHasType`, equal store
lengths, or runtime-world typing alone do not replace these two premises.

The primary execution evidence is `Core/Safety.lean`:
`evaluation_preserves_type` (696), `well_typed_evaluates` (1798), `StateHasType`
(2153), and state/path/runner safety (2741–2808). Static exact application typing
still uses the existing empty data environment. Its well-formedness follows from
empty membership; do not introduce a new nominal-data environment or a hidden
inhabitance assumption. The pinned Rust Function specialization from ADR-0243
and every source acceptance rule remain unchanged.

Expose proof-only source-call runtime preservation and successful exact-cost
existence using independent whole typing or exact elaboration. Preserve the
actual original value and final store, with an extending world and runtime value
typing in that final world. Typed execution supplies an actual cost before all
continuations and exact closed-run fuel thresholds. It is not a bound computed
from source syntax, static types, or the frontend traversal.

Expose machine-state safety for an exact original Core application under a
runtime-typed environment/store and a typed continuation. No source-ID alignment
is needed for this state-only claim: Core executes the given positional values.
Alignment remains mandatory whenever identifying the result with original source
evaluation. Preserve state typing through a genuinely exhausted checkpoint and
exclude faults for all fuel only under the typed-continuation premise. An
arbitrary untyped continuation still has the earlier exact endpoint path but can
fault immediately afterwards. Checker-facing results must obtain exact original
provenance from the existing soundness theorem.

## Why successful execution is justified here

Core's existing reducibility theorem proves successful execution for its current
typed language, not for arbitrary stateful closure languages. `CellPayload`
(`Core/Syntax.lean`, 47) permits primitives, products and sums, but no functions,
references or nominal data. Cell operation typing and store typing retain this
restriction. `ConstructorPayload` (`Core/Data.lean`, 167) excludes functions and
allows only its existing restricted forms; data-environment well-formedness is
used by the general reducibility proof. Core has no fixpoint or recursive-let
expression constructor. Actual closure values carry finite captured values and
typed bodies. Reuse these existing restrictions without changing or broadening
the source language's policy.

An identical original `f(x)` can have costs `3*n+6` for different well-typed
actual bodies. Runtime-world safety therefore gives actual successful execution
and a sufficient cost, not a source-only bound, unchanged store, unchanged world,
or cost agreement between distinct captures or stores.

## Validation and boundaries

Independent consumers cover actual identity and captured references, allocation,
read/write effects, delayed typed bodies, higher-order nominal function values,
and genuine checkpoint/resumption states. Explicit counterexamples distinguish
structural typing from runtime-world typing, runtime-world typing from actual
store validity, wrong payload types from equal lengths, and untyped pending
frames from safe continuations. Parsed consumers retain original AST fields and
complete original parameter records; existing whole entries still reject calls.

No executable evaluator, checker, body/entry grammar, parser, diagnostic, Core
definition or wire change is introduced. Split design, proofs, consumers and
publication into small commits; keep new files below 300 lines. Require focused
and aggregate builds, full tests, all public/consumer standard-axiom audits,
kernel/metadata/whitespace checks, and independent reviews.
