# ADR-0371: Restricted public source compiler

## Status

Accepted for roadmap phase 9.  The public Lean library now checks, specializes,
selects a runtime for, and executes one explicit ground source root through a
reusable compiler artifact.

This is a restricted source compiler, not a source Oracle or an ABI entry-point
policy.  Existing Core, graph-runtime, and `SourceProgramExecution` interfaces
retain their meanings.

## Context

ADR-0343 exposed the first explicit single-seed raw-workspace path.  It selected
the direct Semantic Core linker and, after ADR-0368, a structural finite call-
graph fallback.  ADR-0369 added a separate source-typed runtime for nominal
constructors, mappings, proxies, mutation, closures, matches, and loops.

That runtime was not connected to a public compiler boundary.  A caller had to
repeat whole-program checking, signature lookup, worklist construction, seed-
key recovery, and the trusted plan handoff before invoking it.  Repeated roots
also repeated checking, and failure of both older linkers discarded the graph
diagnostic.  Phase 9 closes that composition gap without inventing automatic
root discovery or a wire representation.

## Decision

### Publish a sealed compile-once artifact

`Solcore.Frontend.SourceCompiler` is the canonical restricted compiler facade.
`compile` accepts a raw workspace and one explicit `Seed`; `compileChecked`
accepts an existing `CheckedProgram` so several entries can reuse one validated
catalog.  Both require ground generic arguments and a complete finite
specialization plan.

`CompiledEntry` has a private constructor.  Its public accessors expose only
the canonical specialization key, source input/result types, specialization
count, and selected backend.  The checked program, plan, and linker payload
cannot be replaced by callers.

Before backend selection, the compiler runs the direct linker's canonical plan
validation as a common preflight.  Each compatibility linker may still repeat
its own authoritative validation; a forged or inconsistent plan is therefore
not hidden by a later runtime fallback.

### Select one backend in a fixed order

Automatic selection is deterministic:

1. the direct, independently rechecked Semantic Core entry;
2. the checked finite structural call graph; then
3. the source-typed runtime.

The first successful backend is authoritative.  This preserves existing Core
and graph behavior for programs they already accept.  The typed runtime is
selected only after both compatibility linkers reject.  Before selection it
preflights executable metadata for every reachable specialization, rejecting
requirements and coercions it does not dispatch.  It also rejects unresolved
where assumptions, marked contracts, recursively nested structural comptime
types, and staged-only expression nodes rather than executing them at runtime.

If no backend is usable, `CompileError.noBackend` retains the direct, graph,
and typed rejection values together.  Checking, seed resolution, worklist,
budget, canonical-plan, root-shape, and backend-entry failures remain distinct
stages.

### Keep runtime domains explicit

Core and graph entries consume `Core.Value` plus `Core.Store`.  Typed entries
consume `SourceTypedRuntime.Value` plus `SourceTypedRuntime.RuntimeState`.
`Invocation.coreValues` and `Invocation.typedValues` keep these domains tagged;
the compiler performs no guessed conversion between them.  A mismatched tag is
rejected before execution.  Once the domain tag agrees, each backend retains
its native input-failure carrier.  The direct Core entry has no runtime-fault
carrier for an input-list mismatch, so the facade reports the dedicated
`coreInputTypesMismatch`; graph and typed runtime faults remain exact results.

`ExecutionResult` retains exact Core, graph, or typed outcomes.  Runtime faults
and fuel exhaustion are results, not compile failures.  Function-valued graph
or typed results may be observed in Lean, but external closure serialization
and reinjection are not part of this phase.

Compiler options separate checking, specialization, and staging.  Runtime
options separately bound recursive typed-input validation and execution.  The
older `SourceTypedRuntime.run` keeps its same-fuel behavior; the compiler uses
`runWithValidationFuel` so a shallow execution limit does not misclassify a
valid nested input.  Bounded validation distinguishes malformed input,
unsupported staged payloads, and validation-fuel exhaustion.  It checks values
in source order and reports the first non-valid outcome, so exhaustion before a
later field is not relabeled as a type mismatch.

### Preserve the compatibility API

`SourceProgramExecution.prepare`, `run`, and `runExact` are unchanged.  They
remain the Core-compatible single-seed interface and continue to select only
direct Core or its structural graph fallback.  Code depending on its result and
error carriers does not silently acquire typed values or heaps.

## Phase boundary

Roadmap phase 9 includes:

- raw-workspace and already-checked single-root compilation;
- a sealed, reusable canonical plan/root artifact;
- fixed Core, graph, then source-typed backend selection;
- typed-runtime whole-plan capability preflight;
- exact tagged invocation, state, result, and aggregate backend diagnostics;
- independent typed-input-validation and execution fuel; and
- public umbrella exports plus focused interface laws and regressions.

Still deferred are:

- automatic entry discovery, overload-based entry choice, ABI root policy, and
  public multi-root or mixed-backend compilation;
- an explicit backend override policy;
- source values, graph closures, typed heaps, or results on an Oracle/JSON wire;
- external closure serialization and reinjection;
- general trait-evidence/coercion dispatch in the typed runtime;
- general members, contract storage, ABI/external-call effects, and staged
  nominal/effectful values; and
- broad compiler correctness, preservation, determinism, and source/runtime
  correspondence proofs.

## Verification target

One checked multi-module workspace is reused to compile three roots.  The tests
fix direct Core precedence for a structural program, graph precedence for a
recursive program, and typed selection for an imported selectively visible
generic enum alias with expected-type construction, matching, and mutation.
They execute all three exact result carriers, reject a wrong typed input before
heap mutation, distinguish input-validation exhaustion from execution
exhaustion, retain supplied Core state, reject a runtime-domain tag mismatch,
propagate one-shot limits, reject where/comptime/staged-expression fallback,
and retain all three diagnostics when no backend supports a user coercion.

The aggregate Lean build and test suite remain the acceptance boundary.  This
phase adds no axiom, `sorry`, unsafe definition, or native decision procedure.
