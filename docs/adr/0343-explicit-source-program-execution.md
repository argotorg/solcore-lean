# ADR-0343: Explicit single-seed source-program execution

## Status

Implemented for the restricted executable source profile.

## Context

ADR-0342 established all of the stages needed to execute a closed, acyclic
source specialization, but exposed them as separate interfaces: callers first
checked a raw workspace, constructed a specialization request, ran the finite
worklist, linked the resulting plan, selected the corresponding linked entry,
and finally invoked Semantic Core.  This was executable, but it made every
consumer reproduce stage ordering and translate identifiers between the
layers.

The remaining policy question is deliberately not hidden in this interface.
The current language does not yet define automatic entry-point discovery, an
ABI-driven root set, or a choice among overloaded public functions.  A public
composition boundary should therefore require one explicit root and preserve
the existing stage errors instead of guessing.

## Decision

Add `Solcore.Frontend.SourceProgramExecution` as the public Lean composition
boundary for one explicitly selected source entry.  It connects, in order:

```text
raw workspace
  -> whole-program checking
  -> exact seed resolution
  -> finite specialization planning
  -> restricted direct-call linking
  -> checked Semantic Core execution
```

The interface is additive.  It does not replace the lower-level checker,
specializer or linker APIs, and it does not add a source Oracle or wire format.

### Explicit seed

`SeedTarget` has two forms:

- `declaration id` selects one already determined stable declaration identity;
- `named moduleId name` resolves an exact function in one module.

`Seed` pairs that target with `arguments`, the ground type arguments used to
specialize the declaration.  Declaration parameters remain authoritative:
arguments are converted to the existing parameter substitution in declaration
order, and missing, extra, open or otherwise invalid specializations reject.
Named selection is an exact lookup in the module-local function-signature
catalog.  A missing function name or multiple matching function signatures is
an error; a same-named non-function does not become an entry candidate.
Declaration selection separately rejects an identity whose catalog entry is
not a function.  Neither form is an overload-resolution or entry-discovery
policy.

The public boundary accepts exactly one seed.  This avoids inventing semantics
for choosing or ordering multiple roots while still allowing the internal
worklist to discover every reachable direct callee.

### Limits and preparation

`Limits` supplies three independent finite bounds, each defaulting to `1024`:

- `checkingFuel` for source checking and trait resolution;
- `specializationBudget` for distinct reachable specialization keys; and
- `executionFuel` for Semantic Core execution.

`prepare raw seed limits` validates and checks the complete raw workspace,
resolves the explicit seed, runs the finite specialization worklist, requires a
complete plan, links it, and returns a `PreparedEntry`.  The prepared value
retains its independently checked linked `entry`; `PreparedEntry.key` derives
the canonical specialization key from that entry, and
`PreparedEntry.inputTypes` exposes its checked input types.  It is therefore
the reusable boundary between source preparation and runtime inputs.

`PreparedEntry.run?` reuses the linked entry's runtime type guard and returns
`none` on an input mismatch; otherwise it runs with explicit execution fuel and
store.
Top-level `run raw seed inputs limits store` composes `prepare` with that
operation, uses `limits.executionFuel`, and translates an argument mismatch to
the public `inputTypesMismatch` error.

Errors retain their stage.  Whole-program checking failures, seed-resolution
failures, worklist errors, specialization-budget exhaustion, linking failures
and runtime-input failures are distinguishable.  In particular, a finite
worklist frontier becomes `specializationBudgetExhausted` before linking rather
than being relabeled as a linker failure.  A completed Core run may still report ordinary
fuel exhaustion in `Core.StatefulRunResult`; the API does not reinterpret that
runtime observation as successful termination.

## Deferred boundaries

This interface intentionally does not provide:

- automatic entry discovery or ABI-based root selection;
- a source Oracle, JSON schema or other wire protocol;
- multiple explicit roots in one public request;
- execution of recursive or indirect source calls;
- a general recursive/global function representation in Semantic Core;
- runtime evidence beyond the profiles accepted by the ADR-0342 linker; or
- lowering for constructors, matches, nominal data, members, place-aware
  assignment, general control flow, and the other unsupported source forms.

These cases reject at their existing checking, specialization or linking
boundary.  The composition API does not weaken those gates or manufacture
runtime behavior for them.

## Consequences

Lean consumers now have one stable entry for the implemented vertical source
slice and no longer need to reproduce the six-stage orchestration.  Tests can
exercise both declaration-ID and module/name selection through the same public
path, including generic specialization, direct-call discovery, linking,
runtime input checking and execution.

The API remains honest about the current profile: "public" means a supported
Lean library boundary, not a claim that arbitrary Solcore source is executable
or that the Oracle accepts source programs.

## Verification policy

Executable positive and negative tests cover both seed selectors, generic
arguments, calls, bad names and declaration kinds, specialization-budget
exhaustion, unsupported recursive or indirect plans, runtime input mismatch,
and observable execution.  As in ADR-0342, broad composition and completeness
theorems remain deferred while `sorry`, `admit`, authored axioms, `unsafe` and
`native_decide` remain forbidden.
