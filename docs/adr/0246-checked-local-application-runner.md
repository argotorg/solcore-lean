# ADR-0246: Checked local application execution on actual local inputs

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Separate executable single-argument call endpoint

## Evidence and decision

Exact original single-argument application typing, raw evaluation, costs and
runtime-world safety are now available. Add a separate checked execution endpoint
on the existing `LocalInputs` record. Its ordered bindings already supply the
names, context and actual environment with matching unique IDs. Do not construct
a replacement context or value list, and do not change the existing record.

`LocalInputs` carries structural `ValueHasType` evidence, not a runtime store
world. Its existing pure-expression checker and runner have stronger store and
fault guarantees because their grammar excludes invocation. Keep those existing
definitions, acceptance and generic contracts unchanged. The primary local
evidence is `LocalInputs.lean`, its projection properties, `LocalInputsExecution`
and the application correspondence/safety established in ADR-0243–0245. No new
Rust Function interpretation or frontend acceptance policy is introduced.

Add `LocalInputs.checkApplication?`, delegating to the exact static application
adapter on the existing names and context. Add `LocalInputs.runApplication?`,
running that checked Core with the actual input values, supplied fuel and actual
store. Its result is `Option (Core.Ty × Core.StatefulRunResult)`. There is no new
external-value decoder, world validator, parser entry, source-call interpreter,
whole-function preparation or entry integration.

Outer `none` means that this static adapter produced no checked application.
It is independent of fuel and store. Successful checking preserves every inner
Core result, including actual `.fault` and `.outOfFuel` states, with the original
static result-type tag. In particular, structurally typed inputs with a reader
and a wrongly typed allocated payload can return `some (Word, done Bool ...)`;
an unallocated reference can fault. Do not suppress either result or assert
value typing from the tag alone.

Prove exact static checking and whole typing correspondence, full-result
factorization, absence characterization, successful raw evaluation soundness,
and completion iff whole typing plus independent source evaluation. Exact raw
costs plus whole typing give exact done/exhaustion thresholds. The whole-typing
premise is essential: selected raw success can coexist with a rejected unselected
branch. No source-only cost bound or unchanged-store conclusion is introduced.

Genuine exhaustion preserves the complete saved Core state. Prove the exact
remaining path/cost and full-result resumption equality, including fault and
exhaustion outcomes and the same static type tag. Resume `Core.runStateful` from
the saved checkpoint; do not restart source evaluation or rebuild its frames,
environment or store.

Explicit same-world runtime environment and store typing separately justify
typed completion, a sufficient actual cost, extending-world preservation and
all-fuel fault exclusion for the closed endpoint. These premises concern the
same actual projections consumed by the executable definition. `LocalInputs`
automatically discharges ID alignment but not runtime-world obligations.

## Validation and boundaries

Independent consumers construct input records once, retain all projections, and
derive original child and actual body evidence before checker/runner comparisons.
Use a captured reader for valid, missing and wrong-payload stores; retain its
cost8 and genuine cost3 checkpoint with residual5, including resumption to fault.
Use typed delayed bodies with cost `3*n+6`, strict writer cost15 and allocator
cost8 with actual stores/captures. Contrast an unselected missing branch's raw
success with whole rejection. Preserve original parsed fields and complete
declaration parameter records; the new local endpoint must not silently enable
old pure or whole-function entries. Higher-order nominal function values are
legitimate actual arguments without manufacturing nominal data inhabitants.

Keep definitions, checking/execution proofs, exact-cost/resumption proofs,
runtime-world proofs, consumers and publication in small commits, each new file
below 300 lines. Require focused and aggregate builds, full tests, all public
and consumer standard-axiom audits, kernel/metadata/whitespace checks and
independent reviews. Diagnostics, Core/Resolved, parser and wire definitions
remain unchanged.
