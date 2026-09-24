# ADR-0252: An explicit mixed-computation function entry

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Original headers and actual arguments around the mixed body profile

## Evidence and decision

ADR-0251 supplies exact checking, typing and effect-aware Core correspondence
for original mixed bodies. Its consumers bind original function parameters but
deliberately do not introduce whole-function acceptance. Existing explicit
entries separately accept pure recursive bodies or singleton applications.
Connect the mixed body through a separate entry, preserving both older endpoints.

Retain the original signature, parameters, body, owner and ordered type table.
Reuse RuntimeFunctionHeader and RuntimeParametersDeclare/Bind without changing
their policies: no implicit global resolution, inferred header policy, generic
entry, modifier expansion, alternate argument packing or shadowing is introduced.
The pinned Rust statement evidence and restricted terminal-control boundary
remain those of ADR-0251; accepting a child does not bypass the original enclosing
return contract.

Define RuntimeComputationFunctionCompiles and RuntimeComputationFunctionPrepares
as independent whole-entry evidence. Both combine the original header and
parameters with LocalComputationReturnTreeElaborates at the declared return type.
Compilation uses value-free parameter inputs. Preparation binds the actual
supplied typed arguments and uses that very record's toTypeInputs for checking;
its runtime values and captures remain in the original record.

Reuse CompiledRuntimeFunction and PreparedRuntimeFunction as data-only records.
Their ownership imports do not grant old pure-body provenance or safety laws.
The three new executable endpoints compileRuntimeComputationFunction?,
prepareRuntimeComputationFunction? and runRuntimeComputationFunction? retain
header/parameter/body/declared-return failure as None. Running uses the exact
prepared Core, actual environment and separately supplied store. Faults and
genuine exhaustion remain present results with the declared static return tag.

## Minimal proof interface

Publish four contracts, with decomposition and reconstruction helpers private:

1. Compile Some of the exact record iff independent new compilation evidence.
2. Prepare Some of the exact record iff independent new preparation evidence.
3. Full-Option preparation projection equals compilation followed by the exact
   ordered argument-type guard.
4. Full-Option running equals compilation and that same guard followed by Core
   running on the original arguments' values in reverse order exactly once.

The guard compares argument types in source order with the reverse of the
compiled parameter context. It includes arity and order. It does not reject a
swap of same-typed arguments, and such a swap may change actual captures,
results or effects despite an unchanged compiled projection. Binding fixes
actual values, not the store later supplied to execution. Do not infer values
from type erasure or invent inhabitants for a nominal static compilation.

The two Some iff laws already support complete/sound/absence/uniqueness uses;
do not republish those as parallel wrapper families. Body Core typing and
raw/exact-cost correspondence are available through the preparation's body
field. Consumers can form an actually typed Core state using explicit runtime
world/environment/store and continuation evidence, then reuse generic Core
safety and resumption. Structural argument typing alone is not that evidence.

Old successful pure provenance embeds using ADR-0251's same-Core/type theorem.
A singleton application's old body case directly constructs the new expression
case. Test these one-way compatibilities without changing old acceptance or
claiming full equality of old and new Options: new mixed bodies were old None.
General source-function values, global calls, nested expression applications,
arbitrary-store safety, source-only fuel bounds and unfuelled total evaluation
remain outside this entry.

## Validation and rollout

Use independent source, parsed-static and actual original-function consumers.
Cover pure compatibility, mixed call initializers/discards/guards, returned
callables, effects through actual stores, same-typed argument swaps, nominal
value-free compilation, whole-header/return/argument rejection and full fault
or checkpoint/resumption outcomes. Fix expected Core and actual value/store/cost
independently. Keep the old header gate distinct from a successful body check.

Separate decisions, definitions, proofs, consumers and publication in small
commits, with new proof/test files below 300 lines. Require focused/aggregate
builds, full tests, all public/consumer standard-axiom audits, dependency and
kernel-policy and whitespace checks, and independent reviews. No Core, parser,
diagnostic, old entry, runtime-record or old body definition changes are needed.
