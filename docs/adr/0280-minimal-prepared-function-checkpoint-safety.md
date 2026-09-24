# ADR-0280: minimal prepared-function checkpoint safety

## Status

Accepted; additive frontend-semantics proofs. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. Existing executable definitions,
source admission, original syntax and every earlier contract stay unchanged.

## Context

Independent shared function preparation retains actual arguments and captures.
Its existing runtime execution theorem also relates source evaluation, exact
costs and an optional checker. Those conclusions correctly require substantial
child execution, insertion, fragment and checker-correctness premises.

Safety of the prepared Core state is a smaller claim. The shared body already
has checkpoint safety and world-extension laws requiring only child Core typing
and a common runtime world for the actual environment, store and pending frames.
The function entry does not yet expose this boundary directly from its original
argument list and independent preparation evidence.

Structural argument typing is insufficient for this claim. A captured cell
reference can be structurally typed but absent from the supplied store. Likewise,
well-typed actual arguments do not validate an incompatible store or arbitrary
pending continuation. Preparation cannot repair those mismatches.

## Decision

Add `ComputationFunctionRuntimeCheckpointProperties` with two public laws:

- `ComputationFunctionPrepares.runtime_checkpoint_safety`;
- `ComputationFunctionPrepares.runtime_checkpoint_world_extension`.

Both quantify over the same arbitrary independent child elaboration relation.
Assume only its Core typing consequence, original independent preparation,
runtime typing of every supplied actual argument in one world, typing of the
separately supplied actual store in that world, and typing of the actual pending
continuation from the prepared return type to its caller's result type.

The first law types the literal initial state, excludes faults at every fuel,
and types every genuine out-of-fuel checkpoint while excluding faults for every
amount of additional fuel from that exact saved state. It retains the complete
control, environment, continuation and store; it does not restart preparation.

The second law identifies a world for a genuine saved store extending the
original supplied world. Every further finite Core path from the exact saved
state has a typed store in a world extending that saved world. The world is
existential; do not equate it to a guessed list or the unchanged initial world.
Consumers may identify it using independent actual store evidence.

Keep the two conclusions separate so consumers of safety alone need not unpack
world-extension evidence. Reuse the existing body laws and keep the short
actual-argument-to-runtime-environment bridge private. That bridge uses original
parameter layout and reverses the supplied values and types exactly once.
Do not add four unrelated static/fragment wrappers or duplicate Core safety.

No child checker, checker-correctness graph, raw evaluator, cost relation,
fragment predicate, weakening/insertion/path law, source-ID alignment, runtime
inhabitant construction or termination premise is needed in these statements.
No matching conclusion about an arbitrary optional checker is inferred.

## Consumers and verification

Construct original independent preparations, not checker graphs. Exercise
symbolic source nesting and actual closures/captures. Apply the new laws with
actual runtime-world evidence, genuine checkpoints and further literal paths.
Retain existing source-cost and Core-path evidence separately when used to
identify concrete execution; the new laws do not establish that correspondence.

Parse original functions with ordered effects, hidden discard slots and shadowed
locals. Verify actual store growth, saved states and subsequent execution,
including a typed caller continuation that can itself allocate or write.
Distinguish structural preparation from runtime safety with missing-reference,
incompatible-store and ill-typed-continuation cases. Distinguish independent
preparation from a separately supplied checker returning no result.

Require focused and aggregate builds, full tests, exact standard-only public and
consumer axiom catalogs, independent reviews, preserved old bytes/signatures/
imports, and kernel-policy, EOF, and whitespace checks. Keep new proof and consumer files
below 300 lines. Record decision, proof, consumers and publication separately.

## Non-goals

No source admission, diagnostic/parser changes, new raw function semantics,
checker acceptance result, termination, exact source cost, unconditional store
safety, runtime-world synthesis, or changes to earlier contracts and consumers.
