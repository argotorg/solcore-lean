# ADR-0206: Recursive return-tree fuel and resumption

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Checked body runner, recursive source bound and genuine checkpoints

## Decision

Add `LocalInputs.checkTerminalReturnTree?` and `runTerminalReturnTree?` for the
separate recursive body adapter. The runner executes exactly the accepted Core
with the actual ordered environment values and supplied store. It does not
reverse values again or construct a replacement Core. Checking failure is absent;
successful checking retains the complete present machine result, including its
real suspended state. No runtime-function entry profile changes in this unit.

Known independent source cost and whole acceptance characterize fixed-fuel Core
completion and exhaustion under aligned identities. Completed Core runs reflect
back to an independent source cost within the supplied fuel. At the proof-carrying
`LocalInputs` boundary, characterize exact results, failed checking, typed-cost
completion/exhaustion, typed evaluation existence and absence of machine faults.
Do not infer generic safety from static acceptance and identity alignment alone:
actual runtime typing remains essential to existence and sufficient-fuel safety.

Define a total `terminalReturnTreeFuelBound` by the size of the original block.
Singleton leaves retain the existing return bound. Explicit conditionals use the
condition bound plus the maximum of both recursive arm bounds plus two. Other
whole shapes receive zero, which certifies neither checking nor execution. Prove
the upper bound for raw cost evidence without a whole-typing premise; combine
acceptance with actually typed, aligned inputs for sufficient-fuel completion.

This is a conservative upper bound, not an exact minimum fuel requirement. A
depth-two variable-return tree may need seven transitions on its long path but
four on its short path, with recursive bound seven. The old nonrecursive bound
can be four on that same source and must not be reused for the recursive runner.

Resume only a genuinely returned exhaustion state. Retain its original control,
environment, pending frames and store; prove the exact unconsumed path of length
`cost - spent` and equality of resumed execution with a larger original run.
Do not reconstruct a checkpoint or discard its continuation. Core recognizes
completion and faults even at zero remaining fuel; arbitrary pending-frame paths
are not automatically exhaustion observations. The new body runner starts with
the empty continuation, and its no-fault law uses real typed inputs.

Preserve all optional runtime results on old singleton or one-level
singleton-arm shapes, at every fuel and store. Reuse exact static shape equalities
and the unchanged Core runner. These equalities do not extend to arbitrary deep
trees, whose old checker still rejects them.

## Boundaries and validation

No entry integration, source calls, mutation, loops, fallthrough, parser, Core,
Resolved or frozen-interface changes. Identity/store replay invariance follows
separately. Consumers cover arbitrary actual typed payloads, opaque cells and
closures, asymmetric costs/bounds, all fuel thresholds, genuine multi-chunk
checkpoints, missing/invalid skipped arms, unsupported zero bounds and unchanged
old entry rejection. Distinguish aligned untyped faults from typed-input safety.

Audit all public declarations and consumers with standard axioms only; run
focused/aggregate builds, full tests and kernel/metadata/whitespace checks.
Keep proof files below 300 lines, commits small, diagnostics paused and all
scratch files inside the repository.
