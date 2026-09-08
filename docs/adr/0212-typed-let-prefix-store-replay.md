# ADR-0212: Typed let-prefix store replay

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Independent store replay and checked body observations

## Decision

Extend the separate typed let-prefix profile of ADR-0209/0210/0211 with store
replay. Fix the original body, owner, explicit name table and actual runtime
environment. A raw path replays from any replacement store with the identical
returned value and that replacement as its final store. The costed path also
retains its exact cost. Prove these facts directly by induction on independent
source paths: replay each initializer and the remaining prefix at the new
store, retaining the actual initializer value in the extended environment.
The terminal suffix reuses recursive return-tree replay.

These raw laws require neither whole checking nor typing, usable annotation
meanings, non-shadowing names or aligned environment IDs. They do not turn a
raw path through rejected source into a checked program. Fresh IDs depend only
on the unchanged owner and name table; this unit neither renames IDs nor claims
that arbitrary renaming commutes with allocation.

Give bidirectional raw and costed store characterizations. A path with an
arbitrary purported final store exists exactly when that final store equals
its initial store and the same value/cost path exists at the replacement.
Store preservation alone is not used as a substitute for replay existence.

At the actual typed `LocalInputs` boundary, whole typing and cost contracts
transport completed observations with the same returned type and value, each
carrying its own initial store. Transport exhaustion presence at the same fuel
and returned type. These are equivalences, including rejected bodies, with no
additional whole-acceptance premise required of the caller. Checking and the
numerical source bound remain unchanged and retain all existing boundaries.

## Boundaries and validation

Do not equate complete results or suspended states across distinct stores.
Actual initializer checkpoints keep their pending let frames, captured old
values and own stores; resumed runs must start from these genuine states.
Existing cells and closures are opaque actual values, not evidence of allocated
locations or invocation. No general Core store independence, mutation, source
call, parser, Resolved, runtime-entry, inference or binding-policy extension.

Use independent source consumers and completely parsed actual-argument tests.
Cover arbitrary-length prefixes, strict unused/noncommutative initializers,
asymmetric terminal paths, arbitrary values and distinct nonempty stores.
Distinguish raw replay from whole checking, incorrect final-store claims from
own-store observations, and equal control/continuation from unequal complete
checkpoints. Exercise same-fuel completed/exhausted equivalences and genuine
multi-chunk resumes; preserve old-shape behavior and whole rejection.

Audit all public contracts and consumers for standard axioms and exact public
registration. Run focused/aggregate builds, actual parsed execution, full tests,
kernel/metadata checks and dependency-direction checks. Keep new proof files
below 300 lines and commits small; diagnostics remain paused and scratch files
remain inside the repository.
