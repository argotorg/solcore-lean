# ADR-0211: Checked typed let-prefix fuel and resumption

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate checked body runner, source bound and genuine checkpoints

## Decision

Add `LocalInputs.checkTypedLetReturnBody?` and `runTypedLetReturnBody?` for the
profile of ADR-0209/0210, with explicit caller type meanings and owner. Checking
uses `inputs.toTypeInputs`; execution uses the actual accepted Core, the original
ordered `inputs.environment.values`, the supplied store and an empty continuation.
Do not reverse the values again, reconstruct inhabitants from static types or
extend the existing tree and runtime-function entry adapters.

Lift independent exact costs to completed/exhausted fuel thresholds. Generic
known-cost and completed-run correspondence needs only whole acceptance and
aligned IDs. At the actual typed-input boundary, retain exact optional results,
whole-source typing and independent value/store/cost witnesses. Typed execution
exists and cannot fault, for every supplied store; raw success for an unsupported
annotation or repeated name must not bypass whole checking.

Define a total source-only `typedLetReturnBodyFuelBound`: an annotated and
initialized let prefix adds its initializer expression bound, its remaining
prefix bound and two. Other shapes reuse `terminalReturnTreeFuelBound`. Recursion
consumes the original statement list, without fuel or a length limit. Annotation
meaning and name freshness are not numerical premises: raw paths can exist even
when these checks fail. Raw costs are bounded independently of typing/checking;
sufficient-fuel safety additionally needs actual aligned, typed runtime values
and whole acceptance. A rejected body need not have bound zero. Neither zero nor
a positive numerical budget is an acceptance or runtime-inhabitation witness.

An actual exhausted state supplies the only checkpoint. Lift its exact remaining
path of length `cost - spent` and show that resuming this complete state equals
the corresponding longer original run. Preserve the initializer's pending let
frame, the original environment captured there, the actual bound value added to
the tail and every enclosing continuation/store component. Do not recreate a
checkpoint by restarting the source or dropping pending frames. Multi-chunk
consumers must use states obtained from the preceding run.

Preserve full optional body results for old singleton returns and singleton
explicit if/else shapes, including failed checks and complete suspended states.
Compare against the existing return/tree/one-level conditional runners only on
their corresponding original shapes; valid let prefixes are new success and
cannot satisfy arbitrary-body equality with the old tree adapter.

## Boundaries and validation

No parser, Core, Resolved, Wire, source-call, inference, default-initializer,
shadowing policy, arm-local let, mutation, early-return or runtime-entry extension.
This checked body runner is distinct from whole-function provenance. Actual cell
references and captured closures remain opaque values, not evidence of allocation
or invocation. Arbitrary data-only Core records and aligned but untyped
environments do not acquire general safety.

Use independent source proofs and completely parsed actual-argument consumers.
Cover arbitrary-length prefixes, exact child-sum costs and conservative bounds,
asymmetric terminal choices, noncommutative initializers, all relevant fuel
thresholds, nonempty stores, real initializer/tail checkpoints and several
resumption chunks. Retain wrong/unsupported source rejection even at generous
fuel, unsupported zero/nonzero budget contrasts, old-shape full Option equality,
and counterexamples to restarting or dropping continuations. Audit all public
contracts and consumers, standard axioms, registration and dependency direction,
focused/aggregate builds, actual parsed execution, full tests and policy checks.
Keep proof files below 300 lines, commits small, diagnostics paused and scratch
files inside the repository.
