# ADR-0183: Exact resumption from genuine frontend fuel checkpoints

- Status: Accepted
- Decision date: 2026-09-08
- Scope: existing Core runner resumption and source-cost residual paths

## Decision

Prove that if the existing Core runner exhausts `spent` fuel at the actual
state `checkpoint`, running that checkpoint with `additional` fuel gives the
same full result as running the original state with `spent + additional` fuel.
This law concerns arbitrary Core states and does not require typing or known
termination. The checkpoint must come from the actual exhaustion result; an
arbitrary state or a terminal/fault result is not interchangeable with it.

For a known independent terminating Core path of exact length `cost`, derive
`spent < cost` and a residual path of exactly `cost - spent` transitions from
that genuine checkpoint to the same final value and store. Derive exact
completion and exhaustion thresholds for every additional fuel budget. Final
recognition remains free, so no new resumption transition is charged.

Lift those laws through existing source cost correspondence and checked local
expressions, singleton return bodies, and complete runtime entries. A source
checkpoint is obtained from its existing endpoint's actual `outOfFuel` result;
whole checking/preparation and actual compiled Core remain in the contract.
Also expose residual paths for independently compiled entries using existing
source cost evidence and compilation provenance. No new runner, checkpoint
record, evaluator, source small-step relation, or serialized continuation is added.

## Boundaries

Do not recreate an initial state at a checkpoint. Retain the actual control,
continuation, environment, and store; dropping a pending frame changes both
results and remaining costs. Additional fuel is a budget for the remaining
path, not a fresh copy of the source's original exact cost. No assertion about
equal checkpoints under different argument values or different stores is made.
Unselected invalid branches still cannot bypass whole checked entry rejection.

Host requests and host-driver resumption are separate interfaces. This unit
handles Core `outOfFuel` only, not host responses, new source calls/effects,
fault recovery, checkpoint editing, or arbitrary-program termination.

## Validation

Exercise zero-spent checkpoints, pending unary/binary frames, short-circuit
paths with different costs, and multi-chunk execution with full result equality.
Independent consumers retain source derivations and exact residual costs;
fully parsed entries test every genuine checkpoint below a known exact cost,
with remaining fuel below, at, and above the residual threshold. Include a
counterexample for discarding a continuation and whole rejection fixtures.
Audit and register every public declaration, run focused/aggregate builds and
full tests, and retain standard-axiom, kernel, forbidden-token and
whitespace checks. Keep files below 300 lines, commits small, and diagnostic
proofs untouched.
