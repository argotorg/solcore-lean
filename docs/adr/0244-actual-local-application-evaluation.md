# ADR-0244: Actual local application evaluation and exact costs

## Status

Accepted.

## Context

The opt-in single-argument adapter fixes both original pure children and their
ordered Core application. Its static result does not supply an actual closure,
argument, capture environment, allocated store, or terminating body. Existing
pure-source store and source-only fuel laws cannot be extended to invocation.

The pinned Rust reference remains
`18fd9f75d290df0070e21ee56e0a5691f232596f`. The Function/Invokable specialization
and original single-argument boundary are unchanged from ADR-0243. This decision
adds Lean execution correspondence, not a new Rust lowering or gas-cost claim.
The runtime evidence is the existing `Core.Evaluates.apply` rule and the
`enterApply`, `beginArgument`, and `invokeClosure` machine transitions. They
evaluate the argument in the caller environment, then evaluate the actual body
under the actual argument followed by the captured environment. Closures capture
values, including cell references, rather than a store snapshot.

## Decision

Add separate independent successful source-call and cost-indexed judgments.
Both retain the original root span, argument-list span, callee, and sole argument.
Their first two premises are the existing pure-source child evaluations, in
the same caller identity environment and in callee-before-argument order. The
third premise evaluates the body contained in the resulting actual closure,
under `argumentValue :: capturedEnvironment`. All intermediate and final stores
are explicit. The raw premise uses Core big-step evaluation of that actual
runtime body; it does not evaluate the output of the application checker.

The cost rule uses exact pure-child costs and a closed exact Core path for that
actual body. The total is `functionCost + argumentCost + bodyCost + 3`.
The three extra transitions are the application protocol, not frontend work,
lookup work, gas, or elapsed time. A private general continuation-append proof
lifts that known body path at the same cost, with no local-fragment premise.
An application composition theorem retains every supplied continuation without
executing its pending frames. Cost existence precedes quantification over those
continuations; no continuation-dependent choice of cost is substituted for it.

Prove raw determinism, erasure, cost existence, positive and unique costs, and
exact Core evaluation/path correspondence for independently elaborated original
calls. Runtime/source scope alignment is equality of the ordered identity lists,
not merely equal lengths. Checker-facing corollaries consume the exact static
soundness theorem. No environment typing is required for these conditional
correspondences; actual closure annotations must not be equated to the static
Function type without a separate runtime typing premise.

Keep executable source evaluation and whole-function entry integration separate.
This unit provides no source-call runner, new whole-body grammar, or automatic
termination/no-fault theorem. Existing Core run/fuel/resumption laws can be
consumed for a supplied successful exact path, including genuinely suspended
checkpoints. A returned value with a nonempty continuation is an endpoint, not
necessarily a completed run, and the pending continuation can immediately fault.

## Boundaries and validation

Pure callee/argument stores are unchanged by existing laws. The actual body may
allocate, read, or update cells, return captured values, or have arbitrarily
different costs for the same source call. Structurally typed cell references do
not establish allocation. A selected raw conditional child can succeed while
the whole static child rejects an unselected branch. Neither circumstance may
be hidden by fabricating runtime values or weakening a checker premise.

Consumers construct original child lookup/evaluation and actual body proofs
independently, then use the generic correspondence. Cover sparse/duplicate
first-match rows, distinct actual arguments and captures, noncommutative argument
evaluation, Unit/products as one argument, actual effects, delayed bodies,
static/raw separation, same-type non-original Core replacements, and pending
continuation faults. Parsed consumers retain the original AST and complete
function-declaration/entry rejection boundary. Costs and checkpoint expectations
are constructed independently rather than obtained from the implementation.

Use small separate definition, proof, consumer, and publication commits. Require
focused and aggregate builds, full tests, all public and consumer axiom audits,
kernel-policy and whitespace checks, and independent reviews. No existing parser,
Core/Resolved definition, body/entry contract, diagnostic policy, or wire changes.
