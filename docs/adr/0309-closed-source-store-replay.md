# ADR-0309: Preserve and replay the external store in closed source evaluation

## Status

Accepted.

## Context

The existing closed source fragment has 17 expression rules and 9 body rules.
Neither these rules nor their shared-depth evaluator read or write the store.
Source closures capture source, owner, names and values, not the external store.
This permits an exact store law independently of syntax gates or call-depth
bounds. Opaque Core closures, host functions and cell references remain values;
their presence does not authorize execution or dereferencing.

## Decision

Prove that every original expression/body success returns its initial store.
Replay the same original success from any replacement store, returning the same
complete runtime value paired with exactly that replacement. Keep all lexical
rows, duplicate lookup priority, saved fields, fresh IDs and chosen match arms.
Use simultaneous original induction for expression/store laws and exact original
body compatibility for the body replay wrapper.

For each finite evaluator, prove at exactly the same supplied budget that its
result on a replacement store equals mapping its original Option endpoint to
the same value and the replacement store. A private simultaneous budget proof
directly covers every evaluator branch. Public laws have no source gate, typing,
successful-child or successful-whole-evaluation premise. The None case follows
by reverse same-budget replay, without discovering or enlarging a budget.

Store replacement does not alter captures or stores nested inside opaque values.
In a call the actual callee is evaluated before the actual argument, and only
then is the source-closure shape checked. The new laws preserve that ordering;
an unsupported host callee does not imply that its argument is skipped.

## Independent checks

Symbolic consumers build original witnesses and direct finite runs before using
new laws. Cover source-closure creation, nested saved identity calls, skipped
failing children, inferred/typed fresh bindings and arbitrary ordered Word-match
misses before the first hit. Replacement stores are universally quantified.
Mixed source/Core closures, host functions, duplicate rows and opaque cell
references test complete values, not a normalized subset. Low-depth None and
sufficient-depth success are independently obtained before same-budget replay.

Negative consumers independently exclude original missing-capture and host-call
success and prove all-budget None directly. Both callee and argument references
have independent successful witnesses in the host-call boundary. Changing a
store cannot fill a lexical capture or make that host callable in this fragment.

Parsed checks compare complete handwritten ASTs, every span, EOF and diagnostics
for two lambdas, f(x), and a short circuit. Twelve saved calls combine two bodies,
three mixed value pairs and two initial stores; each uses three unrelated
replacement stores. Actual creation fields, caller arguments and fresh saved-body
endpoints precede all replay applications. Two distinct store contexts also check
short-circuit success, missing references and a non-Bool condition.

## Preserved boundaries

No original rule, evaluator, source gate, image theorem, primitive, parser,
diagnostic or typing implementation changes. None still conflates insufficient
depth with unsupported execution. No termination, budget search, fault classifier,
Core execution, effect or cost theorem is claimed. Returned cell references need
not be valid in the replacement store: this is not runtime-world preservation.

Keep proof files below 300 lines and commits within 300 changed lines. Require
focused/full builds, tests, policy checks, exact source ports, independent
consumers/reviews, all-public proof checks and complete actual module ownership
inspection. Retain all proof versions and failed captures. Public dependencies
may use only the standard three proof axioms.
