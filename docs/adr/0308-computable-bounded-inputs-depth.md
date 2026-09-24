# ADR-0308: Compose outer-call depth from two successful bounded inputs

## Status

Accepted.

## Context

ADR-0307 removes the callee data gate under a supplied finite successful callee
run, but still requires data-expression argument syntax. An argument application
in `f(g(x))` is not admitted by that gate. Its independent finite successful run
can instead supply the actual argument value and intermediate store.

This is a separate conditional contract. Replacing an argument syntax gate by
an explicit successful argument premise does not strengthen ADR-0307's decision
for failed arguments. The earlier theorem and all its assumptions stay intact.

## Decision

Define `boundedInputsLambdaDepthBound calleeBudget argumentBudget body` as the
maximum of the two supplied budgets and the actual saved data-body bound, plus
one. Require two exact finite successful evaluator equations: the callee starts
from the original initial store, and the argument starts from the actual callee
store. The first fixes every selected source-closure field; the second fixes the
actual mixed argument value and argument store.

Retain `SourceUnaryLambdaShape` for the actual saved source and a syntax-only
`ClosedSourceDataBody` gate for its selected body. Neither input needs a data
expression gate. There is no successful saved-body admission premise. All four
decision laws explicitly include both finite successful input equations.

Obtain independent original input witnesses from old evaluator soundness.
Invert an original whole call, use determinism to fix all saved closure fields
and the callee store, and use shape uniqueness for the parameter and body.
Argument determinism then fixes its actual value and store. Lift both supplied
runs using old success monotonicity; only the freshly extended saved body uses
its existing direct syntax-depth proof. Preserve every intermediate store and
the complete actual final endpoint.

Derive exact full-endpoint success iff, whole Option stability above the bound,
sufficient-depth None iff no original outer-call success, and bound None iff
None at every budget. These laws do not find either successful input budget or
classify input failures under their successful-input assumptions. No eventual
completeness, threshold or image theorem is used to supply a child budget.

## Independent checks

Symbolic consumers first build original creation, reference, nested argument and
fresh-body witnesses, then independently establish the evaluator recurrence,
before using these laws. Starting from f(x), n further nested outer calls have
sharp depth n+3. Arbitrary mixed argument values, independent caller/saved owners
and duplicate rows, inert annotations and separate creation/invocation stores
are retained. The inner argument call is explicitly outside the data gate.
Supplying both successful child budgets at n+k+4 yields outer bound n+k+5 even
though the actual outer call already succeeds at n+4 and at the bound minus one.

Negative consumers keep both supplied inputs successful while independently
excluding original success of the actual saved body. A selected string return
cannot succeed. A saved name with no capture cannot use a successful caller
lookup; freshness also prevents the new argument binding from filling that
missing capture. Original exclusions precede the depth laws. Independent concrete
applications use three distinct owners, duplicate rows and five-element mixed
stores to show that both successful input premises can hold together.

Parsed consumers compare the complete handwritten `f(g(x))` AST, every span,
EOF and zero diagnostics. Both closures are independently created and their
actual fields retained through the outer callee and inner argument runs. The
actual callee store feeds the inner call; its actual argument value/store feed
the fresh saved body, whose actual complete result/store feed the outer checks.
Independent caller x lookup fixes the planned mixed argument before new laws.
The 32 cases cover fresh-parameter returns, saved-free returns, missing saved
captures and missing saved names, with separate saved/caller environments and
mixed values/stores. Inner depths 0/2/3 and outer depths 0/3/4/7 are checked
separately. No failed input is presented as a use of the new conditional laws.

## Preserved boundaries

No existing evaluator, original judgment, source gate, image statement or proof,
primitive, selector, lowering, typing, annotation policy or parser changes.
This is not budget discovery, unconditional general-call termination, runtime
typing, staging, Core cost, effect, fault classification or closure conversion.
Parser and diagnostic proof work remains paused.

Keep every proof file below 300 lines and every commit within 300 changed lines.
Require complete focused/full builds, tests, kernel-policy and whitespace checks,
independent semantic consumers and reviews, exact source ports, public proof
checks and actual formal-module ownership inspection. Retain all versions and
failed captures; only the standard three proof axioms are permitted.
