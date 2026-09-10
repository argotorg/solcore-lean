# ADR-0290: executable depth-bounded closed source evaluation

## Status

Accepted; follows the completed ADR-0289 source judgments.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
Production follows the reviewed four-module, eight-declaration contract below.

## Motivation and exact scope

The callback-free original source judgments now support higher-order source
closures, but they are propositions, not functions that run arbitrary inputs.
Provide a terminating executable search for exactly the existing eight expression
and nine body forms, without adding Core/host dispatch, effects or syntax cases.
Preserve every old definition, constructor, theorem and entry point unchanged.

Use a natural-number recursion-depth budget rather than structural recursion on
source syntax: a saved closure body can call itself through actual higher-order
arguments. Finite source and finite captured data do not imply termination.
Successful finite derivations should eventually be found at all sufficiently
large budgets; no budget depending only on source size is promised.

## Independent ordered choice

Introduce chooseRuntimeWordMatch? over an actual RuntimeValue, the original
ordered cases and optional original default, returning Option (Block × Nat).
Implement structural recursion over the original case list and reuse the existing
interpretWordMatchPattern? function and its independent classification iff.

An empty list returns only its original default with zero comparisons.
A first wildcard succeeds for every actual value and never inspects the suffix.
A visited literal requires an actual Word: compare it once, return the first hit,
or recurse on the untouched suffix on a miss and increment the returned count.
A non-Word at a literal, unsupported original pattern, or absent final default
returns none. Do not project arbitrary closures/stores or skip unsupported cases.
Prove an exact result/body/count iff with RuntimeWordMatchChooses.

The returned count remains literal comparisons, not evaluator fuel or Core cost.

## Mutually recursive executable functions

Introduce evaluateClosedSourceExpression? and evaluateClosedSourceBody? with
budget, owner, ordered name rows, ordered actual captures, initial raw store and
original Expr/Block inputs. Return Option (RuntimeValue × List RuntimeValue).
Keep stores explicit and thread every actual intermediate store in the same
callee-argument-saved-body or child-tail order as the independent judgments.

Both functions return none at budget zero, including leaves and creation.
At successor budget, every recursive expression/body child receives the predecessor.
Sequential children each receive that same predecessor budget: this is a depth
bound for the successful derivation, not a consumed-step counter or resumable fuel.
The separate total pattern/case scan does not consume this recursion budget.

References use existing first-name then first-ID lookup functions. Word literals
use the strict existing decoder; groups and empty/pair/many tuples preserve exact
original child/suffix data and spans. A manually constructed singleton tuple has
no successful branch. Creation uses sourceUnaryLambdaShape? and captures original
source/owner/rows without interpreting annotations or running the body.
An original unary call evaluates the original callee and argument at caller scope,
requires an actual sourceClosure and original supported saved shape, then evaluates
the saved body with the same names-only fresh parameter row as ADR-0289.

Mirror all nine body constructors. Let initializers use pre-binder rows, typed
and inferred syntax stay original, strict discard keeps rows, explicit blocks keep
their original inner span, Bool condition and Word selector evaluate only the
selected original branch. Do not check unvisited bodies or annotation meanings.
No fallback branch silently adds unsupported syntax or normalizes source nodes.

## Proofs and minimal public surface

Prove expression and body soundness: each concrete some (value, finalStore)
result yields the exact ClosedSourceExpressionEvaluates/ClosedSourceBodyEvaluates
derivation at the same original inputs and actual endpoints.
Use simultaneous budget induction, not checking or Core evaluation premises.

Prove expression and body eventual completeness: from each independent finite
derivation, there exists a required budget such that every budget at least that
large returns the same actual result and final store. Use the joint derivation
recursor and take maxima of the children's existential thresholds, plus one.
This stronger eventual statement avoids a separate public monotonicity helper.
It does not classify inputs lacking finite successful derivations.

Target eight public declarations in four modules: RuntimeWordMatchSelection
(choice function and exact iff), ClosedSourceEvaluator (the two mutual functions),
ClosedSourceEvaluatorSoundnessProperties (two soundness laws), and
ClosedSourceEvaluatorCompletenessProperties (two eventual completeness laws).
Keep each below 300 lines. If the actual proof does not fit, revisit the split
before enlarging the public interface or weakening the exact result contract.
Helper lemmas stay private; do not introduce a fuelled declarative grammar family.

## Observable boundaries and validation

None intentionally conflates insufficient budget with lack of a supported
successful path. It is neither a source-language type error, a runtime fault nor
a divergence certificate. This evaluator is not the canonical Core machine,
does not return resumable states and does not measure transition costs.
The existing raw name/staging boundaries remain: no whole-source acceptance,
typing, canonical resolution, global references or general runtime safety.

Independently construct source derivations before using completeness, and inspect
actual some results before consuming soundness. Cover budget-zero/threshold cases,
nested and higher-order calls with literal captures, arbitrary tuple/body nesting,
original selection order, and non-Word literal-first absence. Preserve actual
source closures rather than checking only projected Core outputs.
Run the established focused/aggregate/full, standard-only public/consumer,
old-contract/import, independent-review, metadata and small-commit checks.
