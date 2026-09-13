# ADR-0310: Exact saved self-application has no finite successful endpoint

## Status

Accepted.

## Context

Closed source evaluation admits raw unary lambda self-application. Eventual
completeness discovers every finite successful derivation, but does not promise
that every source expression has one. An explicit re-entry example makes this
boundary precise without extending the evaluator or classifying arbitrary None.

## Decision

Define a syntax-only `SourceSelfApplicationBody` relation for a single return of
two identifier references used as callee and argument. Both spellings equal the
parameter's spelling; all original spans remain independent and literal.
Use the existing inferred/typed unmarked unary shape relation. Parameter/result
annotations remain inert syntax, not evidence of runtime typing.

First directly unfold the existing evaluator: a self-calling body bound to a
source closure evaluates both references successfully and enters that closure's
actual saved body. At depth n+3 its result equals that saved body's result at
n+1. The calling and saved owners, names, captures, parameter spellings and
source spans may differ. Both inputs contain the complete same finite closure.

Specialize to a closure whose own saved body calls its parameter on itself.
Every re-entry reconstructs the same fresh binding from the original saved name
rows, not from the previous invocation's extended rows. Captured values need not
contain the closure itself; no recursively defined runtime value is constructed.
Three direct base cases and decreasing budget induction prove None at every
finite depth. Only then use existing eventual completeness to exclude every
finite original successful derivation. No successful-body premise is assumed.

Lift this boundary to saved-reference calls under four explicit first-match
lookup premises. Both references select the same actual source closure. Also
prove it for direct calls between two independently created self-calling lambdas.
Their source occurrences, parameter names, annotations and bodies need not be
equal: the left body enters the right closure's saved body before exact re-entry.

## Independent checks

Symbolic consumers construct original creation/reference witnesses and direct
successful input runs before applying non-return laws. Distinct caller/saved
owners, duplicate rows, an already occupied fresh capture slot, mixed source/Core
closures, host functions, cell references and unrelated stores are retained.
Identity returns the complete looping closure at depth three; a false conjunction
skips the self-call at depth two. Their original successes and low-depth None
are independently proved before the contrast consumes non-return laws.

Constructor inversion independently excludes self-calling bodies from the old
data-body gate. Thus the bounded-input call laws do not cover these bodies merely
because both inputs succeed. Arbitrary finite sequences of grouping and strict
left/right tuple contexts preserve the non-return boundary. Right-tuple proofs
retain the actual preceding child's store; unrelated children are unrestricted.

Parsed tests compare full handwritten ASTs and every span, including typed-name
ranges, EOF and diagnostics. Four typed/inferred lambda pairs, self-calling versus
identity left bodies, and two mixed stores give sixteen contexts. Actual left
creation feeds the right creation; all saved fields and complete endpoints are
retained. Saved f(x) and short-circuit controls use separately created closures
and distinct caller/saved owners. The identity body's actual result/store feed
the actual original whole call. No source occurrence is replaced by another
occurrence with different spans to make a theorem apply.

## Preserved boundaries

No evaluator, original rule, existing source gate, image proof, typing, host/Core
execution, parser or diagnostic changes. These are raw-source finite non-return
theorems, not claims about well-typed whole programs or small-step infinite runs.
The explicit re-entry recurrence is additional evidence specific to this family;
None alone still distinguishes neither divergence, unsupported paths nor depth
exhaustion. No general termination decision, budget search or cost law is added.

Keep proof files below 300 lines and commits within 300 changed lines. Require
exact source ports, full builds/tests, independent consumers/reviews, public proof
checks and complete actual module ownership inspection. Retain all versions and
failed captures. Public proofs may depend only on the standard three axioms.
