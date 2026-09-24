# ADR-0304: Computable depth for direct data-lambda applications

## Status

Accepted.

## Context

ADR-0302 and ADR-0303 bound the existing data-expression and data-body gates.
Neither gate admits calls or lambda creation. The original evaluator nevertheless
supports unmarked typed or inferred unary lambdas, retaining every saved lexical
field. A direct lambda's body is available in caller syntax; an arbitrary saved
callee's body is runtime data and requires a different contract.

## Decision

Define `directDataLambdaDepthBound argument body` as one plus the maximum of
one, the argument's data-expression bound and the body's data-body bound.
One is the creation depth of the direct unary lambda. Each child of the original
call receives the same predecessor budget, so its bound is a maximum, not a sum.

Retain independent `SourceUnaryLambdaShape`, `ClosedSourceDataExpression` and
`ClosedSourceDataBody` premises. The callee is the original direct lambda syntax,
not a grouped lambda or an arbitrary expression. Parameter and return annotations
are inert syntax; no runtime typing or canonical staging claim follows.

Prove the successful-depth result by inverting the original application.
Independent original creation and callee determinism identify every saved
source, owner, name row, capture row and callee store. Shape uniqueness identifies
the actual parameter and body. The direct argument/body bounds then find the
actual intermediate stores and final endpoint under the actual fresh extension.
No eventual completeness, threshold or image theorem supplies the depth bound.

Compose this result with existing soundness and success monotonicity to prove
four exact laws: success iff the original full endpoint at sufficient depth;
whole Option stability above the bound; sufficient None iff no original success;
and bound None iff None at every budget. These four laws assume neither argument
nor body success. They quantify over arbitrary mixed runtime inputs and complete
stores, including duplicate first-match rows and captured closures.

## Independent checks

Symbolic consumers first construct original creation, argument, fresh-body and
call witnesses. Separate runner recursions prove the exact cutoff for arbitrary
grouped-argument depth and nested-body depth, with typed or inferred parameters
and arbitrary annotations. A conditional argument that skips deeply grouped
string syntax demonstrates that the whole-source bound need not be minimal.
All actual value/store endpoints and the new success and failure laws are used.

Negative consumers independently rule out original success before deriving
finite-depth failure. Missing argument names or first captures prevent even a
valid body from running. Selected string returns cannot be repaired by type
annotations. A duplicate first non-Bool argument remains the actual fresh guard,
even when later rows contain Booleans.

Actual parsed spellings cover direct inferred and typed return-reference calls,
a direct bare return, a missing argument, and a grouped bare-return call.
The complete handwritten AST, every source range, EOF and zero diagnostics are
checked over mixed contexts and whole stores. Grouped syntax is retained as such:
its whole original call needs depth three, while the separately extracted direct
call needs depth two. The new direct-only theorem is not applied to the grouped
callee. Original witnesses and independent endpoint checks precede the new laws.

## Preserved boundaries

No data gate, original evaluator, evaluation rule, primitive meaning, selector,
image contract, lowering rule or typing definition changes. The six public image
statements and proofs remain untouched. This does not bound arbitrary saved
invocation, general nested calls or whole-language evaluation, nor does it define
Core transition costs, fault classification, effects or closure conversion.

Proof files remain below 300 lines. Require focused and full builds, complete
tests, kernel policy, whitespace, public axiom checks, exact source
ports and actual new-module ownership inspection before small commits. Only the
standard three proof axioms are permitted; generated names and flags are kept
as observed, with no prototype-generated-name equivalence claim.
