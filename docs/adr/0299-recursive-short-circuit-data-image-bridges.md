# ADR-0299: recursive short-circuit data images

## Status and baseline

Accepted design after independent production and consumer review.
The Bool and Word parsed prototype suites passed independent repetition:
eight Bool fixtures and forty-eight Word fixtures. Formal adoption and final
aggregate verification remain separate required gates.
Baseline is completed ADR-0298 at
`cf9bb78649f1d6d7d1eb2922930d2b4eb6db5fee`.
Its completion record is `.lake/trace-audits/ADR0298CompletionRoot.json`, SHA256
`b973cf340f1c9cfc8f2fc0afb71145b0a81f629ae5bab7707f54b0d6ac218dbc`.
Canonical Rust stays at `18fd9f75d290df0070e21ee56e0a5691f232596f`.
Diagnostics and parser proofs remain paused.

## Exact production boundary

Append logicalAnd and logicalOr to ClosedSourceDataExpression, admitting eleven
recursive forms instead of nine. Both original children must be admitted, even
when execution skips the right one. Keep all outer/operator/child source ranges
and the nine existing clauses in their original order.
The gate is a syntax predicate, not successful execution, resolution or typing.

Only two production files change, under Solcore/Frontend:
ClosedSourceDataExpression.lean and ClosedSourceDataExpressionProperties.lean.
The latter adds cases only to its private reflect and embed proofs.
The six existing public expression/body/invocation/application image contracts,
including their public proof bodies, remain literally unchanged.
ClosedSourceDataBody and its three body/expected-lambda proof modules stay
whole-byte unchanged. Its seven constructors recursively reuse the extended gate.
All original closed evaluation rules, runner, correctness, threshold and
short-circuit law sources from ADR-0298 stay whole-byte unchanged.

Reflection follows actual original evaluations. It reflects the left endpoint
and complete middle store, identifies the forced Core Boolean through ofCore
injectivity, and reflects a selected right at that same actual mapped store.
The right value remains arbitrary Core data, not necessarily Bool.
Skipped cases use no right evaluation, return the fixed Boolean and preserve
the complete reflected left-final store. Embedding independently follows the
four original Local andTrue/andFalse/orTrue/orFalse constructors.
Neither private proof uses the bounded runner as its semantic definition.

The reviewed production prototype freeze is
`.lake/trace-audits/ADR0299ProductionPrototypeFreezeReviewerB.json`, SHA256
`b2ef70d4def1cb85b50726ee56c03a5e66902a39f725a4fa96da37fcf9bbe912`.
Removing its three exact added blocks and reversing its import substitutions
restores all six previous source files completely. The four unchanged files
have import-only aliases for isolated prototype verification, not formal edits.

## Independent consumers

The symbolic expression consumer uses original grouped negation as the left
operand and a grouped arbitrary Core payload on the right. Both operators and
all actual Boolean choices have independently constructed Closed, Local and
Core evaluations, with explicit whole resolution and lowering. These precede
the two image iff conversions, each used in both directions over every actual
RuntimeValue and complete final store. Ordered lookup hypotheses permit duplicate
IDs and spellings; no runtime typing or unique-row premise is introduced here.

Boundary consumers separately prove:

- Skipped lambdas and calls can succeed in the original closed judgment while
  the whole expression remains outside the data gate.
- A missing reference right is admitted as syntax and can be skipped, but every
  whole-expression resolution is impossible.
- An admitted unit-valued left still excludes every successful whole endpoint.

These are original-rule witnesses and semantic impossibility proofs, not merely
failed bounded executions. Whole structural checking continues to inspect both
operands; no skipped-side exemption is added to resolution or typing.

Expected-Bool consumers use a fresh local p initialized by p && !p or p || !p,
then return its value with a saved arbitrary Core payload q. The static Unit
context for q does not imply that the actual payload is runtime-typed Unit.
Expected-Word consumers use a grouped Boolean short-circuit condition to choose
between the fresh Word parameter and its bitwise complement. An unrestricted
raw selected Word right is never mistaken for a Boolean-typed expression.

Both families exercise body, direct application and saved invocation through
the six existing contracts, with independent original evaluations first.
Checked saved inputs inherit their existing ID uniqueness from LocalTypeInputs;
duplicate source spellings, foreign owners and arbitrary mixed caller rows
remain possible. This is distinct from the unrestricted raw-expression consumer.
Actual returned closures retain all saved fields. Parsed tests pass the returned
creation value and store through actual callee/argument evaluation to the saved
body; they do not synthesize these inputs from an expected result projection.
The saved-call fixtures explicitly preserve their callee stores. They do not
establish an additional theorem for arbitrary state-changing caller prefixes.

Parsed counterparts use returned original ASTs, independently specified source
ranges, zero diagnostics and EOF, and adjacent checks around independently
derived depth bounds. Closed derivation depth and Local/Core transition cost
remain different measures. Parsed certificate depth fields are expected annotations,
not new universal cutoff theorems. These tests do not establish parser correctness.

## Verification and publication

The complete consumer source headers and exact import reversals are frozen in
`.lake/trace-audits/ADR0299FormalPortFreezeRoot.json`, SHA256
`667c61109e45f648dcdf19ff575dac35f91e86addf8509aa85b445f928f3efa5`.
The six new modules under Solcore/Test are:

- FrontendClosedSourceShortCircuitDataImageProperties.lean
- FrontendClosedSourceShortCircuitDataBoundaryProperties.lean
- FrontendExpectedBoolShortCircuitDataImageProperties.lean
- FrontendParsedExpectedBoolShortCircuitDataBridge.lean
- FrontendExpectedWordShortCircuitDataImageProperties.lean
- FrontendParsedExpectedWordShortCircuitDataBridge.lean

Register six new consumer modules and two parsed IO tests in Tests/Main.lean;
no new production public theorem or umbrella import is needed.
Keep every proof file below 300 lines. Commit the grammar, private proofs,
individual consumers, registration and status documents in separate small units.

Inspect actual module-owned declarations for the changed data gate and its
image-proof dependents, retaining full types, flags, axioms, dependencies and
public logical closures. Do not predict compiler-generated names or normalize
numeric binder atoms. Preserve the complete ordered historical catalogs.
Require focused and direct-client builds, full frontend/syntax/tests builds,
new and retained parsed tests, full tests, standard-axiom and kernel-policy
checks and whitespace checks before completion.

This slice adds no Word binary dispatch, effects, mutation, source/Core closure
identity, whole-frontend totality or canonical Rust compiler-correctness claim.
