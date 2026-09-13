# ADR-0303: Computable source depth for closed data bodies

## Status

Accepted.

## Context

ADR-0302 gives a syntax-only upper bound for recursive closed data expressions.
The existing seven-form data-body gate additionally admits returns, nested
blocks, typed or inferred bindings, discards, conditionals and ordered matches.
Their executable search still needs a depth budget. Binding introduces fresh
lexical rows, while match selection has a separate visited-comparison count.

## Decision

Define `closedSourceDataBodyDepthBound` mutually with
`closedSourceDataMatchDepthBound`, using decreasing source sizes. Bare return
costs one. Expression return and nested block add one. Binding and discard use
the maximum of the expression and original tail-body bounds, plus one. A
conditional includes its guard and both written branches. A match includes its
scrutinee and the maximum over all written arm bodies and the optional default,
plus one. Scanning patterns does not add recursive evaluator depth.

Unhandled root shapes receive zero. This is not a bound for arbitrary syntax:
every evaluation law retains the independent `ClosedSourceDataBody` premise.
Nested gate-external syntax does not imply that the outer bound is zero.
The bound is sufficient, not minimal, and includes branches that are never
selected, even when their patterns or expressions would fail.

Prove `ClosedSourceDataBody.evaluates_at_depthBound` directly by gate induction
and original body-evaluation cases. Expression children use the direct
ADR-0302 result. Binding evaluates the initializer with the old lexical inputs
and passes the actual fresh rows, captures and middle store into the tail
induction hypothesis. Original ordered match selection identifies a written
body whose bound is at most the full branch maximum. No previous threshold,
eventual completeness or image law is used as an oracle for this direct proof.

Existing soundness and success monotonicity then give four public laws:

- Sufficient-depth success iff the original judgment, for every actual value
  and complete final store.
- Equality of the whole Option result at every budget at least the bound.
- Sufficient-depth None iff there is no original successful endpoint.
- None at the bound iff None at every budget, including smaller ones.

These laws retain arbitrary mixed runtime payloads, duplicate first-match rows
and saved lexical fields. Absence of an original successful endpoint does not
classify the reason for failure.

## Independent checks

Symbolic consumers construct original witnesses before using the depth laws.
Arbitrary chains of typed or inferred fresh shadowing have bound `n + 2` and
fail at every smaller budget. Initializers read the old binding. Conditional
branches demonstrate distinct selected depths under a common upper bound.
An arbitrary number `n` of literal misses has comparison count `n` but body
depth two: comparison work and recursive search depth are distinct quantities.

Negative consumers independently exclude successful original endpoints for
missing initializers or discards, selected missing branches, a duplicate
non-Bool first guard, invalid patterns, absent cases/defaults and a literal
miss followed by an invalid pattern. Invalid patterns do not escape to a
later default. An early wildcard or literal hit skips arbitrarily deep bad
arms and defaults, succeeding below the conservative whole-source bound.

Three actual parsed spellings exercise typed followed by inferred shadowing,
discard, a nested return, and literal-headed wildcard/default matches.
The forty successful lanes retain the whole handwritten AST, all source ranges,
EOF, zero diagnostics, original witnesses and complete actual outputs. Inputs
include duplicate captures, source and Core closures, pairs and nonempty stores.

## Preserved boundaries

No original evaluator, evaluation rule, primitive meaning, gate, match selector,
image law, lowering rule or typing contract changes. All six public image
statements and proofs remain untouched. Source-call and saved-invocation bounds
remain separate work, as do Core transition costs, fault classification,
runtime typing, effects, closure conversion and whole-language totality.

All new proof files remain below 300 lines. Focused and full builds, complete
tests, kernel policy, metadata, whitespace and public axiom checks are required.
Actual module ownership is audited separately from public declarations.
Compiler-generated recursive companions retain their observed flags and are
checked separately from authored definitions and public logical dependencies.
Only the standard three proof axioms are permitted.
