# ADR-0247: A separate singleton application-return body

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Original single-return bodies whose expression is a local application

## Evidence and decision

The canonical AST retains a return's optional original expression and the full
ordered statement list (`Syntax/Term.lean`, lines 107–154). The Lean return parser
keeps the keyword-to-semicolon span and that expression unchanged
(`Parser/Statement/Simple.lean`, lines 153–160). At the pinned Rust revision
`18fd9f75d290df0070e21ee56e0a5691f232596f`,
`crates/parser/src/parse/stmt.rs`, lines 191–198, parses that same expression and
mandatory semicolon. `crates/hir-ty/src/infer/stmt.rs`, lines 19–41 and 101–130,
distinguishes nonfinal returns and checks the returned expression against the
enclosing return contract. This slice does not implement general early returns
or that enclosing header gate.

Existing `ReturnBody` handles bare or pure-expression singleton returns and
adds no Core transition for the return wrapper. Exact application typing,
evaluation, actual costs and checked execution are now available in ADR-0243–0246.
Connect them to an original body through a separate application-return profile.
Accept exactly one `.returnStmt (some source)` whose original expression belongs
to `LocalFunctionApplication`. Retain the original block span, statement span,
child syntax, argument list and order. The child supplies exactly the body's
Core, type, result value, all stores and actual cost. Return wrapping introduces
no Core binder, source identity, control frame or transition.

Do not widen the existing pure or recursive body adapters. In addition to store
independence and source-only fuel bounds, the recursive discard proofs use
`tailElaboration.localFragment` for exact positional weakening and reflection
(`TypedLetReturnTreeExecutionProperties.lean`, lines 108–113 and 198).
`Core.Expr.LocalFragment` excludes applications and cell operations. Preserving
those old contracts requires a deliberate separate integration, not merely an
extra accepted child. Existing bodies, entries, runtime records, Core, Resolved,
parser, diagnostics and wire definitions remain unchanged.

## Independent contracts

Define `LocalApplicationReturnBodyHasType`, exact
`LocalApplicationReturnBodyElaborates`, raw evaluation and cost evaluation with
one constructor each, using the existing independent child judgments rather
than successful checker premises. Prove static success/rejection correspondence,
whole typing, exact Core/type uniqueness and Core typing. Raw erasure, cost
existence and determinism preserve the same actual values and stores. Exact
elaboration with ordered runtime IDs gives Core evaluation and closed exact-cost path
correspondence in both directions; the same actual cost works under every
retained continuation without executing its pending frames.

Add separate `LocalInputs.checkApplicationReturnBody?` and
`runApplicationReturnBody?` endpoints. On an original singleton return, prove
full-Option equality with `checkApplication?` and `runApplication?`. Thus every
checked outcome, static type tag, genuine checkpoint and resumed result is
identical to the child's. Also expose whole-body exact checking, full-result
factorization, absence characterization and fixed-fuel typed-cost reflection.
Reuse ADR-0246's runtime-world and resumption laws through the full-result
equality; do not duplicate its entire API under body names.

Structural input records still do not establish runtime-world validity.
Missing cells may fault and wrong payloads may return values inconsistent with
the checked tag. Actual body effects and costs are retained, not bounded by
source syntax. This is neither a direct source interpreter nor whole-function
compilation/preparation, general return control flow or new Function policy.

## Validation

Use independent source-body certificates and original parsed blocks/declarations,
with full original parameter binding and the same actual input projections.
Exercise reader cost8, writer cost15, allocation cost8, delayed typed closures
with cost `3*n+6`, and identical child/body checkpoints including fault resumption.
Distinguish nominal static contexts from actual higher-order Function values.
Selected raw success must not excuse an unknown unselected branch. Bare/pure
returns, empty or multiple statements, discards, conditional statements, nested blocks and
nested calls remain outside this new profile; their old endpoints are unchanged.

Separate decisions, definitions, proofs, consumers and publication into small
commits. Keep each new proof/test file below 300 lines. Require focused and
aggregate builds, full tests, all public/consumer standard-axiom audits,
kernel-policy and whitespace checks and independent reviews.
