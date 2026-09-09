# ADR-0240: Strict expression-statement prefixes

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Semicolon-terminated discard prefixes in existing recursive bodies and entries

## Reference and prerequisites

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/stmt.rs` retains the original expression and explicit
trailing-semicolon flag. `crates/hir-ty/src/infer/stmt.rs` checks an expression
statement, discarding its expression type rather than requiring Unit.
`crates/specialize/src/specialize/body.rs` retains `MonoStmtKind::Expr`.
The evaluator/optimizer in `crates/specialize/src/evaluate/core.rs:397–427`
processes effects and may remove known values. Lean's exact unoptimized Core
transition counts are not assertions about optimized Rust transition counts.

Canonical Lean syntax already retains `StatementValue.expression source true`
and its original statement span. ADR-0239 supplies exact body membership in
the local Core fragment. Existing Core insertion laws preserve and reflect
typing, literal runtime values and exact path lengths under a hidden binder,
including under nested lets and both conditional arms.

## Decision

Extend the existing recursive typed-let/return-tree adapter with
`expression; tail`, retaining the original semicolon flag, source expression,
block span and statement order. Independently resolve, lower and type the
expression in the original inputs, allowing any supported inferred expression
type. Check the original tail in those same inputs. Do not allocate a source
LocalId, introduce a spelling, bind a synthetic source local or alter the
parameter-only records.

Compile exactly to `Core.Expr.letE expressionCore (tailCore.weakenAt 0)`.
The hidden Core binder enforces strict once-only evaluation and discards the
actual result; positional weakening retains every original tail reference.
The source tail is not weakened or elaborated under an extra input.

Add separate `discard` constructors to independent whole typing, exact
elaboration, raw evaluation and costed evaluation. Keep every existing
constructor name and type. Raw judgments evaluate the original head then tail
with the same name table and environment, threading initial/middle/final stores.
They require no static typing or fresh-name premise. The direct evaluator
retains this strict order, and both cost and source bound add head plus tail
plus two existing Core transitions. An unused head is never skipped.

Retain all 58 directly affected theorem statements. Add one child-decomposition
theorem exposing the original expression Core/type and original tail Core,
with the complete result equal to the exact weakened `letE`. Extend the
structural membership proof with the head lowering and weakened tail membership.
Use existing insertion/reflection to transport typing and raw evaluation.
For exact costs, obtain the tail's closed final path, insert the actual head
value, then compose with the original head at any unchanged outer continuation.

## Consumers, migrations and boundaries

Independent source and complete parsed consumers must distinguish unchanged
source scopes from the hidden Core binder. Cover arbitrary mixed discard,
written/inferred let prefixes and conditional depth, sparse/duplicate caller
rows, unused noncommutative or product work, typed opaque actual values,
nominal static types and preserved owner/lookup/type-table contracts.
Specify original AST, exact Core, values and manual paths independently of
checker or Core-evaluator results. Verify all bounded fuel thresholds and
genuine initializer/tail checkpoint residuals, not restart substitutes.

Migrate four obsolete parsed rejection claims using their original sources and
callers: a closed literal followed by bare return, a discarded parameter before
a terminal conditional, a sparse-body parameter copy, and a single-parameter
whole-entry copy. Retain neighboring invalid cases and old body-only adapters.

A missing semicolon flag, a missing terminal tail, statements after return,
assignment, source calls and other unsupported expressions remain outside this
profile. Invalid unselected arms and invalid whole headers/arguments still
reject. No implicit tail-return/default Unit, general early return, shadowing,
block-wrapper, allocation or call policy is introduced. Core/Resolved definitions,
parser, diagnostics, wire formats and runtime records remain unchanged.

Maintain body-to-entry acyclicity and proof/test files under 300 lines. Split
definition, proof, migration, consumer and publication commits where practical.
Run focused/aggregate builds, full tests, all public/consumer axiom audits,
kernel/metadata/whitespace checks and independent reviews. Keep scratch local
to the repository; retain the paused diagnostic files untouched.
