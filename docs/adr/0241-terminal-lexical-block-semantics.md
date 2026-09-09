# ADR-0241: Terminal lexical block semantics

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Singleton terminal blocks in recursive bodies and existing entries

## Reference and prerequisites

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/stmt.rs:366–375` retains the block statement and its
original inner statement list. `crates/parser/src/lower/body.rs:456–458`
preserves that block in HIR. Name resolution opens a lexical scope in
`crates/hir/src/nameres/body_resolver.rs:109–115`. Type inference pushes and
pops a scope, returning the inner sequence's type unchanged, in
`crates/hir-ty/src/infer/stmt.rs:250–254`. Inner returns consult the existing
function return context at lines 101–128.

Specialization retains both Return and Block in
`crates/specialize/src/specialize/body.rs:314–317,397–401`. Its evaluator
processes a block with cloned environments and does not export newly bound
locals (`crates/specialize/src/evaluate/core.rs:611–628`). This is optimization,
not a runtime transition-count specification. Hull emission also retains
Return and opens a lexical scope for Block
(`crates/hull/src/emit/emitter.rs:251–259,334–337,1371–1375`).

Canonical Lean `StatementValue.block` stores an original statement list.
`Syntax.Parser.blockStatement` preserves the inner braces' span as the
statement span. The existing recursive body already checks complete terminal
returns, strict discard/let prefixes and both terminal conditional arms.

## Decision

Accept exactly an original singleton terminal block
`⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩` by checking
`⟨innerSpan, statements⟩` in the same original inputs. The inner child uses
the statement's inner span, never the outer wrapper span. Keep the original
list, child spans, source order, caller tables, owner and parameter records.
Do not flatten or rewrite source syntax, allocate a source LocalId, reset
the input scope, or shift positional Core references.

The exact result Core and type are the inner child's Core and type. Add
independent `block` constructors to whole typing, exact elaboration, raw
evaluation and costed evaluation. Raw evidence retains the same original
name table, environment, initial/final stores, value and cost. Direct
evaluation and the source bound recur on the same inner child. No extra
Core transition is introduced; accepted inner computations still have their
existing positive costs. This does not assert agreement with Rust optimizer
fuel or emitted execution costs.

Retain all 59 directly affected theorem statements and every old constructor
name and type. Add one full-Option checker equality for the original wrapper
and child, preserving both acceptance and rejection. Reuse the child's exact
Core typing, local-fragment membership, evaluation and continuation paths.
Extend owner/type-name/lookup/store/fuel contracts without new premises.

## Consumers, migrations and boundaries

Independent source and complete parsed consumers must cover arbitrary finite
wrapper depth, distinct inner/outer source ranges, retained sparse first
matches and original positional references. Include mixed annotated/inferred
lets, strict discarded arithmetic/products and asymmetric conditional costs.
Specify exact Core, values and manual paths independently; compare every
tested fuel and actual checkpoints with the original inner computation and
resume genuine saved states. Distinguish nominal static types from actual
typed opaque cells/closures, and any retained continuation endpoint from a
completed run.

Migrate obsolete entry/body rejection claims using the same original sources
and callers: closed bare-return wrappers in runtime, compilation-owner and
recursive-entry consumers, and the typed-let wrapper in a conditional arm.
Keep narrower singleton/terminal-tree/prefix adapters unchanged, along with
neighboring invalid inputs. Do not weaken common rejection helpers.

Only the last singleton wrapper is added. Nonterminal blocks with following
statements, empty or unterminated inner bodies, implicit returns, general
early return, local scope escape, shadowing and default initialization remain
outside this profile. Rust's direct-statement non-final-return check is not
used as evidence about arbitrary nested early returns. Invalid unselected
arms, original headers and actual arguments still reject as before.
Core/Resolved definitions, parser, diagnostics, wire formats and runtime
records remain unchanged.

Keep body-to-entry imports acyclic and new proof/test files under 300 lines.
Separate definitions, proofs, migrations, consumers and publication commits.
Run focused/aggregate builds, full tests, all public/consumer axiom audits,
kernel/metadata/whitespace checks and independent reviews. Scratch remains
inside the repository, and paused diagnostic files remain untouched.
