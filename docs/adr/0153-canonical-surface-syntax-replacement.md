# ADR-0153: Canonical Surface Syntax Replacement

- Status: Accepted
- Decision date: 2026-08-31
- Scope: source syntax, lexical tokens, parsed syntax, and frontend migration
- Implementation: Executable parser complete; formal proof boundary active

## Context

Parser work was paused while the concrete Solcore language was undergoing a
large redesign. That redesign is now represented by
`argotorg/solcore-rs` pull request 20. Its `new-syntax` head at the time of this
decision is commit `18fd9f75d290df0070e21ee56e0a5691f232596f`.

The new surface is deliberately incompatible with the previously modeled
Surface v1 and internal Multi grammar. It changes more than individual
keywords. Among other changes, it introduces Solidity-shaped declarations,
name-first binders, angle-bracket type application, `enum`/`trait`/`impl`,
`returns`, `where`, canonical import and export forms, C-style control flow,
and the current inline-Yul boundary.

Trying to evolve the old grammar and preserve its proof inventory would make
the obsolete grammar constrain the replacement. The user-facing goal is an
executable formal specification of the current Solcore language, not continued
development of two source languages.

## Decision

Implement the pull-request syntax as the only active Solcore source syntax.
The Rust implementation at the pinned pull-request head is the migration
source for lexical and grammatical behavior. Lean remains the authority for
the formal model implemented in this repository; this pin identifies the
external source revision being modeled and makes later upstream adjustments
reviewable.

The replacement does not attempt AST compatibility, parser compatibility, or
source compatibility with Surface v1 or Multi m2c-v1. Old syntax-specific
types and proofs are not design constraints. Generic workspace identity and
UTF-8 source-location ideas may be retained when they express unchanged facts,
but old grammar constructors are not wrapped or translated merely to keep them
alive.

Until a new wire protocol is explicitly published, the canonical frontend is
a Lean library boundary. Oracle v4 and its Surface v1 wire bytes remain frozen
historical compatibility artifacts; they are not the definition of current
Solcore syntax and receive no new features. A future source Oracle must use a
new schema version.

## Source-of-truth order

For this replacement, conflicts are resolved in this order:

1. parser and lexer behavior at the pinned pull-request head;
2. accepted canonical `.sol` files and focused parser tests in that revision;
3. migration documentation and examples associated with the pull request; and
4. a new Lean ADR for any intentional divergence.

The local Rust checkout or an untracked design note is useful evidence but is
not independently normative. The exact Git commit, not a moving branch name,
defines the initial comparison point.

## Active syntax boundary

The replacement covers the complete parsed source layer:

- UTF-8 byte spans and retained line and nested-block comments;
- hard and contextual keywords, identifiers, Yul-only identifiers, literals,
  punctuation, operators, and lexical errors;
- dotted module paths plus canonical import, export, and hiding forms;
- pragmas, type aliases, algebraic `enum` declarations, derive attributes,
  traits, implementations, contracts, fields, constructors, fallbacks, and
  functions;
- named, proxy, function, `comptime`, mapping, and tuple types;
- named and inferred lambda parameters, predicates, generics, and `where`;
- literals, names, constructors, proxies, lambdas, postfix operations, unary
  and binary operators, tuples, arrays, and conditional expressions;
- bindings, returns, assignments, matches, `for`, `while`, `if`, blocks,
  assembly, `break`, and `continue` statements;
- patterns and match arms; and
- the supported inline-Yul expressions and statements.

Parser recovery and diagnostics are executable behavior, but exact Rust
diagnostic prose is not automatically a stable Lean wire contract. Lean makes
success/failure, source ranges, error categories, and deterministic priority
explicit. Publication can freeze display text separately if needed.

## Representation strategy

The new implementation is built as a fresh source layer rather than by adding
constructors to the frozen Surface v1 algebra.

The AST is a parsed-syntax layer. It represents recovery nodes that the pinned
parser deliberately returns after emitting a diagnostic; grammar validity,
match arity, and other contextual facts belong to a subsequent well-formedness
layer. Valid productions may still use nonempty collections where parse
failure prevents construction altogether.

Lean retains written distinctions that the Rust implementation sometimes
lowers immediately, including grouping, `while`, compound assignment, and
explicit Yul return clauses. Core and inline-Yul literals are separate because
only Yul has boolean literal nodes; Core `true` and `false` remain
identifier-shaped syntax. Literal strings retain their raw quoted spelling and
are decoded only by a later semantic phase.

1. Define source locations and a closed token catalog.
2. Define the complete source-preserving AST independently of Semantic Core.
3. Implement a total lexer with explicit lexical diagnostics.
4. Implement the grammar in dependency order: types, expressions and
   patterns, statements and Yul, then declarations and files.
5. Add focused accepted and rejected fixtures derived from the pinned Rust
   tests and canonical corpus.
6. Expose the canonical frontend through `Solcore.Syntax` and `Solcore`, while
   retaining the old Surface modules only as historical compatibility code.
7. Define resolution, source typing, and elaboration into checked Core as
   later milestones.

Intermediate commits may keep frozen files buildable while consumers are
migrated, but they must not present the old grammar as the current language.
No compatibility parser or automatic old-to-new translation is added.

## Stability and upstream follow-up

Small upstream changes after the pinned head are expected. Each update must:

- identify the new upstream commit;
- classify the lexical, AST, grammar, diagnostic, fixture, and elaboration
  impact;
- update the Lean implementation and focused conformance fixtures together;
  and
- record an ADR amendment when the accepted language shape changes rather
  than merely fixing an implementation defect.

This policy keeps the frontend adaptable without returning to an undefined
moving target.

## Proof order

The previous parser effort accumulated deep grammar-specific proofs before the
syntax stabilized. The replacement uses a different order:

1. executable AST, lexer, and parser coverage;
2. totality and resource bounds at public entry points;
3. span validity and token provenance;
4. parser success soundness against a declarative grammar;
5. resolution, typing, and elaboration preservation; and
6. performance refinements only after the canonical behavior is complete.

This is a sequencing decision, not a relaxation of the final formal-spec
goal. Grammar-specific proofs are rebuilt for the new language where they
protect an active executable boundary.

## Required validation

The syntax replacement is complete only when:

- every active token and AST constructor has an executable witness;
- the selected canonical positive corpus parses;
- focused legacy-spelling fixtures are rejected;
- lexical and parse errors are deterministic and source-located;
- comments and UTF-8 spans preserve their documented ranges;
- no active public module describes Surface v1 or Multi m2c-v1 as current
  Solcore syntax;
- the complete repository build and tests pass; and
- metadata and kernel-policy checks still pass.

Source name resolution, source type checking, elaboration, and end-to-end
execution are subsequent frontend milestones. They target the already checked
Semantic Core and Oracle v5 execution boundary rather than changing its
meaning.

## Consequences

This decision intentionally invalidates the old syntax as a development
target. Existing historical ADRs, frozen wire files, and golden bytes remain
available to explain or verify previously published interfaces, but they do
not receive feature work and must not be cited as the current language.

The immediate benefit is a clean AST and parser aligned with the compiler
syntax users will actually write. The cost is that old parser proofs cannot be
ported mechanically; useful generic lemmas will be re-established only after
their new premises and consumers are clear.
