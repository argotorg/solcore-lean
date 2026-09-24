# ADR-0153: Canonical syntax boundary

- Status: Accepted
- Decision date: 2026-08-31
- Scope: lexical tokens, parsed syntax, parser behavior, and frontend conformance
- Implementation: Executable parser complete; public ordinary-grammar soundness established

## Context

The concrete Solcore language underwent a large redesign. That design is
represented by `argotorg/solcore-rs` pull request 20, whose `new-syntax` head
at the time of this decision was commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.

The redesign includes Solidity-shaped declarations, name-first binders,
angle-bracket type application, `enum`/`trait`/`impl`, `returns`, `where`,
canonical import and export forms, C-style control flow, and the current
inline-Yul boundary. The repository needs one executable formal account of
that language, with a reviewable external comparison point.

## Decision

Implement the syntax at the pinned upstream revision as the canonical Solcore
source syntax. The upstream implementation supplies the initial lexical and
grammatical comparison point. Lean remains the authority for the formal model
implemented in this repository, and an intentional divergence requires an
explicit local decision.

The canonical frontend is exposed as a direct Lean library boundary through
`Solcore.Syntax` and the `Solcore` umbrella. Source name resolution, source
typing, and lowering into checked Core are later semantic stages rather than
parser responsibilities.

## Comparison evidence

The Lean definitions and accepted local decisions are normative. When adding
syntax that is not yet formalized, consult comparison evidence in this order:

1. parser and lexer behavior at the pinned upstream commit;
2. accepted canonical `.sol` files and focused parser tests from that commit;
3. migration documentation and examples associated with the pull request.

A moving branch, local checkout, or untracked design note may provide useful
evidence but is not independently normative. An intentional difference from
the pinned evidence requires an accepted Lean ADR. Updating the upstream pin
must likewise be explicit and reviewable.

## Active syntax boundary

The parsed source layer covers:

- UTF-8 byte spans and retained line and nested-block comments;
- keywords, identifiers, literals, punctuation, operators, and lexical errors;
- dotted module paths plus import, export, and hiding forms;
- pragmas, type aliases, enums, derive attributes, traits, implementations,
  contracts, fields, constructors, fallbacks, and functions;
- named, proxy, function, `comptime`, mapping, and tuple types;
- predicates, generics, `where` clauses, expressions, patterns, statements,
  match arms, and the supported inline-Yul language; and
- deterministic recovery and source-located diagnostics.

The AST is recovery-aware parsed syntax. Contextual validity, resolution,
typing, and lowering belong to subsequent stages. Lean preserves written
distinctions when they matter for source fidelity, including grouping,
`while`, compound assignment, explicit Yul return clauses, and raw literal
spelling.

## Representation and implementation order

1. Define source locations and a closed token catalog.
2. Define a source-preserving AST independently of Semantic Core.
3. Implement a total lexer with explicit lexical diagnostics.
4. Implement types, expressions and patterns, statements and Yul, then
   declarations and files.
5. Add focused accepted and rejected fixtures derived from the pinned upstream
   tests and canonical corpus.
6. Establish executable and declarative parser correspondence.
7. Add resolution, source typing, and lowering as later milestones.

Parser recovery and diagnostics are executable behavior, but diagnostic prose
is not itself a stable interface. Success and failure, source ranges, error
categories, and deterministic priority are formalized directly.

## Stability and upstream follow-up

Each update to the upstream comparison point must:

- identify the new commit;
- classify lexical, AST, grammar, diagnostic, fixture, and lowering impact;
- update the Lean implementation and focused conformance fixtures together;
  and
- amend this decision when the accepted language shape changes rather than
  merely correcting an implementation defect.

## Proof order

1. executable AST, lexer, and parser coverage;
2. totality and resource bounds at public entry points;
3. span validity and token provenance;
4. parser success soundness against the declarative grammar;
5. resolution, typing, and lowering preservation; and
6. performance refinements after canonical behavior is complete.

The implemented boundary establishes source ownership, full-file provenance,
carrier identity, exact-prefix scanner progress, and preservation across lexer
branches. Public lexer results have nonempty, ordered, nonoverlapping,
UTF-8-valid token and diagnostic spans. Parser preflight accepts these valid
lexer results, so public parse errors occur after preflight.

The compositional parser laws preserve source ownership, spans, token carrier,
cursor order, transactional branch priority, and complete output provenance.
A diagnostic-free successful `parseLexed` or `parse` result derives
`CoreSourceFileOrdinaryParsesFromStart` from the root token carrier to the
canonical terminal remainder and composes with canonical parsed-file validity.

## Required validation

The decision is implemented when:

- every active token and AST constructor has an executable witness;
- the selected canonical positive corpus parses;
- focused rejected spellings remain rejected;
- lexical and parse errors are deterministic and source-located;
- comments and UTF-8 spans preserve their documented ranges;
- executable parsing and declarative grammar judgments agree at the public
  diagnostic-free boundary; and
- the complete repository build, tests, and kernel-policy
  checks pass.

## Consequences

The repository has one canonical source parser and proof tree. The pinned
upstream revision makes conformance claims reproducible, while the local ADR
process makes later divergences explicit. Resolution, typing, lowering, and
end-to-end execution build on this parsed syntax without changing its lexical
or grammatical meaning.
