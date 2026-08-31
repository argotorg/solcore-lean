# ADR-0018: Semantics-first development order

- Status: Superseded by ADR-0153
- Decision date: 2026-08-27
- Scope: repository development order and internal version boundaries

## Context

The current internal Multi frontend has a large grammar-specific proof surface.
Its lexer, chart parser, structural validator, source-location evidence,
retained-token correspondence, and certified one-file entry point are useful
for the grammar they describe.

The concrete Solcore syntax is now expected to change substantially. Continuing
the fast parser, structural identity, resolver, and exact grammar proofs would
spend proof effort on token, production, AST, and source-location structures
that may be replaced.

At the same time, the published Semantic Core covers only a small closed
fragment. Functions, structured values, mutation, algebraic data, contract
state, rollback, storage, ABI behavior, and semantic observations remain.
Most of this work can be defined independently of concrete spelling.

## Decision

Development moves to a semantics-first order.

1. Surface v1, Oracle v4, and the internal Multi frontend are retained as
   versioned reference implementations.
2. New grammar-dependent proof and performance work on the current Multi
   frontend is paused.
3. The incomplete fast-parser experiment after commit 0209a37 is not part of
   the stable parser boundary.
4. ADR-0016 remains an Accepted design, but its implementation is paused.
5. ADR-0017 remains Proposed, and its review and implementation are paused.
6. Active development targets an internal, syntax-independent Semantic Core
   vNext and explicit contract runtime semantics.
7. Existing Semantic Core v1/v2, Surface v1, Oracle v1 through v4, schemas,
   profiles, capabilities, limits, and golden bytes retain their meaning.
8. Core vNext additions are rejected by old Core wire projections.
9. Resolved static semantics should consume abstract structured identities.
   A concrete Surface adapter and source elaborator wait for a stabilized
   syntax version.
10. A future Surface or Core publication is additive and receives new version
    identifiers and compatibility artifacts.

## Consequences

The repository can strengthen the executable language meaning without choosing
temporary concrete syntax. Existing parser work remains available for
regression, comparison, and reuse of generic proof techniques.

There is no near-term end-to-end source compiler path. This is explicit:
Semantic Core features may be complete internally before any source spelling
elaborates to them.

Frontend status documents describe the frozen guarantee rather than a
parser-first roadmap. Historical parser ADRs remain available as design and
implementation records.

## Resumption gate

Surface-dependent work resumes only after a concrete syntax version fixes its
token language, grammar, AST, recovery behavior, diagnostics, and adapter
target. The change from retained versions and the required proof-regeneration
budget must be reviewed before implementation.

## Conformance requirements

- Published Oracle and wire golden tests remain unchanged.
- New Core constructors have negative old-wire projection tests.
- Core and runtime modules do not import the frozen Multi frontend.
- Documentation distinguishes frozen parser results from active Core work.
- Semantic commits do not accidentally include the unfinished parser
  experiment.
