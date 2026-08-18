# M2: Frontend implementation plan

The objective of M2 is to convert a shared `.solc` workspace into the published
Semantic Core through independently specified parsing, resolution, checking,
and elaboration phases. M2 must make source-level differential testing possible
without treating either existing compiler's lowering pipeline as the
specification.

## Current progress: M2b parser publication complete

Following
[ADR-0012](adr/0012-m2a-surface-parser-kernel.md), the repository contains an
internal parse-only Surface kernel for a deliberately closed single-file
fragment:

- one zero-argument top-level function used only as a fixture envelope;
- explicit return type `()`, `bool`, or `word`;
- initialized, explicitly typed immutable `let` statements;
- one final value-returning statement;
- raw decimal and hexadecimal integers;
- unresolved names and generic calls;
- explicit grouping and unit syntax;
- keyword conditionals;
- unary `!` and the shared arithmetic, bitwise, relational, and equality
  operators.

The lexer is pure and total, retains ordered comment spans, supports nested
block comments, uses ASCII-only maximal munch, and records half-open UTF-8 byte
spans. Its public success path validates a complete, ordered, non-overlapping
source partition. The AST preserves grouping, operator spans, raw literal
spelling, call boundaries, and keyword conditional syntax.

The proof layer now contains:

1. an independent maximal-munch lexical judgment and executable checker that
   gates public lexer success;
2. an independent full-token difference-list parser grammar;
3. proof-carrying private parser results that construct a `FileParses`
   derivation without using the public conformance gate;
4. relational determinism for expressions, prefix and infix parsing,
   arguments, types, statements, functions, and complete files;
5. executable checks for span validity, grammar shape, and exact AST/token
   correspondence;
6. sufficient-fuel theorems for both lexer and parser input-derived bounds;
7. global uniqueness of accepted lexical partitions and sound reachability for
   every public source-level lexer failure; and
8. reverse executor completeness for every `FileParses` derivation over the
   exact lexer output.

Successful public parsing retains the exact lexer and parser results and proves
the lexical judgment, complete token correspondence, source validity, grammar
validity, and `FileParses`. Fuel exhaustion remains represented as an internal
invariant for defensive classification, but public lexer and parser theorems
prove it unreachable. The lexer's defensive output-validation invariant is
also proved unreachable from the raw executor's lexical-soundness theorem.

The internal M2a proof obligations are discharged in both executor directions.
Successful execution constructs the independent judgments, and every
complete-file derivation for the exact lexer stream is accepted; its full
source conformance follows from the lexical and grammatical derivations.
Two accepted lexical partitions of one source are equal, and every public
source-level lexer failure is connected to an implementation-reached cursor
that satisfies the executable local rejection judgment. These results supplied
the proof-kernel prerequisites for the M2b publication decision.

[ADR-0013](adr/0013-m2b-surface-parser-publication.md) now publishes the exact
fragment as `surfaceGrammar` under `solcore/0.1.0-draft.4` and the frontend-only
`frontend-m2b-v1` profile. The publication adds the closed
`solcore-surface/v1` and `solcore-parse-result/v1` schemas and Oracle v4, whose
only queries are `capabilities` and `parse`.

Oracle v4 accepts one source string paired with a nonempty opaque source label.
It copies that label exactly into every returned span and does not interpret it
as a filesystem path. Its `sourceBytes` limit measures only the UTF-8 byte
length of the content: a content length at or below the requested limit reaches
the parser, while a greater length is `inconclusive` at source preflight.

The M2b boundary is complementary to, rather than a replacement for, the M1c
Core boundary. Oracle v3 continues to accept only frozen Semantic Core v2
inputs. Oracle v1 through v3 and draft.1 through draft.3 artifacts retain their
existing bytes. Because M2b does not resolve workspaces, names, types, or
standard-library identities and does not elaborate or execute source, it does
not yet establish full source-level semantic differential conformance.

## Phase boundaries

### M2b: parser publication

Parsing is published with all of the following completed:

1. a closed, version-local `solcore-surface/v1` wire AST;
2. bounded decoder/encoder round-trip and canonicalization theorems;
3. a parse-result schema with stable phase, code, UTF-8 span, and structured
   arguments;
4. `solcore/0.1.0-draft.4` with `grammarVersion = 1`;
5. frontend-only profile `frontend-m2b-v1`, enabling only `surfaceGrammar`;
6. Oracle v4 and capabilities v4, supporting only `capabilities` and `parse`;
7. positive, negative, malformed-wire, resource, cross-version, and mixed
   stream golden cases.

The publication is additive. It does not modify draft.1 through draft.3,
Semantic Core v1 or v2, Oracle v1 through v3, their profiles, or their existing
golden bytes.

### M2c: workspace and resolution

[ADR-0014](adr/0014-m2c-workspace-identity.md) fixes the first internal M2c
subphase: canonical logical paths, structured library/source/module identities,
the exact raw and validated user-workspace shapes, complete deterministic
structural errors, and an independently specified pure validator. It does not
reinterpret the opaque Oracle v4 path and does not publish a workspace profile.

After that identity kernel is complete, extend from validated source records to
module and name resolution only after a separate Accepted resolver ADR fixes:

- safe canonical source paths and entry-file selection;
- module path derivation;
- import, export, alias, selection, and hiding behavior;
- declaration order and structured declaration identities;
- duplicate declarations and shadowing;
- local scope, including independent conditional branches;
- the identity and visibility of the canonical standard-library bundle.

That resolver ADR must also define the closed multi-module Surface algebra,
separate lexically resolved occurrences from type-directed selectors, and fix
the intrinsic dependencies needed to resolve the canonical standard-library
sources. The Resolved layer uses structured identifiers derived from source
paths, syntactic roles, and declaration indices. It must not replace identity
with raw name strings. Successful resolution must construct a declarative
resolution derivation and establish uniqueness and non-dangling references.

### M2d: checking and Core elaboration

Typed elaboration requires separate Accepted decisions for:

- the polymorphic type of source integer literals and their conversion to
  `word`;
- the status and shadowing behavior of `true` and `false`;
- operator resolution through type classes versus profile-defined direct
  rules;
- canonical standard-library identities for `bnotWord`, `bshlWord`, and
  `bshrWord`;
- exactly-once source argument evaluation when a resolved helper must reorder
  values for Core;
- the fixture function's entry-envelope meaning;
- short-circuit elaboration of `&&` and `||`;
- source diagnostics and unsupported-feature classification.

An elaborator may map only resolved identities, never a callee's spelling, to a
Core primitive. The shift helpers take source arguments in `(shift, value)`
order, while Core uses `(value, shift)`; elaboration must bind source arguments
left to right before reordering the resulting values.

Successful checking must construct a declarative typing derivation.
Elaboration must preserve type and stage/effect information and must target a
published closed Core version without silently widening it.

### M2e: polymorphism, classes, and staging

General polymorphism, tabled class resolution, and comptime/runtime staging are
added only after their rule sets and resource models are complete. Class search
uses explicit fuel or another proved terminating decision procedure; exhaustion
is `inconclusive`, not `rejected`.

## Implementation order

1. Surface source ownership, tokens, syntax, lexer, parser, and correspondence.
   Soundness, completeness, direct parser derivation, relational determinism,
   lexical uniqueness, lexer-failure reachability, and fuel sufficiency are
   implemented for the internal M2a fragment.
2. Version-local Surface wire and parse-only Oracle publication. Implemented
   in M2b as Surface v1, parse-result v1, and Oracle v4.
3. Workspace identity and structural validation, as fixed by ADR-0014.
4. Multi-module Surface syntax and an Accepted resolver ADR.
5. Module/import resolution, structured identifiers, and declarative
   resolution correspondence.
6. Source typing and typed elaboration for literals, immutable bindings,
   conditionals, calls, and the operator-backed M1c subset.
7. Standard-library identity refinement for word not and shifts.
8. Polymorphism, tabled class resolution, and staging.
9. Source-to-Core differential fixtures and shrinkable conformance corpora.

## Completion criteria for a frontend feature

- An Accepted ADR fixes every observable grammar or static-semantics choice.
- A declarative judgment exists independently of the executor.
- A pure, total decision procedure exists.
- Soundness is proved; completeness is proved or its exact limitation is
  recorded.
- Successful phase output satisfies source ownership, span, uniqueness, and
  non-dangling invariants as applicable.
- Resource exhaustion is explicit and cannot become rejection.
- A closed version-local wire representation and canonical codec exist before
  Oracle publication.
- Positive, negative, boundary, and upstream-difference witnesses exist.
- The semantic kernel contains no `sorry`, `admit`, `partial`, `unsafe`,
  undeclared axioms, or IO.
