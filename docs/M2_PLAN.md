# Canonical syntax implementation plan

This plan covers the active source frontend. The old parser target is replaced
by the stabilized canonical syntax introduced by `solcore-rs` PR #20.

## Target and compatibility

The canonical frontend is implemented afresh under `Solcore/Syntax`. The
Surface v1 and Multi definitions are historical compatibility artifacts, not
constraints on the new AST, lexer, parser, or diagnostics.

Oracle v4 bytes remain unchanged. A future public source Oracle will use a new
additive version and will not reinterpret v4 requests or responses.

The pinned Rust implementation is migration evidence for accepted spelling,
grammar, recovery, comments, and byte spans. The accepted Lean definitions and
their declarative rules remain the formal specification authority.

## Implementation order

1. Define source identities, UTF-8 byte spans, the complete token catalog, and
   a source-preserving parsed AST.
2. Implement a total lexer with deterministic, accumulated lexical diagnostics.
3. Implement parsing for types, expressions, patterns, statements, inline Yul,
   declarations, and complete source files.
4. Port the relevant positive and negative fixture corpus from the pinned Rust
   revision and add focused span, comment, recovery, and Unicode cases.
5. Establish resource bounds, span validity, token provenance, and parser
   success soundness against a declarative grammar.
6. Expose one canonical Lean frontend umbrella after executable behavior and
   its initial provenance boundary are coherent.
7. Add name resolution, source type checking, and elaboration into checked
   Semantic Core as separate stages.

## Current executable coverage

The source-to-AST path is operational and public as a Lean library. It
includes:

- the total public lexer and parser result;
- source-identity and exact full-file-span provenance;
- the Rust-compatible delimiter and conditional nesting guard;
- leading-comment attachment;
- the complete declaration and type grammar;
- expressions, patterns, statements, blocks, and inline Yul;
- deterministic recovery and diagnostic filtering;
- all 23 pinned dedicated positive fixtures plus focused negative cases; and
- explicit rejection of representative spellings from the replaced grammar.

The external fixed-revision comparison audit also accepts all 490 upstream
`corpus/ok` sources without lexical or parse diagnostics and found no
source-AST gap. The four diagnostic-cardinality differences are frozen by
exact malformed-fixture regressions and preserve the same rejection/recovery
behavior.

Source and full-file-span provenance and exact lexer-carrier retention are
complete. The public lexer is proved total and always returns a `LexedFile`
whose tokens and comments are nonempty, source ordered, nonoverlapping, and
valid at UTF-8 byte boundaries; its lexical diagnostics also have valid source
spans. Exact-prefix scanner proofs and the strict decrease of the unconsumed
suffix establish this contract for every lexer branch and rule out the
exceptional fuel result.

Parser preflight accepts exactly the lexer results satisfying that contract,
and every public lexer result passes preflight. Any public parser error
therefore occurs only after successful lexing and preflight. Parser state,
primitive consumers, carrier-preservation rules, and cursor/order laws now
support compositional proofs for names, selectors, literals, delimiters,
pragmas, derive attributes, Core blocks, the complete recursive type parser,
complete function signatures, and the public Yul expression, statement, and
body parsers. The generic Core block proof now lifts any valid,
token-preserving statement parser. Complete imports, exports, type aliases,
and enums have source-validity, token-window, carrier, cursor, and
start-position contracts.
Function declarations, constructors, fallback entries, and implementations now
reach the canonical boundary through the unconditional public Core block
contract. Trait methods, bodies, and complete trait declarations have full
source and state contracts. Contract fields and optional initializers also have
complete source and state contracts.
Individual trait predicates have reached the same boundary. Named parameters
preserve provenance through recovery, and their delimited function-parameter
list has the complete compositional boundary. Public lambda parameters also
have complete source, token-window, carrier, cursor, and starting-token
contracts.

The public lexer and parser are now total. For every `SourceFile`, public
parsing returns an ordinary output; neither fuel exhaustion nor an internal
parser invariant is reachable. Ordinary malformed input stays inside the same
output type and is represented by source-located diagnostics and recovery
nodes.

This result is assembled from the production parsers rather than assumed at
the outer API. It covers recursive types, expressions, patterns, statements,
Core blocks, inline Yul, all declaration forms, contract members, derive
handling, recovery, and complete-file accumulation. The corresponding proofs
also preserve the immutable token carrier, source ownership, cursor order, and
valid UTF-8 spans.

Every successful public result has one complete provenance contract covering
the parsed file, tokens, nested comments, lexical diagnostics, and parse
diagnostics. All carriers refer to the same input file, and the parsed file
retains its exact full-file span.

The next proof slice is intentionally different from the completed totality
work. It will define an independent declarative grammar for the canonical
syntax and prove that a diagnostic-free parser result is derivable in that
grammar. Recovered malformed output will receive a separate, explicit
soundness statement so that recovery is not confused with language
acceptance.

This frontend work remains separate from the completed syntax-independent
execution semantics. Resolution, source typing, and elaboration will consume
the canonical syntax result after the grammar boundary is coherent.

## Completion conditions

The canonical syntax slice is complete when:

- every active token and parsed-node form has an executable witness;
- the selected canonical corpus parses and obsolete spellings are rejected;
- lexical and parse diagnostics are deterministic and source-located;
- all retained token, comment, and AST spans use valid UTF-8 byte boundaries;
- ordinary malformed input produces total diagnostic output;
- the canonical frontend is the only current syntax described by public
  documentation; and
- the complete build, tests, metadata validation, and kernel audit pass.

Resolution, source typing, elaboration, and end-to-end source execution are the
next frontend stages. They consume the syntax result without changing the
meaning of checked Semantic Core or Oracle v5.
