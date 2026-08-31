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
Function declarations reach the same boundary once their recursive block
parser supplies its validity contract; constructors and fallback entries have
the corresponding conditional guarantee for non-tail bodies. Individual trait
predicates have reached the same boundary. Named parameters preserve provenance
through recovery, and their delimited function-parameter list has the complete
compositional boundary. Public lambda parameters also have complete source,
token-window, carrier, cursor, and starting-token contracts.

The recursive validity contracts for types, Yul syntax, Core expressions,
patterns, and Core statements are independent of parser control flow. The
proof implementation currently has the following shape:

- public type and Yul parsers are complete at the compositional boundary;
- pattern leaves, constructors, groups, tuples, comptime forms, dispatch, and
  recovery are complete. The public fuel-indexed parser lifts these contracts
  to source-validity, token-window, carrier, cursor, and starting-token
  guarantees under the documented all-fuel `coreExpression` assumptions;
- established expression atoms, groups, tuples, arrays, operator helpers, and
  the left- and non-associative layers have complete contracts. Generic postfix
  tail and wrapper contracts are complete structurally and for retained source,
  and concrete `expressionAtom` parsing has token-window, carrier, cursor, and
  starting-token contracts. Its source-validity contract remains open;
- conditional folding, the conditional tail, and the outer conditional parser
  have complete source-validity, token-window, carrier, cursor, and
  starting-token contracts;
- lambda return types and lambda-expression state/start/end behavior are
  proved, and public lambda-parameter parsing has complete source-validity,
  token-window, carrier, cursor, and starting-token contracts across ordinary,
  comptime, stop-token, rewind, and recovery paths;
- the generic unary wrapper has complete source-validity, token-window,
  carrier, cursor, and starting-token contracts;
- assignment/expression, `let`, return, block, `while`, `if`, and `for`
  statements are complete, including both `for` item forms and item lists; and
- match cases, the repeated case loop, and optional `default` parsing are
  complete. The enclosing `match` parser has token-window, carrier, cursor, and
  starting-token contracts, while its source-validity contract remains open.

The next proof work is therefore concrete: prove source validity for
`expressionAtom`, carry it through the generic postfix and unary wrappers into
the recursive expression path, assemble complete lambda-expression validity,
and prove source validity for the enclosing `match` parser. Remaining
declarations and the complete-file parser follow.
Parser-generated diagnostic validity, grammar-invariant provenance and
unreachability, resource bounds, and success soundness against a declarative
grammar remain part of the final boundary.

Executable coverage preceded deep grammar-specific proof regeneration. The
proof work now targets the completed executable grammar while preserving the
already completed, syntax-independent execution semantics.

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
