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

The recursive validity contracts for types, Yul syntax, Core expressions,
patterns, and Core statements are independent of parser control flow. The
proof implementation currently has the following shape:

- public type and Yul parsers are complete at the compositional boundary;
- pattern leaves, constructors, groups, tuples, comptime forms, dispatch, and
  recovery are complete. The public parser has unconditional canonical
  source-validity, token-window, carrier, cursor, and starting-token guarantees;
- established expression atoms, groups, tuples, arrays, operator helpers, and
  the left- and non-associative layers have complete contracts. Concrete atom
  parsing, including lambda and recovery, has source, state, strict-progress,
  and starting-token contracts that compose through postfix, unary, every
  binary precedence, and conditional parsing;
- conditional folding, the conditional tail, and the outer conditional parser
  have complete source-validity, token-window, carrier, cursor, and
  starting-token contracts;
- lambda return types and lambda-expression state/start/end behavior are
  proved, and public lambda-parameter parsing has complete source-validity,
  token-window, carrier, cursor, and starting-token contracts across ordinary,
  comptime, stop-token, rewind, and recovery paths;
- the generic unary wrapper has complete source-validity, token-window,
  carrier, cursor, and starting-token contracts;
- assignment/expression, `let`, return, block, `while`, `if`, `for`, inline
  assembly, `break`, and `continue` statements are complete, including both
  `for` item forms and item lists;
- match cases, the repeated case loop, and optional `default` parsing are
  complete, and the enclosing `match` parser has complete source, state,
  strict-progress, and starting-token contracts; and
- recognized-statement fallback preserves source validity and state across
  primary success, fallback success, rejection, diagnostic reset, and
  diagnostic re-emission. The complete eleven-branch statement dispatch is
  assembled from those contracts; and
- expression, pattern, and statement are closed in one simultaneous fuel
  induction. Step-indexed canonical validity discharges its explicit closure
  premise, yielding unconditional public contracts for expressions, patterns,
  statements, and Core blocks.

Contract-member dispatch, derive attachment, recovery, the complete contract
body, the outer declaration, and top-level recovery now have canonical
source/state contracts. Comment attachment preserves validity for every
top-level branch, item list, and complete parsed file. All nine plain top-level
declarations, the derive-aware item parser, the item loop, `sourceFile`,
`parseLexed`, and public `parse` are therefore composed without an assumed
declaration contract.

Successful public output now has one unconditional contract covering the
canonical parsed file plus every retained token, lexical-diagnostic, and
parse-diagnostic span. Nesting diagnostics also have direct source provenance.

Totality is being closed from the outside inward. The production bounds for
top-level and contract-member recovery, malformed type-alias recovery, pragma
accumulation, and generic comma-delimited lists are proved adequate. The
complete contract body now exposes five member obligations: field, contract
function, constructor, fallback, and enum. The file loop and public parser
expose five declaration obligations: module function, enum, trait,
implementation, and contract. Import, export, type alias, pragma, and the
complete derive path are already discharged. The shared recursive type parser
is invariant-free with proved production-fuel adequacy across every type form.

Term totality now covers the complete expression precedence layer and the
complete recovering pattern layer. Lambda parameters are unconditionally
total; lambda atoms, postfix operations, unary operators, binary operators, and
conditionals compose from explicit recursive expression and block contracts.
Pattern totality lifts through the recursive fuel family and reaches the public
parser under the matching expression-family premises.

Statement totality covers assignment/expression fallback, `let`, `return`,
`break`, `continue`, and Core block iteration/isolation. Fuel-aware fallback is
also complete. The next proof step is to finish fuel-aware blocks, recursive
control statements, and inline Yul, close the simultaneous expression and
statement families, discharge the remaining declaration branches, and then
prove success soundness against a declarative grammar.

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
