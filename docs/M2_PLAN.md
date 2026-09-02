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

The independent declarative grammar now covers pragma declarations, maximal
dotted qualified names, local and `@`-prefixed external module paths, and
identifier or parenthesized-operator selector names. Shared declarative rules
and parser-soundness theorems also cover nonempty comma-separated lists with
an optional trailing comma, selected import names and aliases, nonempty
selected-import lists, hiding clauses, optional hiding dispatch, and both
allow-empty delimiter policies. Export coverage additionally includes
nonempty lists without trailing commas, constructor selections, prioritized
export names, local export items, and remote selections. Derive targets and
normal `#[derive(...)]` attributes now have exact parser-independent grammars;
the public attribute theorem uses diagnostic freedom only to exclude recovery.

Shared generic parameters now have an exact nonempty `<...>` grammar with an
optional trailing comma. Required-list rejection records the exact delimiter
or nested checked-identifier failure. `requireGenericParameters` adds no
reject branch; its defensive empty-list invariant is unreachable after a
successful required-list parse. The optional judgment makes an absent `<` a
nonconsuming success, while a present guard commits from the original input
and retains positive evidence for that `<`. Required and optional success
endpoints are deterministic and each is exclusive with exact rejection. Both
parsers also retain unconditional success soundness and compose with their
established source-validity contracts.

Algebraic enum declarations now have exact grammar and unconditional success
soundness from the contextual `enum` marker through the closing brace.
Constructor payloads are selected by a leading `(`; when present, they may
contain zero fields but cannot have a trailing comma. Bodies may be empty,
admit an optional trailing comma, and preserve constructors in forward source
order. Every successful enum declaration is unconditionally grammar-sound. It
retains an already supplied derive attribute in its AST and uses that
attribute's span as the outer span start; source validity composes with the
supplied derive contract.

Recursive type expressions now have exact mutual declarative judgments for
named, mapping, comptime, proxy, tuple, and function forms. The concrete
recursive delimiter rules retain empty and nonempty lists, optional trailing
commas, optional nonempty named arguments and function returns, exact token
windows, and source element order. Named-type derivations explicitly retain
the failed `comptime<` and `mapping(` pair lookaheads that select the dispatcher
branch. Both the fuel-bounded parser and the public recursive type parser have
unconditional success soundness, with source validity available by
composition.

Transparent aliases now have an exact grammar for their keyword, name,
prioritized optional parameter list that may be empty and may have a trailing
comma, equals sign, recursive value type, and semicolon. Diagnostic freedom is
used only to rule out the executable alias-value recovery branch; ordinary
recursive type success is already unconditional. Recursive type, shared
generic-parameter, type-alias, and enum-declaration theorem families have
compile-time consumers and public `Solcore.Syntax` registration. The full
build and `lake test` pass with those registrations.

Backward diagnostic reflection now provides the reusable bridge needed by
strict diagnostic-free grammars: diagnostic-free successful output implies a
diagnostic-free parser input. The laws cover pure parsing, sequencing,
transactional choice, primitive token consumers, and delimiter policies, and
are instantiated through recursive types, parameters, predicates and their
sequences, optional `where`, generic parameters, modifiers, and return
clauses. Named-parameter recovery and missing-type errors separately prove
that every successful error path commits a diagnostic.

Typed named parameters now have an exact `FunctionParameterParses` grammar for
ordinary and contextual `comptime` forms. The ordinary constructor records
the absence of the composite `comptime`-identifier prefix, and
`FunctionParametersParses` lifts the element grammar to a possibly empty,
optionally trailing-comma parenthesized list. Diagnostic freedom excludes
parameter error and recovery nodes, yielding strict element and list
soundness with source-validity compositions.

The single public `namedParameter` now also has a broad ordinary-outcome
relation. A missing colon is a diagnosed `.error` Core success at the post-name
remainder, not recovery. Only a Core rejection rewinds to the original cursor:
end, comma, or right parenthesis gives exact nonconsuming rejection; otherwise
the parser emits the failure diagnostic and performs its mandatory-first-token
maximal recovery scan. A carrier hole is reflected as recovery rejection.
Success endpoints are deterministic and exclusive with rejection, while the
strict `FunctionParameterParses` relation remains diagnostic-free.

The canonical `TypeExpr` and recovery-aware `namedParameter` outcomes now lift
to the `(` / `)` parameter list, with empty contents and a trailing comma
allowed. Delimiter and nested rejection endpoints are exact: recovery stops
leave an outer comma or right parenthesis unconsumed, a carrier hole remains a
nested rejection, and recovery to the window end may then yield exact
`delimiterMissing` rejection. Success endpoints are deterministic and
exclusive with rejection; strict `FunctionParametersParses` remains the
diagnostic-free list relation.

Individual predicates, nonempty bare and grouped predicate sequences, and
prioritized optional `where` clauses now have parser-independent grammars and
unconditional success soundness. Bare tails preserve forward order and their
optional trailing comma; grouped sequences use the generic nonempty trailing
delimiter grammar. Transactional grouped-or-bare dispatch now records exact
grouped-first priority. A bare result carries
`GroupedPredicateSequenceUnavailable`, derived either from opening-parenthesis
absence or from exact grouped rejection and its `no_parse` consequence before
transactional fallback restarts at the original input. Exact rejection traces
cover the bare tail, the complete bare sequence, and grouped-first dispatch.
When both transactional alternatives reject, the grouped attempt's intermediate
remainder is retained separately while the relation returns the final bare
remainder reached from the original input. Bare and complete sequence outcomes
have deterministic success remainders and exclude simultaneous rejection. An
absent contextual `where` marker is a nonconsuming success, while a present
marker commits to the prioritized predicate sequence. Executable ordinary
rejection is reflected exactly as that committed sequence rejection; optional
`where` has a deterministic success remainder and exclusive success/rejection
outcomes.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable ordinary rejection reflects the exact
nested type or delimiter remainder. The success endpoint is deterministic and
success/rejection outcomes are exclusive.

Optional function modifiers now preserve exact keyword absence or presence in
the fixed `public`-then-`payable` order. Modifier grammar soundness is
unconditional; diagnostic-free module success proves that both contract-only
markers are absent, while contract success satisfies its permissive policy.
The complete diagnostic-free `functionSignature` parser, which ends before a
function body or trait-method semicolon, now derives `FunctionSignatureParses`
for either location. Its proof reflects diagnostic freedom from `where`
through returns and modifiers to the parameter boundary, retains every
intermediate remainder and AST field, and identifies the parser and
declarative endpoint calculations exactly. Source validity composes with the
generic location-indexed theorem. These parameter, predicate/`where`,
modifier, and function-signature theorem families are exported through
`Solcore.Syntax` and checked by compile-time consumers.

A broad ordinary `functionSignature` outcome is now independent of location
and modifier policy. Success preserves the exact keyword, name, generics,
recovery-aware parameters, modifiers, returns, and `where` order, complete AST,
signature cover span, and final remainder. Rejection records the first failing
keyword, name, generics, parameter-list, returns, or `where` stage. Modifiers
always succeed; module-location markers may instead emit diagnostics without
changing the declarative remainder. Success endpoints are deterministic and
exclusive with rejection, while `FunctionSignatureParses` remains the strict
diagnostic-free, location-policy judgment.

The broad ordinary `functionDecl` layer is now complete and location
independent. Its success judgment sequences the ordinary signature into the
isolated `.allow` Core body and preserves the exact declaration AST, outer
signature/body cover span, and final remainder. Its exact rejection judgment
has only the signature branch and the uncaptured body branch reached after
ordinary signature success. A balanced captured child's rejection is instead
an empty-body success with a retained recovery diagnostic and the exact parent
remainder. The combined declaration outcomes are deterministic and mutually
exclusive. This complements, rather than replaces, the location-policy-aware
diagnostic-free `FunctionDeclParses` boundary.

The broad ordinary `constructorDecl` layer now records the exact executable
order from the required `constructor` keyword through recovery-aware
parameters, optional `public` then `payable`, and the isolated `.require` body.
An explicit `public` marker emits a diagnostic but is omitted from the AST, and
that emission does not change the declarative remainder. Successful derivations
retain the exact parameter and payable fields, final remainder, and complete
marker/body cover span. Exact rejection exposes only a missing marker, rejected
parameters, or an uncaptured body rejection after successful modifiers. A
rejection inside a balanced captured child becomes diagnosed empty-body
recovery success at the exact parent remainder. Success is deterministic and
exclusive with rejection; strict diagnostic-free `ConstructorDeclParses`
continues to coexist as the canonical acceptance judgment.

The broad ordinary `fallbackDecl` layer now follows the exact `fallback`
keyword with recovery-aware parameters and a pure validation outcome. Empty
parameters pass directly, while nonempty parameters are retained in the AST
and emit their constraint diagnostic without changing the declarative
remainder. Fixed optional `public`-then-`payable` modifiers then precede the
isolated `.require` body. Success retains every AST field, the marker/body cover
span, and the exact final remainder. Exact rejection has only marker absence,
parameter rejection, or uncaptured body rejection after validation and
modifier success. A balanced captured child rejection is absorbed as diagnosed
empty-body recovery at the parent remainder. Success endpoints are deterministic
and exclusive with rejection, while strict diagnostic-free
`FallbackDeclParses` continues as the canonical acceptance judgment.

The implementation-method wrapper now carries that broad declaration contract
one level upward. Its exact AST adds only the empty parser-time comment list,
and its final remainder is unchanged; its sole rejection stage is the nested
function declaration. Module modifier diagnostics and captured-body recovery
stay on the success path. The resulting method endpoints are deterministic and
mutually exclusive.

Trait methods now add the exact terminating semicolon to a module-policy
signature. Trait bodies preserve forward method order, exact braces, the
right-brace-first loop priority, and the retained body cover span. Backward
diagnostic reflection through that loop yields complete diagnostic-free
`TraitDeclParses` soundness from the contextual marker through required
generics, optional `where`, and the final brace. Method, body, and declaration
theorems have source-validity compositions, public registration, and
compile-time consumers.

Function declarations now compose exact location-indexed signatures with an
abstract parser-independent block relation. Implementations lift the same
boundary through optional `default`, nonempty head arguments, optional
`where`, module-policy methods, right-brace priority, strict progress, and
forward-order body accumulation. Their diagnostic-free reflection,
source-validity compositions, consumers, and public imports are complete.
Contract declarations now extend these parametric boundaries through exact
member dispatch, enum-only derive attachment, brace-delimited forward member
order, strict progress, and recovery exclusion by diagnostic commitment.
Their body and declaration soundness theorems compose with source validity and
are publicly consumed. Exact plain and derive-aware top-item judgments now
compose every declaration branch in executable priority order. Their
diagnostic reflection feeds a complete-file theorem that preserves forward
item order, strict progress, end-of-window termination, exact source-order
comment attachment, and recovery exclusion. The resulting `SourceFileParses`
boundary composes with source validity and is publicly consumed. Independent
Core block, expression-layer, and ordered pattern-layer judgments are now in
place, together with Core simple, control, `for`, `match`, and assembly
statement judgments. Inline-Yul coverage now includes name sequences, the
public expression layer, exact braced blocks, `let`, assignment, expression
and source-level `return(...)` statements, `if`, `for`, `switch`, function
definitions, keyword controls, optional semicolons, and the complete ordered
dispatcher through its diagnostic-free recovery boundary. The aggregate Core
dispatcher is also complete. Concrete rejection witnesses now cover delimited
constructor/call fallbacks and public Yul assignment. The public Yul
expression, statement, and braced-body parsers have complete fuel-indexed
clean/ordinary/reject closures, including recovery, transactional rewind,
exact dispatcher priority, optional termination, and block-boundary rejection.
The mutually recursive Core expression, pattern, statement, and block parsers
now likewise have fuel-indexed ordinary/reject closures, public production-fuel
specializations, deterministic outcomes, and backward diagnostic reflection.
The concrete `CoreSourceFileOrdinaryParses` grammar instantiates the completed
parametric file theorem with public Core expressions and isolated `.allow` and
`.require` bodies. `CoreSourceFileOrdinaryParsesFromStart` fixes its exact root
window and canonical terminal remainder, preserving the carrier and `endIndex`
while setting the final cursor to the token count. Diagnostic-free successful
`parseLexed` and `parse` results derive that form over their exact input or
retained-output carriers, and paired theorems add canonical parsed-file source
validity. The ordinary component relations remain reusable for recovered
parser outcomes; the diagnostic-free premise excludes such recoveries from
these public conclusions.

At the complete diagnostic-free declaration level, strict soundness now covers
all four canonical import forms—plain, namespace, wildcard with or without a
hiding clause, and selective imports—transparent type aliases, and traits.
Unconditional strict soundness also covers all four canonical export forms:
local, module, module alias, and items-from-module, together with complete
algebraic enums. Parser-independent `ImportDeclParses` and `ExportDeclParses`
judgments combine their respective forms without caller-supplied AST shape
guards. `EnumDeclParses` directly characterizes complete enum success while
retaining the supplied derive attribute. Export and enum soundness need no
diagnostic-free premise. `PlainTopItemParses` records exact earlier-branch
absence, and `TopItemParses` records leading-hash priority and enum-only derive
attachment. The complete-file item loop and `SourceFileParses` theorem now
preserve forward order, strict progress, end-of-window termination, exact
comment attachment, and recovery diagnostics. Recovered malformed output
remains separate so that recovery is not confused with language acceptance.

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
- every diagnostic-free public `parseLexed` or `parse` result is proved
  derivable in both the parametric independent grammar and its concrete
  mutually recursive Core term, block, and inline-Yul ordinary specialization;
- the canonical frontend is the only current syntax described by public
  documentation; and
- the complete build, tests, metadata validation, and kernel audit pass.

Resolution, source typing, elaboration, and end-to-end source execution are the
next frontend stages. They consume the syntax result without changing the
meaning of checked Semantic Core or Oracle v5.
