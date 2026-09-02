# Current status

This page describes what works at the current revision and where its public
boundary ends. It is not an implementation-history ledger.

## At a glance

`solcore-lean` now has a public, syntax-independent path for checking Semantic
Core programs and executing checked contracts. Oracle v5 accepts an explicit
contract package, initial world, immutable execution environment, top-level
invocation, resource limits, and requested state probes. It returns a total
typed result as JSON.

The executable contract semantics and its Oracle v5 interface are implemented.
Checked-in command-line fixtures cover both Core checking and contract
execution, and the aggregate test and metadata checks protect those public
bytes.

A public Lean library can also generate reproducible, checker-sealed programs
from a pure Word/Boolean subset of Core Wire v3, package them as minimal Oracle
v5 scenarios, and enumerate type-preserving shrink candidates.

Standalone JSON Schema files have not been published for Core Wire v3 or
Oracle v5. Their closed wire catalogs and strict Lean codecs are the current
normative format definitions. Producing additional schema files is a packaging
task, not missing executable behavior.

Canonical Solcore syntax is implemented as a fresh `Solcore.Syntax` layer. Its
executable lexer and parser follow the stabilized syntax introduced by
`solcore-rs` PR #20 and do not reuse the Surface v1 or Multi AST and parser
definitions. Oracle v4 remains available only as a frozen historical
compatibility interface. Formal parser proofs continue after the executable
grammar; this does not block use of the Lean parser API.

## What works now

### Semantic Core

Semantic Core is the syntax-independent language consumed by the evaluator.
The current Core Wire v3 boundary supports:

- unit, Boolean, Word, product, sum, and function values;
- immutable bindings, conditionals, and local mutable cells;
- program-local algebraic data with normalized constructor matching;
- the current unary, binary, and ternary Word operations; and
- a frozen 14-entry host context for contract execution.

Core Wire v3 has canonical encoders and strict, resource-bounded decoders.
Unknown fields, missing fields, invalid tags, noncanonical scalar encodings,
and duplicate JSON keys are rejected deterministically.

Well-typedness is mandatory. Oracle v5 checks each Wire v3 program against the
frozen host context and admits it only on success. Unchecked Core cannot enter
the contract executor through the public boundary.

### Reproducible checked-Core inputs

`Solcore.Synthesis.CoreV3` provides a syntax-independent input source for
semantic testing. A caller supplies a 64-bit seed and a Program-node bound. The
versioned generator builds Core Wire v3 directly, restricts variables to Word
locals introduced by generated `let` expressions, and seals every result with
the frozen v3 checker.

The initial generated subset contains Word and Boolean literals, Word locals,
`let`, `if`, every current Word unary, binary, and ternary operation, and no
host effects or recursion. Its shrinker preserves binder scope, rechecks every
candidate, and returns only candidates that are strictly smaller by the fixed
node/literal order.

Generated cases use one explicit account and checked contract, then execute
through both the strict Oracle v5 text handler and the same one-record
dispatcher used by the command-line service. A fixed 256-seed corpus reaches
all 29 tracked forms and operators, returns normally at the declared regression
fuel, and freezes its request bytes and final generator states with a replay
fingerprint.

### Checked-contract execution

An execution request supplies all state and environmental inputs explicitly:

- a finite package of contract definitions expressed as Core Wire v3 programs,
  which the Oracle checks and admits before materialization;
- a finite initial `WorldState` with balances, nonces, sparse storage, and code;
- nested-call bindings and checked creation templates;
- an explicit creation-address policy;
- target, caller, call value, calldata, and evaluation fuel; and
- a finite list of state locations to observe.

The executor currently provides:

- one top-level checked-contract invocation;
- ordinary and value-bearing checked nested calls to depth one;
- non-wrapping, atomic balance transfer;
- checked creation with initializer execution and runtime-code installation;
- a static `uint256 -> uint256` ABI dispatcher;
- storage reads/writes and explicit caller, call-value, and calldata inputs;
- ordered Word logs; and
- one explicit shared evaluator-fuel budget. Internal resumption laws prove
  that completed effects are not replayed; Oracle v5 publishes no resume token.

The transaction lifecycle is explicit. A top-level return commits the working
world and journal. Top-level balance-preflight rejection, revert, or trap
selects the checkpoint.

Failed child calls and failed initializers roll back their local state and
journal effects before control returns to the parent.

### Total observations

A v5 execution response distinguishes:

- preflight rejection, such as an unavailable sender balance;
- normal return or revert, each with its data;
- trap with a Word reason;
- resource exhaustion or an internal invariant failure.

Every terminal `executed` result includes the rollback-selected journal and
the requested initial/committed state observations. Probes can observe account
presence, storage, balance, nonce, and installed code. Logs and successful
creation addresses preserve order and duplicates.

Fuel exhaustion is reported as `inconclusive`; the Oracle does not invent a
terminal state observation for an unfinished execution. The fuel counter is a
formal evaluator bound, not an EVM gas model.

## Public Oracle interfaces

All versions coexist in one NDJSON command-line service. A request's exact
`schema` selects its decoder and handler; adding v5 does not reinterpret older
requests.

| Interface | Purpose | Status |
| --- | --- | --- |
| Oracle v1 | Legacy general envelope and capability discovery | Frozen compatibility interface |
| Oracle v2 | Semantic Core v1 checking and evaluation | Frozen |
| Oracle v3 | Semantic Core v2 checking and evaluation | Frozen and supported |
| Oracle v4 | Surface v1 restricted single-file parsing | Frozen historical compatibility interface |
| Oracle v5 | Core v3 checking and checked-contract execution | Implemented and public |

Oracle v5 publishes three queries:

- `capabilities` reports the exact profile, schemas, limits, and feature set;
- `coreCheck` checks one Core Wire v3 program; and
- `execute` validates and runs one complete contract scenario.

The command-line executable reads one compact JSON object per line and emits
one result per line in order. Capability reports are also available directly:

```text
lake exe solcoreOracle capabilities-v3
lake exe solcoreOracle capabilities-v4
lake exe solcoreOracle capabilities-v5
```

`--version` intentionally retains its legacy v1 meaning. Use a versioned
capability command to discover a newer protocol contract.

The human-readable wire catalogs are [Core Wire v3](CORE_WIRE_V3.md) and
[Oracle v5](ORACLE_V5_WIRE.md).

Requests, typed responses, and protocol errors have canonical encoders and
strict decoders. They reject unknown or duplicate fields, query/verdict
mismatches, invalid catalog entries, and rollback observations that claim
committed effects.

## Canonical syntax status

Source identities, UTF-8 byte spans, the complete token catalog, the
source-preserving parsed AST, exact Unicode identifier classification, a
public identifier validator, and the canonical lexer and parser are
implemented under `Solcore.Syntax`. `import Solcore` exposes this API.

`Solcore.Syntax.Parser.parse` accepts a complete `SourceFile` and returns its
tokens, retained nested comments, lexical and parse diagnostics, and parsed
file. The executable grammar covers imports, exports, pragmas, aliases, enums,
derive attributes, traits, implementations, contracts, fields, constructors,
fallbacks, functions, types, expressions, patterns, statements, blocks, and
inline Yul. It applies the pinned nesting policy, preserves UTF-8 byte ranges
and written distinctions, and recovers ordinary malformed input without using
the exceptional result branch.

The checked-in suite embeds all 23 dedicated positive fixtures from the pinned
Rust parser and adds focused acceptance, rejection, recovery, comment, Unicode,
span, legacy-spelling, and deterministic source-mutation tests. A development
comparison against the same revision also parsed all 490 `corpus/ok` sources
without lexical or parse diagnostics. No acceptance or source-AST gap was found
in the fixed-revision parser audit. Four malformed inputs differ only because
Lean retains an additional explicit recovery diagnostic; exact diagnostic
kinds, byte ranges, order, and recovery ASTs are now regression-tested.

The public lexer is proved total. Its character-count bound always suffices,
and every returned token, nested comment, and lexical diagnostic belongs to
the input file and uses a valid UTF-8 byte span. Tokens and comments remain in
source order without overlap.

The parser is also proved total at its public boundary. Every `SourceFile`
produces an ordinary `ParseOutput`; the internal lexer- and parser-invariant
error branches are unreachable. Malformed source is therefore represented by
ordinary diagnostics and recovery syntax rather than by an internal failure.
The same guarantee holds when `parseLexed` is called with a lexer result that
satisfies the public lexical contract.

The proof is compositional across types, expressions, patterns, statements,
Core blocks, inline Yul, imports, exports, aliases, enums, traits,
implementations, functions, contracts, derive attributes, recovery, and the
complete file loop. Recursive expression, pattern, statement, type, and Yul
parsers have sufficient production fuel, while list and recovery loops either
advance or terminate. All top-level declarations and contract-member forms are
included in the unconditional result.

Every public output also has a source-provenance contract: its parsed file has
the input identity and full-file span, retained lexer carriers are unchanged,
and all token and diagnostic spans belong to that same file. These properties
cover recovered output as well as diagnostic-free output.

An independent declarative grammar now covers pragma declarations, maximal
dotted qualified names, both local and `@`-prefixed external module paths, and
identifier or parenthesized-operator selector names. Shared declarative rules
and parser-soundness theorems now also cover nonempty comma-separated lists
with an optional trailing comma, selected import names and aliases, nonempty
selected-import lists, hiding clauses, optional hiding dispatch, and both
allow-empty delimiter policies. Export coverage additionally includes
nonempty lists without trailing commas, constructor selections, prioritized
export names, local export items, and remote selections. Derive coverage now
includes ordinary and diagnosed reserved target components, maximal dotted
targets, and exact normal `#[derive(...)]` attributes; diagnostic-free public
attribute soundness excludes its malformed recovery path.

Shared generic parameters now have an exact nonempty `<...>` grammar with an
optional trailing comma. Required-list rejection records the exact delimiter
or nested checked-identifier failure. `requireGenericParameters` has no reject
branch; its defensive empty-list invariant is unreachable after a successful
required-list parse. An absent leading `<` is a nonconsuming optional success,
while a present guard commits from the original input and retains positive
evidence for that `<`. Required and optional success endpoints are
deterministic and each is exclusive with exact rejection. Both parsers also
retain unconditional success soundness and source-validity compositions.

Algebraic enums now have exact parser-independent ordinary success and
rejection coverage from the contextual `enum` marker through the closing
brace. A leading `(` commits constructor payload parsing; payloads may be empty
but cannot have a trailing comma. The custom body loop is reflected into the
allow-empty, allow-trailing delimited outcome relation with forward constructor
order and exact rejection remainders. Full declarations distinguish marker,
name, optional-generic, and body rejection. Constructor, body, and declaration
outcomes have deterministic success endpoints and disjoint success/rejection.
An already supplied derive attribute consumes no input, remains in the AST,
and supplies the outer span start; source validity composes with its existing
contract.

Recursive type expressions now have exact parser-independent coverage for
named, mapping, comptime, proxy, tuple, and function forms. Their mutually
recursive delimiter judgments retain empty and nonempty lists, optional
trailing commas, optional nonempty named arguments and function returns, exact
token windows, and written element order. The named branch also records the
failed `comptime<` and `mapping(` composite lookaheads that give the executable
dispatcher its priority. Soundness is unconditional for both the fuel-bounded
and public recursive type parsers and composes with the established source
validity contract.

Transparent type aliases now reuse that recursive type grammar after an exact
`type` keyword, name, prioritized optional parameter list that may be empty and
may have a trailing comma, equals sign, and semicolon. Their public theorem
requires diagnostic freedom only to exclude the alias-RHS recovery branch; the
normal alias path and recursive type theorem do not otherwise need that
premise. Recursive type, shared generic-parameter, type-alias, and
enum-declaration theorem families have compile-time consumers and public
`Solcore.Syntax` registration. The full build and `lake test` pass with those
registrations.

Backward diagnostic reflection is now a reusable parser proof boundary. A
diagnostic-free successful result can only have started from a diagnostic-free
parser state; this property composes through pure parsing, sequencing,
transactional choice, token consumers, and delimiter policies. Concrete
instances cover recursive types, named and delimited function parameters,
individual predicates, bare and grouped predicate sequences, optional `where`
clauses, and the generic-parameter, modifier, and return-clause leaves of a
function signature. Parameter recovery has a complementary commitment
theorem: every successful recovery or missing-type error retains a diagnostic.

`FunctionParameterParses` now describes exactly the ordinary and contextual
`comptime` typed forms, including the composite prefix absence that selects the
ordinary branch. `FunctionParametersParses` lifts that strict grammar through
the possibly empty parenthesized list with an optional trailing comma. Their
public success theorems require diagnostic freedom precisely to exclude error
and recovery values; both compose with the established source-validity
contracts.

The single public `namedParameter` also has a broad ordinary-outcome relation.
A missing colon is a diagnosed `.error` Core success at the post-name
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

Predicates and optional `where` clauses also have exact component grammars and
unconditional success soundness. Bare sequences retain forward predicate
order and distinguish a final predicate from a trailing comma; grouped
sequences reuse the nonempty trailing-delimiter grammar. `PredicateSequenceParses`
now records the transactional parser's exact grouped-first priority. Its bare
constructor carries `GroupedPredicateSequenceUnavailable`: this follows either
from absence of the opening `(`, or from an exact grouped rejection whose
`no_parse` theorem excludes every grouped derivation before transactional
fallback runs the bare parser from the original input. Exact rejection traces
now also cover bare tails, complete bare sequences, and the grouped-first
dispatcher. The fallback rejection retains the grouped attempt's intermediate
remainder separately from the final bare rejection reached from the original
input. Bare and complete sequence outcomes are deterministic and success/reject
exclusive. For optional `where`, an absent contextual marker is a nonconsuming
success, while a present marker commits to the prioritized predicate sequence.
Executable ordinary rejection is reflected exactly as that committed sequence
rejection; the successful remainder is deterministic and success/rejection are
exclusive.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable rejection reflects the exact nested
type or delimiter remainder. The successful endpoint is deterministic and
success/rejection are exclusive.

Function modifiers are parsed in the fixed optional `public`-then-`payable`
order, with unconditional grammar soundness. A diagnostic-free module parse
proves both markers absent because either marker commits an
outside-contract diagnostic, while every syntactically ordered pair is
allowed in a contract. Complete diagnostic-free function signatures, ending
before a function body or trait-method semicolon, now derive
`FunctionSignatureParses` under the corresponding module or contract policy.
The proof reflects diagnostic freedom backward through `where`, returns, and
modifiers before applying strict parameter-list soundness, and it matches the
parser and declarative signature endpoint definitions exactly. Source
validity composes with the same result. These parameter, predicate/`where`,
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

A broad ordinary `functionDecl` outcome is likewise independent of location.
Success composes the ordinary signature directly into an isolated `.allow`
Core body, retaining the exact declaration AST, signature-to-body order, outer
cover span, and final remainder. Rejection has exactly two externally visible
stages: signature rejection, or an uncaptured body rejection after ordinary
signature success. A rejection inside a balanced captured child block does not
escape; isolation emits its diagnostic and returns an ordinary empty-body
recovery success at the parent remainder. Declaration success endpoints are
deterministic and exclusive with rejection. The existing location-policy-aware
`FunctionDeclParses` theorem remains the stricter diagnostic-free judgment.

A broad ordinary `constructorDecl` outcome now follows the executable stages
exactly: the required `constructor` keyword, recovery-aware parameters,
optional `public` then `payable`, and an isolated `.require` Core body. An
explicit `public` marker emits its constraint diagnostic but is discarded from
the AST, while diagnostic emission leaves the declarative remainder unchanged.
Success preserves the parameter and payable fields, exact final remainder, and
the marker-to-body cover span of the complete constructor AST. Rejection has
exactly three external stages: missing marker, rejected parameters, or an
uncaptured body rejection after modifier success. A balanced captured child
rejection instead yields diagnosed empty-body recovery success at the parent
remainder. Outcomes are deterministic and exclusive, while the existing
`ConstructorDeclParses` relation remains the strict diagnostic-free judgment.

A broad ordinary `fallbackDecl` outcome now begins with the exact `fallback`
keyword and recovery-aware parameters, followed by a pure validation stage.
Empty parameters pass silently; nonempty parameters remain in the AST and emit
the fallback-specific diagnostic without changing the declarative remainder.
Parsing then keeps the fixed optional `public`-then-`payable` modifier order and
enters an isolated `.require` Core body. Success preserves the complete AST,
marker-to-body cover span, retained parameters, payable marker, and exact final
remainder. Rejection exposes exactly three external stages: missing marker,
rejected parameters, or an uncaptured body rejection after validation and
modifier success. A balanced captured child rejection instead becomes a
diagnosed empty-body recovery success at the parent remainder. Outcomes are
deterministic and exclusive; strict diagnostic-free `FallbackDeclParses` remains.

Implementation outcomes now cover the optional `default` prefix, contextual
marker, optional generics, trait name, required nonempty trailing-comma head
types, optional `where`, custom method body, and complete AST. The default
prefix cannot reject, and the pure nonempty refinement adds only an invariant
branch. The right-brace-first body loop retains positive `function` guards,
strict progress, forward method order, and exact unexpected or nested
rejection remainders. Full declarations expose six rejecting stages after the
default prefix: marker, generics, name, head arguments, `where`, and body.
Default, head, method, body, and declaration outcomes are deterministic and
exclusive; module diagnostics and captured-body recovery remain successes.

Trait methods now extend the broad module-signature outcome through an exact
semicolon, retaining diagnostic-producing signature successes and separating
signature from missing-semicolon rejection. Trait bodies reflect the custom
right-brace-first loop with positive `function` guards, strict progress,
forward method order, and exact unexpected, nested-method, and recursive
rejection remainders. Complete declarations distinguish contextual marker,
name, required generics, optional `where`, and body rejection. Method, body,
and declaration success endpoints are deterministic and success/rejection
exclusive. The strict diagnostic-free `TraitDeclParses` family and its
source-validity compositions remain available beside the publicly exported
broad outcomes.

Ordinary function declarations and strict diagnostic-free implementations
retain parametric parser-independent judgments over an abstract block
relation. Function soundness composes the exact location-specific signature,
isolated body, outer cover span, and final remainder. Implementation soundness
additionally retains optional-`default` priority, nonempty trailing-comma head arguments,
module-policy methods, right-brace-first body dispatch, strict method progress,
and forward method order. These APIs reflect diagnostic freedom through every
nested body and have source-validity compositions, consumers, and public
registration.

Contract declarations now lift the same abstract expression and block
relations through fields, functions, constructors, fallbacks, aliases, and
enums in exact executable priority order. Attribute-aware members accept a
derive attribute only on enums; body soundness preserves exact braces,
right-brace priority, strict member progress, forward member order, and rules
out every recovery success using its required diagnostic. Complete contract
soundness retains the marker, name, optional generics, body span, members, and
final remainder, with source-validity composition and public consumers.

The same abstract relations now extend through complete top-level dispatch and
the complete-file parser. `PlainTopItemParses` records the exact negative
lookaheads for every earlier declaration branch, while `TopItemParses` records
leading-hash priority and permits derive attachment only to enums.
`TopItemsParses` preserves declaration order, strict cursor progress, and
end-of-window termination. `SourceFileParses` additionally specifies the exact
pure attachment of the complete source-order comment stream. Diagnostic
reflection through every declaration and top-item branch rules out all file
recovery successes, so every diagnostic-free `sourceFile` result derives this
parameterized complete-file grammar and composes with source validity.
Parser-independent judgments now cover raw, balanced, isolated, and canonical
Core blocks; the complete Core expression layer; the ordered public Core
pattern layer; Core `let`, `return`, assignment, `for`, `match`, assembly,
block, `while`, `if`, `break`, and `continue` statements, and their complete
ordered dispatcher. Their mutually recursive executable expression, pattern,
statement, and block parsers are now closed by fuel-indexed ordinary/reject
outcome families. The public fuel bounds are explicit: expressions and
patterns use the active-window remainder plus one, statements use it plus two,
and blocks use the fixed statement fuel of the remainder plus one. Public
success and rejection soundness, deterministic outcome specifications, and
diagnostic reflection are registered for all four entry points.

Inline-Yul coverage includes name sequences, the public expression layer,
exact braced blocks, `let`, assignment, expression and source-level
`return(...)` statements, `if`, `for`, `switch`, function definitions,
keyword controls, optional semicolons, the complete ordered dispatcher, and
the diagnostic-free recovery boundary. Transactional constructor,
call-argument, and Yul-assignment fallbacks carry concrete parser-independent
rejection witnesses whose disjointness laws preserve parser priority. The
public recursive Yul expression, statement, and braced-body parsers are closed
by fuel-indexed clean/ordinary/reject outcome families, including recovery,
transactional rewind, exact statement priority, optional semicolons, and block
boundaries.

`CoreTopItemOrdinaryParses` now supplies the public Core expression relation
and the isolated `.allow` and `.require` block relations to the abstract
top-item grammar. `CoreSourceFileOrdinaryParses` lifts that specialization
through exact item order, complete-window consumption, and comment attachment.
`CoreSourceFileOrdinaryParsesFromStart` fixes both the root token window and its
canonical terminal remainder: the carrier and `endIndex` are preserved and the
final cursor is exactly the token count. Every diagnostic-free successful
`parseLexed` result derives that judgment over the supplied lexer tokens and
comments; the public `parse` theorem states it over the tokens and comments
retained in its output. Paired theorems add canonical parsed-file source
validity at both boundaries.
The component relations deliberately remain recovery-aware ordinary
over-approximations, while the outer diagnostic-free premise excludes actual
recovery successes at the complete-file boundary.

Import leaves and payload helpers now have exact broad outcomes. Selector names
choose a checked identifier when `(` is absent; a positive `(` commits to a
nonempty maximal operator-symbol scan and exact `)`. An absent selected-name
`as` is a nonconsuming `none`, while a positive guard commits to one checked
identifier. Module paths similarly choose a local qualified name when `@` is
absent and commit to an external qualified name after exact `@`. Selected
entries parse source then alias, and both selected-import and hiding braces
require a nonempty, trailing-comma-permitting list. Optional hiding is
nonconsuming when its contextual marker is absent and commits to the complete
clause when present.

The import terminator consumes an exact semicolon. If it is missing immediately
before one of the exact top-item starters, it instead records a diagnostic,
returns the last payload span, and succeeds without consuming that starter;
every other missing terminator rejects. Plain, namespace, wildcard, and
selective payload outcomes compose these leaves in executable order, retain
the exact AST, covering span, cursor, token carrier, and active window, and
separate the first rejecting stage. Every endpoint is deterministic and its
success and rejection relations are exclusive.

The complete broad `importDecl` outcome also records the exact leading
`import` token and nonconsuming dispatch evidence. A leading `*` selects
namespace import exactly when offset-one lookahead is hard `as`; otherwise it
commits to wildcard import. Without `*`, `{` selects the selective branch and
every other token selects plain import. Branch failure never falls through to
a later alternative, and the complete outcome remains deterministic and
exclusive while preserving terminator recovery success.

Export leaves, payloads, and the complete `exportDecl` now likewise have exact
broad outcomes. Export paths consume maximal dotted checked names. Constructor
selection prioritizes the `(*)` form over a nonempty, no-trailing-comma name
list; export names prioritize `*`, then a parenthesized operator selector, then
a checked identifier with optional constructor selection. A local item uses
identifier-plus-offset-one-dot lookahead to commit to qualified `path.*`, and
otherwise parses an export name. Remote selection chooses either `*` or an
allow-empty, trailing-comma-permitting braced export-name list.

Local payloads compose an allow-empty, trailing-comma-permitting item list with
an exact, nonrecovering semicolon. Path payloads parse a maximal path, then
prioritize dot plus selection, absent-dot `as` plus checked alias, and finally
the bare module form; every branch ends at the same exact semicolon boundary.
The aggregate consumes exact `export`, dispatches on a nonconsuming `{` guard,
and retains exact AST, covering span, carrier, window, cursor, and first
rejection. All endpoints are deterministic and success/rejection exclusive.
The declarative and parser outcome packages are exported publicly and checked
by dedicated and public-boundary consumers; broader top-item rejection remains
a separate boundary.

At the complete diagnostic-free declaration level, strict soundness now covers
all four canonical import forms—plain, namespace, wildcard with or without a
hiding clause, and selective imports—transparent type aliases, and traits.
Unconditional strict soundness also covers all four canonical export forms:
local, module, module alias, and items-from-module, together with complete
algebraic enums. Parser-independent `ImportDeclParses` and `ExportDeclParses`
judgments combine their respective forms without caller-supplied AST shape
guards. `EnumDeclParses` directly characterizes complete enum success while
retaining the supplied derive attribute. Export and enum soundness need no
diagnostic-free premise. These declaration judgments now feed the exact
`PlainTopItemParses` and derive-aware `TopItemParses` correspondences. The
complete file-loop and `sourceFile` theorems preserve forward item order,
strict cursor progress, end-of-window termination, exact comment attachment,
and recovery exclusion by diagnostic commitment. The generic theorem remains
reusable with abstract expression and block relations, and its concrete Core
ordinary specialization is now public and compile-time consumed. Recovered
malformed output remains separate so that recovery is not confused with
language acceptance.

Resolution, source type checking, and elaboration into checked Semantic Core
are separate later stages. No new frontend result is published through Oracle
v4; that interface continues to mean only its frozen Surface v1 format.

## What is not yet claimed

The current public system is not yet an end-to-end implementation for arbitrary
Solcore source text. In particular, it does not yet provide:

- source resolution, typing, elaboration, and execution as one pipeline;
- unbounded recursive contract-call depth;
- a general dynamic ABI, memory model, or bytecode interpreter;
- Ethereum gas, fees, block context, address derivation, or full EVM equivalence;
- generation beyond the current pure Word/Boolean Core subset, including
  functions, data, cells, and host effects; or
- an automated semantic differential-testing harness against other Solcore
  implementations.

The intended longer-term direction remains aligned with those last two items:
expand generation to more well-typed programs, run the same programs through
independent implementations, and compare normalized semantic observations.
Oracle v5 is
the execution and observation boundary needed for that work, not the completed
differential-testing system itself.

## Validation boundary

The repository checks different kinds of claims at different layers:

- Lean types prevent incompatible checked-program and response combinations;
- proofs connect evaluator, state, checkpoint, and rollback operations to laws;
- general materialization theorems prove exact pointwise lookup, absence,
  balance, nonce, storage, code, registry, template, route, and default-address
  behavior for every successfully accepted finite world and environment;
- executable tests cover checking, admission, materialization, fuel boundaries,
  return, revert, trap, nested calls, balances, creation, logs, and encoding;
- a public-handler regression repeats the same execution request with the same
  fuel and checks identical typed, canonical JSON, and canonical text results;
- the synthesis regressions check all tracked constructors and operators,
  exact corpus replay, normal public execution, and type-preserving strict
  shrinking;
- strict wire tests fix canonical JSON shapes and deterministic error priority;
- metadata validation checks published profiles, digests, and capability output;
  and
- the kernel audit checks the compiled declaration trust boundary.

These checks establish the behavior of the formal model that is present. They
do not establish source-language conformance for features that have no current
frontend-to-Core path, nor do they establish equivalence with the EVM or either
external Solcore compiler.

From the repository root, the full local validation entry points are:

```text
lake build
lake test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

For protocol-level details, use the wire catalogs rather than internal Lean
module names. For supported-feature comparisons and external implementation
boundaries, see the [compatibility matrix](COMPATIBILITY_MATRIX.md).
