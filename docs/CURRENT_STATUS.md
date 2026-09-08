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

Generic delimited outcomes now transport the stronger exact contract through
all four required-or-empty and trailing-or-no-trailing policies. Given exact
nested outcomes, tail relations fix forward elements, closing span, and final
remainder; complete relations fix the full `DelimitedList` AST; and every
delimiter rejection policy fixes its first failing remainder. The four exact
spec constructors are exported and compile-time consumed. This is a reusable
conditional law and does not assert that every existing nested production has
already acquired an exact contract.

Prioritized transactional fallback now has the matching generic exact
transport. Exact primary and fallback outcomes determine one successful value
and final remainder; success in the primary excludes fallback selection; and a
double rejection returns the unique original-input endpoint. The constructor
is exported and compile-time consumed, while each concrete use must still
supply exact contracts for both alternatives.

Shared generic parameters now have an exact nonempty `<...>` grammar with an
optional trailing comma. Required-list rejection records the exact delimiter
or nested checked-identifier failure. `requireGenericParameters` has no reject
branch; its defensive empty-list invariant is unreachable after a successful
required-list parse. An absent leading `<` is a nonconsuming optional success,
while a present guard commits from the original input and retains positive
evidence for that `<`. Required and optional success endpoints are
deterministic and each is exclusive with exact rejection. Both parsers also
retain unconditional success soundness and source-validity compositions.

Algebraic enums now have complete parser-independent ordinary success and
rejection coverage from the contextual `enum` marker through the closing
brace. A leading `(` commits constructor payload parsing; payloads may be empty
but cannot have a trailing comma. The custom body loop is reflected into the
allow-empty, allow-trailing delimited outcome relation with forward constructor
order and exact rejection remainders. Full declarations distinguish marker,
name, optional-generic, and body rejection. Constructor, body, and declaration
outcomes have deterministic success endpoints and disjoint success/rejection.
Their stronger exact contracts now unconditionally fix the constructor and
body ASTs, final remainders, and rejection endpoints. Complete declaration
exactness holds for each fixed supplied derive attribute, not across different
attributes. These laws are exposed by declarative and executable APIs.
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
validity contract. The same recursive family now has exact outcomes: every
successful derivation fixes the complete `TypeExpr` AST and final remainder,
and every rejection fixes its first failing endpoint, both at fixed fuel and
at the public fuel boundary. Exact composite theorems also expose recursive
type-list tails, complete delimited lists, optional named arguments, and
optional function returns without leaking parser state or fuel into the
grammar.

Transparent type aliases now reuse that recursive type grammar after an exact
`type` keyword, name, prioritized optional parameter list that may be empty and
may have a trailing comma, equals sign, and semicolon. Their public theorem
requires diagnostic freedom only to exclude the alias-RHS recovery branch; the
normal alias path and recursive type theorem do not otherwise need that
premise. Recursive type, shared generic-parameter, type-alias, and
enum-declaration theorem families have compile-time consumers and public
`Solcore.Syntax` registration. The full build and `lake test` pass with those
registrations.

The complete broad type-alias outcome is now exact. Its allow-empty,
allow-trailing optional parameter list fixes the complete optional identifier
list, final remainder, and committed rejection endpoint. Malformed RHS
recovery fixes its error type and final remainder and has one nonconsuming
rejection endpoint. Core `TypeExpr` exactness makes the recovery-aware alias
value contract unconditional, and the full `type`/name/parameters/`=`/value/
semicolon sequence consequently fixes the complete declaration AST and every
first failing endpoint. Executable reflection and dedicated/public consumers
expose these laws; diagnostics, failure payloads, and whole parser states
remain outside the claim.

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
strict `FunctionParameterParses` relation remains diagnostic-free. The broad
relation is also exact: fixed recovery-prefix spans determine the recovery
scan, complete recovery fixes its error parameter and remainder, and Core
`TypeExpr` exactness lifts through ordinary, `comptime`, missing-type, and
recovered parameter outcomes. Public executable reflection exposes unique
parameter AST/result and rejection-endpoint theorems.

The canonical `TypeExpr` and recovery-aware `namedParameter` outcomes now lift
to the `(` / `)` parameter list, with empty contents and a trailing comma
allowed. Delimiter and nested rejection endpoints are exact: recovery stops
leave an outer comma or right parenthesis unconsumed, a carrier hole remains a
nested rejection, and recovery to the window end may then yield exact
`delimiterMissing` rejection. The generic allow-empty trailing-list exactness
theorem now lifts those element outcomes to the complete parameter-list AST,
final remainder, and every delimiter or nested rejection endpoint. Strict
`FunctionParametersParses` remains the diagnostic-free list relation, while
the broad declarative and executable exact contracts are public and
compile-time consumed.

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
exclusive. Predicate ASTs, grouped and bare nonempty sequences, grouped-first
dispatch, and optional `where` values are now exact as well. Bare-tail value
uniqueness keeps the necessary shared preceding span explicit; complete
sequences discharge it and fix their AST, final remainder, and rejection
endpoint. Executable leaf APIs re-export the same result and endpoint laws.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable rejection reflects the exact nested
type or delimiter remainder. The successful endpoint is deterministic and
success/rejection are exclusive. Core `TypeExpr` exactness now lifts through
the complete optional clause, fixing the return AST, remainder, and committed
rejection endpoint.

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
diagnostic-free, location-policy judgment. All six component stages now have
exact child contracts, so the broad signature unconditionally fixes its
complete AST and final remainder and fixes every rejection endpoint. These
laws are reflected for every executable location and compile-time consumed.

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
Exact signatures and unconditional isolated `.allow` bodies now give complete
function-declaration AST and endpoint exactness without additional premises.
The earlier body- and statement-parameterized APIs remain available.

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
Exact parameters, modifiers, and isolated `.require` bodies now make constructor
ASTs, final remainders, and rejection endpoints unconditionally unique.

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
deterministic and exclusive; strict diagnostic-free `FallbackDeclParses`
remains. Exact parameters, validation, modifiers, and isolated `.require` bodies
now make the complete fallback AST and rejection-endpoint contract unconditional.

Implementation outcomes now cover the optional `default` prefix, contextual
marker, optional generics, trait name, required nonempty trailing-comma head
types, optional `where`, custom method body, and complete AST. The default
prefix cannot reject, and the pure nonempty refinement adds only an invariant
branch. The right-brace-first body loop retains positive `function` guards,
strict progress, forward method order, and exact unexpected or nested
rejection remainders. Full declarations expose six rejecting stages after the
default prefix: marker, generics, name, head arguments, `where`, and body.
Default, head, method, body, and declaration successful remainders are
deterministic, and success/rejection are exclusive; module diagnostics and
captured-body recovery remain successes.
The optional default marker and required head arguments now unconditionally
fix their ASTs and final remainders, with exact head rejection endpoints and
no default-marker rejection. Unconditional isolated `.allow` Core-body exactness
now also fixes complete method, body, and declaration ASTs, final remainders,
and rejection endpoints without further assumptions.

Trait methods now extend the broad module-signature outcome through an exact
semicolon, retaining diagnostic-producing signature successes and separating
signature from missing-semicolon rejection. Trait bodies reflect the custom
right-brace-first loop with positive `function` guards, strict progress,
forward method order, and exact unexpected, nested-method, and recursive
rejection remainders. Complete declarations distinguish contextual marker,
name, required generics, optional `where`, and body rejection. Method, body,
and declaration success endpoints are deterministic and success/rejection
exclusive. Exact signature and child contracts now also make all three levels
unconditionally fix their complete ASTs, final remainders, and rejection
endpoints, including the forward method list and closing/body spans. These
stronger laws concern declarative values and remainders, not diagnostic traces,
failure payloads, or whole parser states. The strict diagnostic-free
`TraitDeclParses` family and its source-validity compositions remain available
beside the publicly exported broad outcomes.

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
diagnostic reflection are registered for all four entry points. A single fuel
induction now proves unconditional AST and endpoint exactness for all three
mutually recursive term families. This covers lambda parameters and bodies,
maximal postfixes, operator precedence, tuple/pattern order, diagnosed statement
successes, prioritized transactional fallback, and recovery with fixed first
and last spans. Exact statements lift through raw block items, public blocks,
balanced capture/recovery isolation, and both tail policies, fixing complete
block ASTs, closing spans, final remainders, and external rejection endpoints.
Public executable APIs and consumers compare results with independently derived
grammar outcomes. The full build and tests pass; no diagnostic-free assumption,
diagnostic-trace equality, failure-payload equality, or whole-state equality is
required or claimed by these exactness laws.

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

Inline-Yul expressions, statements, and bodies now also have unconditional
exact AST and remainder contracts, including fixed-fuel and public recursive
boundaries. Expression names, literals, identifier/call selection, and
transactional argument rewind fix their successful values. Statement priority,
optional semicolons, switch/default selection, diagnosed empty switches, and
brace-delimited bodies preserve complete ASTs, forward order, and retained
spans. Recovery-scan exactness shares both accumulated endpoint spans.
Expression and statement rejection rewind to the input; body rejection fixes
its first-failing endpoint. Declarative and executable APIs and dedicated
consumers expose these laws, and the full build and test suite pass. Diagnostic
traces, failure payloads, and whole parser-state equality remain outside this
contract.

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
exclusive while preserving terminator recovery success. Stronger unconditional
contracts now fix complete import ASTs, successful remainders, and first
rejecting endpoints, including every alias, selected list, hiding clause, and
payload form. Terminator exactness shares the preceding span; payload exactness
shares the outer start. Selector operator parts are unique at a shared stopping
index, while the maximal scan and complete selector are unconditionally exact.
Public APIs and independent grammar-result consumers cover this full chain.

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
rejection. Successful endpoints are deterministic and success/rejection
exclusive. Stronger unconditional exactness now also fixes every complete
export AST and rejecting endpoint, from constructor/name selection through
local or remote payloads and the aggregate declaration. Supplied outer spans
remain shared explicitly where required.
The declarative and parser outcome packages are exported publicly and checked
by dedicated and public-boundary consumers. Their declaration-local guarantees
feed the broader top-item boundary described below.

Pragma item scanning and complete `pragmaDecl` now also have exact broad
ordinary outcomes. An immediate `;` gives an empty, nonconsuming item scan;
otherwise checked identifiers remain in forward order. Comma absence ends the
scan without consumption, while comma followed by `;` consumes only the
trailing comma. Complete pragmas compose exact `pragma`, a raw-identifier name
(which deliberately omits the checked-name hyphen diagnostic), the item scan,
and an exact semicolon. Rejection separates missing keyword,
rejected name, rejected items, and missing semicolon. Item-tail, item-list, and
declaration successful remainders are deterministic, and success is disjoint
from rejection. Unconditional exactness additionally fixes all item lists,
complete located declaration ASTs, and first rejecting endpoints. Production
tail consumers share the reverse prefix, retaining forward result order.
The public packages are compile-time consumed and feed the broader top-item
and file outcomes described below.

Dotted derive targets now have exact broad ordinary outcomes at the component,
recursive dotted-tail, and complete-target layers. Components retain both
checked identifiers and diagnosed reserved hard keywords; rejection records
that neither branch is available. Tail rejection preserves the consumed dot
and the exact first or later component failure. Successful remainders are
unique and success is disjoint from rejection at every layer. The stronger
exact outcome contract now also fixes each successful identifier/component
list/complete target AST and every rejecting remainder. Executable success and
rejection reflection expose these exactness laws publicly and are checked by
dedicated and umbrella consumers.

Complete derive attributes now also have exact broad ordinary outcomes. The
valid path records five rejection stages: hash, opening bracket, contextual
`derive` marker, no-trailing target list, and closing bracket. Recovery gives
current `]` first priority and consumes it as malformed recovery; otherwise it
stops without consumption at the window end, a top-item start, an
identifier-plus-colon contract field, `}`, or a missing carrier slot inside
the active window. Any other raw token advances the scan and updates its last
span. After exact `#[` consumption, that tail has no ordinary rejection. The
public transactional choice retries recovery from the original input after a
valid-path rejection, and a public rejection records rejection of both
attempts. Generic no-trailing lists now lift exact nested outcomes to a unique
complete list AST and rejecting remainder. Consequently the valid path, the
complete recovery path, and the public prioritized choice each fix the exact
successful attribute AST and final remainder as well as every rejecting
remainder. Recovery-tail value uniqueness is stated only for one fixed hash and
last-retained span, which is exactly what the complete recovery prefix proves.
Executable reflection exposes the public result and rejection-endpoint laws,
and dedicated and public-boundary consumers compile against them. These laws
concern declarative ASTs and remainders; they do not equate parser diagnostics,
failure payloads, or complete parser states.

Attribute-free `contractMemberCore` now has complete broad ordinary coverage for
its prioritized six-way dispatcher. Identifier-plus-colon field lookahead runs
first, followed by `function`, `constructor`, `fallback`, `type`, and contextual
`enum`; a selected branch never falls through after rejection. Success retains
the wrapped member AST, declaration span, empty leading comments, carrier,
window, cursor, and final remainder. Rejection records the selected leaf or an
exact nonconsuming unrecognized-member case. Successful remainders are
deterministic and success is disjoint from rejection. Its stronger AST and
endpoint contract is now unconditional: public Core expressions fix field
initializers, isolated `.allow`/`.require` bodies fix the three body-bearing
declarations, and type aliases and enums are independently exact. Existing
conditional APIs and strict member soundness remain available.

Contract-member derive attachment now has an exact pure relation for all seven
member variants, with one unique AST result for every input. Only enums retain
the attribute; the five other declaration variants keep their payload while
extending both their member and nested declaration spans, and the error variant
extends only its member span. Every branch preserves leading comments.
Executable attachment unconditionally reflects this transformation and leaves
the declarative remainder unchanged, including the non-enum branches that emit
`deriveOnlyEnum`; attachment itself therefore has no rejecting outcome.

The public derive-aware `contractMemberWithAttribute` boundary now has complete
broad ordinary success and rejection coverage. An absent hash selects the
attribute-free core directly. A present hash commits to the public derive
parser, then the core member parser, and finally the pure attachment above.
Rejection records exactly one of three first failing stages: plain core, derive,
or core after a successful derive. Successful remainders are deterministic and
success is disjoint from rejection. Exact attribute-free members and pure
attachment now make derive-aware member ASTs and rejection endpoints
unconditionally unique; the generic conditional lift remains available.

Standalone contract-member recovery now has exact broad outcomes. Success
consumes one mandatory token, scans to the window end, a recovery boundary, or
a missing carrier slot, and returns the exact error-member span without
consuming the boundary. Rejection records only an unavailable mandatory first
token. Successful remainders are deterministic and success is disjoint from
rejection. For fixed first and last retained spans the scan fixes its error AST;
the complete recovery path fixes those spans, the member AST, and final
remainder, while rejection has one exact nonconsuming endpoint. These stronger
laws are re-exported at the executable boundary and compile-time consumed.

The recovery-aware contract body now composes right-brace priority, direct
member progress, window-preserving rejection rewind, boundary-aware recovery,
forward member order, exact braces, and every first rejecting remainder. Broad
contract declarations then compose exact `contract`, name, optional generics,
and body stages with four matching rejection cases. Both layers have
deterministic successful remainders and disjoint success/rejection. Stronger
unconditional exactness now lifts from derive-aware members through the
recovery-aware body and complete declaration, fixing the full AST, final
remainder, and rejection endpoint. Core terms discharge the earlier shared
premises. The earlier conditional declarative and executable APIs remain
public and compile-time consumed. These
claims do not equate diagnostic traces, failure payloads, or whole parser
states.

Attribute-free top-item dispatch now has exact broad outcomes for import,
export, pragma, type alias, function, enum, trait, implementation, and contract
declarations in executable priority order, followed by an exact nonconsuming
unrecognized case. Pure top-item derive attachment covers all ten item variants:
enums retain the attribute, while every other item retains its payload and
extends the appropriate outer and nested spans. The public derive-aware
dispatcher records hash absence or commits to derive parsing, plain dispatch,
and attachment, with each first rejecting stage represented. Successful
remainders are deterministic and success is disjoint from rejection.

Top-item recovery and the complete file loop now also have exact broad
outcomes. Recovery consumes one mandatory malformed token, updates the last
span while scanning, and stops without consuming the next top-item boundary;
an unavailable first carrier is its only rejection. The file loop retains
source order without exposing its reverse accumulator, enforces direct-item
progress, rewinds a window-preserving item rejection, treats rejection at a
recognized item start as a nonconsuming diagnostic success, and otherwise
inserts the exact recovered error item. The complete `sourceFile` outcome keeps
the input source id, full-file span, pure comment attachment, comments, and
first rejection remainder exactly. These relations, executable reflection
packages, and outcome specifications are public and compile-time consumed.
Unlike strict diagnostic-free acceptance, the broad boundary-stop outcome does
not claim that every successful final cursor is at the window end.

Complete syntax exactness is now unconditional. Exact import and export leaves
close plain top-item dispatch; derive attachment closes the public dispatcher;
and recovery and comment attachment lift the contract through the file loop to
the complete parsed-file AST. Success fixes the full AST and declarative
remainder, and rejection fixes its endpoint, without recursive exactness or
diagnostic-free premises. Public `parseLexed` and `parse` results agree with
every independently derived public AST over the same file, tokens, and comments.
The public AST theorem does not invent a final cursor that `ParseOutput` does
not expose, or equate complete diagnostic traces and parser states.

Ordinary grammar completeness now pairs those uniqueness laws with soundness
and invariant-free execution. Independent success is equivalent to executable
success with the same AST and remainder; independent rejection is equivalent
to executable rejection at the same endpoint. Public Core types, expressions,
patterns, statements, lambda parameters, both raw/isolated block policies,
Yul expressions/statements/blocks, all top-level declarations, derive paths,
top-item dispatch, recovery, and the file loop have compile-time consumers.
Most internal boundaries require only a valid input state; pragmas and the
unconditionally total recovery/derive leaves need no such premise. File-loop
correspondence keeps the fixed forward prefix outside the grammar suffix and
discharges its fuel condition at the production boundary.

At `parseLexed`, a specified AST is returned exactly when the supplied lexical
carriers pass validation and the public grammar derives that AST. At `parse`,
the corresponding condition uses carriers produced by canonical lexing.
Neither direction requires diagnostic freedom or nesting clearance. This is
the recovery-aware syntax boundary, not a claim that every source is accepted
without diagnostics, nor an independent characterization of lexer payloads.
The public correspondence theorems depend only on the allowed standard axioms.

Validated carriers also have exactly one independently derived public AST, and
every such derivation satisfies recursive source provenance for its complete
Core syntax, top-level items, and comments. No executable parser reply is needed
as a caller premise. Contract-internal fields, plain/derive-aware members,
braced bodies, and standalone member recovery have matching completeness APIs.

The public nesting preflight now has its own parser-independent exact outcome
grammar. It classifies each token as conditional, group-open, block-open,
close, reset, or preserving; carries the exact delimiter and conditional scope
bases; and either clears the full token list or returns the first overflowing
span, dimension, and shared canonical limit. The executable checker is proved
equivalent in both the `none` and `some` directions, so the implementation and
declarative limit cannot drift.

Already-tokenized input validation now also has a parser-independent exact
outcome grammar. It checks source identity first, then the first invalid token
span, comment span, or lexical-diagnostic span in that priority order, retaining
the exact zero-based index and span. The scans and whole outcome are total and
functional, and declarative acceptance is equivalent to `LexedFile.ValidFor`.
The executable validators reflect those outcomes exactly. For every arbitrary
`LexedFile`, a public `parseLexed` error is precisely the mapped first
validation rejection; otherwise production parsing returns a broad public AST
outcome with exact retained lexical carriers and canonical output validity.

Broad successful `parseLexed` and `parse` syntax is now covered at the public
boundary as well. A nesting overflow returns the exact empty parsed file with
source id, full-file span, and retained comments. A clear nesting scan runs the
recovery-aware `SourceFileOrdinaryParses` relation from the exact root token
window while existentially hiding the final remainder that `ParseOutput` does
not expose. Both the direct token boundary and the complete source boundary
compose with the full canonical output-validity contract. The overflow branch
additionally fixes the entire `ParseOutput`: retained tokens, lexical
diagnostics, and the unsuppressed singleton nesting diagnostic. The normal
branch's complete parse-diagnostic trace is not yet claimed by this broad
relation because the current declarative remainder deliberately carries no
diagnostic accumulator. When nesting clears, a separate exact executable
witness exposes the successful underlying `sourceFile` reply, final state, and
the diagnostic-filter equation used to assemble the public output.

A first normal-branch diagnostic-trace slice is now exact independently of that
executable witness. Standalone top-item recovery appends exactly one recovery
event at the recovered AST span, while rejecting an unavailable first token
adds none. Independent trace rules preserve prior diagnostic order explicitly.
An independent lexical-cascade relation keeps or drops candidate spans in
input order, retaining duplicates and the existing same-source, LF-line,
overlap, inclusive endpoint, and horizontal-whitespace rules. Its interpretation
as top-item recovery diagnostics agrees with the executable filter both ways.

When all top-item starts are absent and one independent recovery reaches the
root-window end, these laws fix the complete `parseLexed` or `parse` output:
the comment-attached error AST, retained tokens and lexical diagnostics, and
the entire filtered parse-diagnostic list. Validation and nesting clearance
remain explicit, and canonical lexing supplies validation at the source boundary.

A recognized-start trace is also complete when `pragma` has no following raw
identifier. Independent current-input observations fix the exact found token
and failure span, including EOF and unavailable carrier slots, with source and
window-end byte supplied explicitly. Raw and checked identifier rejection add
no diagnostic themselves. The file boundary rewinds only the cursor, preserves
the failed attempt's diagnostics, and appends its unexpected report. This
missing-name prefix therefore fixes every public output field, including the
empty item list, retained comments and lexical carriers, and exact filtered
expectation diagnostic. Its public correspondence needs no assumed parser reply.
Other recognized-start failures, nested isolation, and arbitrary declaration
diagnostic traces remain outside these completed slices.

Identifier success now has an independent exact trace too. Raw names emit
nothing; checked names append exactly one located hyphen diagnostic when their
spelling contains `-`, even if it occurs repeatedly. The grammar fixes the full
name, token remainder, and added diagnostic suffix, with a bidirectional
executable correspondence and no input-validity or diagnostic-free premise.
Filtering also has a total, unique independent relation over arbitrary mixed
diagnostic lists, not only fixed-kind span lists. It preserves every retained
report's metadata and occurrence order; identifier, grammar-constraint, and
nesting diagnostics are protected even when their spans match lexical errors.
Exact hard-keyword, symbol, and contextual-word primitives now also have
bidirectional trace correspondence. A successful token step emits nothing;
rejection preserves the input and its existing diagnostics while fixing the
uncommitted report. Contextual words remain identifier tokens with contextual
expectations, not hard keywords. Protected identifier traces can be appended to
an independently filtered mixed prefix without losing either order or metadata.

These rules now cover successful complete pragma declarations. Only checked
items contribute diagnostic events, in written order; the raw pragma name and
punctuation are silent, and an accumulated item prefix is never diagnosed again.
Empty item lists and trailing commas are included. One independent pragma
derivation reaching the root-window end fixes every public output field,
including the comment-attached singleton AST and all protected item diagnostics.
No assumed declaration or item reply is needed at that public boundary.
Ground canonical-source proofs fix the raw-name/checked-item distinction,
multiple hyphens per item, trailing commas, same-line lexical errors with
protected item diagnostics, and retained/attached comments. Normalization is
also proved idempotent and compatible with concatenating independently filtered
traces, so repeated filtering cannot remove an already retained occurrence.

The same complete-output boundary now covers any finite sequence of successful
pragmas through the token-window end, including the empty sequence. Independent
grammar fixes the declaration list, final remainder, and concatenated protected
trace. Existing reverse item prefixes are restored once and are never diagnosed
again. Declaration count supplies a sufficient execution bound, and the usual
production bound is proved adequate. Public token/source theorems retain every
wrapped and comment-attached declaration in order; a proposed output diagnostic
list is correct exactly when it equals the complete independent trace.

Pragma rejection now has its own complete independent trace contract. Keyword,
raw-name, checked-item, and final-semicolon failures are distinguished in first
failure order. The grammar fixes the exact remainder, every uncommitted failure
field, and all events from completed checked items. Source-file and full-window
context are preserved without a validity assumption, including arbitrary prior
diagnostics and malformed windows. At the public boundary, a recognized initial
pragma stop produces no AST item, retains every lexical field and comment, and
normalizes the earlier item events followed by exactly one committed failure.
All earlier events are protected: only that final report can be suppressed.
Canonical regressions cover missing items, missing semicolons, same-line lexical
suppression, and ordered protected events across two successful declarations.

The recognized-stop contract also extends across any successful pragma prefix.
Independent grammar fixes the ordered retained declarations, the start of the
final rejected pragma, its complete report, and all preceding events. Production
execution rewinds only to that final start, retains earlier items, and appends
the final report once. Complete public outputs preserve comments and all lexical
fields, with exact mixed filtering. Canonical successful-then-rejected examples
retain the first AST and both hyphen events; a same-line lexical error suppresses
only the final expectation report, including its exact EOF byte position.

Balanced block isolation now has exact compositional diagnostic laws and an
independent conditional trace grammar. The child starts with an empty trace and
uses its captured closing-byte boundary; the parent resumes after that capture
with its original file, tokens, and full window. Child events follow parent
events, and only recovered ordinary rejection appends its report once. Invariants
remain invariants. Independent grammar erases to the existing ordinary isolation
outcomes and lifts inner AST/remainder/report/trace uniqueness. Explicit inner
success/rejection soundness and completeness contracts yield outer trace iff
theorems, including suffix existence for every execution and exact duplicate
order. These are lifting contracts, not a claim that all concrete Core block
traces have already been specified. Repeated isolation does not recommit a
failure already recovered by an inner wrapper.

Core block closing now has complete independent tail-validation traces. Every
non-final unterminated expression emits one constraint at its full statement
span; only the final expression is exempt under `allow`. These traces are total,
unique, ordered, and protected from lexical suppression. An empty trace is
equivalent to the existing tail-validity predicate. Exact right-brace recognition,
the source-order body, remainder, and complete appended trace characterize
successful closing. A missing brace rejects before any tail validation and
preserves the whole input, with an exact uncommitted failure. Mixed filtering
acts on preceding diagnostics while retaining the full validation suffix.
The existing parser behavior is unchanged; a small proof-only seam exposes
the private validator's diagnostic effect.

Raw Core blocks now have independent successful and rejecting trace grammars,
with exact braces, branch priority, AST order, remainders, and full reports.
Success concatenates all statement events before the single whole-body tail
validation pass. Rejection retains earlier statement events without performing
that validation. Statement trace soundness/completeness and source/full-window
preservation lift to raw success/rejection iff theorems, including sufficient
production fuel, arbitrary prior diagnostics, and fixed complete failures.
These contracts also compose through balanced isolation: successful raw traces
are retained, and recovered raw rejection appends one report at the parent
resume point. Independent statement outcome exactness supplies joint raw and
isolated block exactness; no totality claim is inferred from uniqueness alone.
Normalization keeps the entire delayed validation suffix after filtering earlier
statement events. Concrete general statement trace contracts remain separate.

A test-only checked-identifier statement adapter exercises these contracts on
nonempty hand-constructed token carriers. Two hyphenated names emit both name
events before either delayed termination event; allowing the final expression
removes only its termination event. Rejection after the first name emits no
termination event, and isolation commits the unexpected-token report once while
restoring the parent window and leaving the next token untouched. These examples
do not claim a Core statement grammar or canonical-lexer correspondence.

The real Core `break` and `continue` leaves now have unconditional independent
diagnostic traces, with success/rejection correspondence, complete failure
records, and all five statement execution contracts. Success changes only the
cursor by two tokens and is silent; rejection is also silent and selects the
missing keyword before the missing semicolon. Independent outcome existence,
uniqueness, and disjointness cover arbitrary carriers, including exhausted
windows and missing array slots. These leaf laws instantiate raw and isolated
restricted-block exactness without abstract statement assumptions. Concrete
token-carrier consumers exercise two-statement success and later-semicolon
rejection under both tail policies, retaining arbitrary prior events and the
post-recovery parent window and following token. Two canonical source fixtures
also connect actual lexing to break-pair success and break/continue rejection
priority, including recovered parent continuation. Their lexer results are
kernel checked; parser outcomes follow the independent trace proofs. General
statement and whole-file traces remain separate.

Return statements now have independent optional-value and full-statement
success/rejection traces. A current semicolon selects no value without invoking
the expression parser. Otherwise the expression's AST, complete event order,
and first rejection report are preserved; a later missing semicolon keeps the
successful expression's events and its own report remains uncommitted.
Expression trace contracts lift to all five return statement contracts and
exact execution iff theorems, including the full failure record and arbitrary
prior events. Successful trace correspondence needs no expression context
assumption; source/full-window preservation is explicit for the frame and final
semicolon-failure report. The empty `return;` execution is unconditional and
changes only the cursor by two tokens. Independent expression exactness and
existence are separate assumptions: the former lifts to return and restricted
raw/isolated block exactness, while the latter supplies return outcome existence.
General expression trace contracts are still abstract at this boundary.

Core literal and Boolean primitives now have unconditional exact silent
success/rejection traces. Decimal, hexadecimal, and string spellings are retained
verbatim; Boolean keywords retain the existing identifier-shaped AST. Success
changes only the cursor by one token; rejection retains the whole input state
and fixes the complete failure, including the distinct literal versus expression
expectations. Independent existence, uniqueness, and disjointness cover arbitrary
carriers and windows. The actual literal-expression leaf supplies all five
expression execution contracts and both independent expression laws, discharging
the abstract assumptions for empty/one-literal returns and restricted raw/isolated
return block exactness. General expressions are not implied by this leaf result.

Concrete consumers now connect canonical lexing to `return 42;` and the exact
window-end semicolon failure for `return 42`. Empty `return;` bypasses an arbitrary
expression parser. A separate explicit-token block mixes literal and empty
returns under both tail policies and proves raw/isolated success with arbitrary
prior diagnostics, restored parent context, and an unread following token.

Raw block statements now have independent traces and all five execution
contracts under explicit inner statement laws. They wrap `coreBlock .require`:
the successful AST is mapped to a block statement with the same output state,
and rejection propagates the complete failure and state without committing a
report or performing isolation. Erasure, progress, token-window laws, and joint
exactness compose from the raw block relations. Successful file/full-window
preservation is proved from the inner frame alone, including delayed validation;
the parser file adds only a proof exposing its existing validator frame.

Expression names and the real identifier-expression leaf now have unconditional
exact traces. Boolean keywords take priority and remain silent identifier-shaped
values; ordinary identifiers retain the checked spelling event when they contain
hyphens. Independent ordinary erasure, output shape, uniqueness, disjointness,
and outcome existence match the executable branch order. Successful execution
fixes the entire state: one token is consumed and the fresh trace is appended
to existing diagnostics. Rejection preserves the whole input and reports the
identifier expectation after both Boolean guards fail. The identifier-expression
leaf supplies all five expression contracts and independent expression laws,
including concrete nonempty returns that retain a single hyphen event.

Protected event traces now compose through optional return values, returns,
raw block items/blocks, and block statements on both success and rejection.
Checked-name events and delayed termination constraints survive arbitrary
lexical cascade filtering with all metadata, order, and duplicates intact.
Executable filter consumers show that prior diagnostics may be normalized while
the complete fresh suffix remains unchanged, including nested return blocks.
Uncommitted failure reports are kept separate, and reports appended by isolated
recovery are deliberately not presumed protected.

Concrete two-level break-block consumers verify nested AST order and spans,
direct propagation of an inner semicolon failure without skipping closing
braces, and one-report recovery only when isolation is applied to the outer
block. Checked-name return blocks have canonical lexer fixtures for successful
two-name events and later semicolon failure, with exact raw/recovered diagnostic
order, restored parent contexts, and unread following tokens. These remain
restricted statement/leaf instances rather than general expression/file traces.

Generic no-trailing lists now have independent successful and rejecting traces
for either empty-list policy. Child contracts give exact AST/remainder/report
and complete appended-event correspondence, with arbitrary prior diagnostics
and reverse element prefixes. Successful children preserve source and the full
active window; token-carrier preservation is separate and needed only when
erasing whole-list success to the older ordinary grammar. Completeness uses
the actual production fuel measured immediately after the opening delimiter.
Commas take priority over closing symbols, even when both symbols are comma;
after a comma the child runs directly without a closing-absence guard. Missing
delimiters report comma then closing, retaining duplicate expectations. Joint
independent exactness and protected-suffix normalization compose from child
laws without asserting child totality or general expression trace completion.

Array-literal wrappers lift these list laws to all five expression trace
contracts and exact success/rejection/full-failure correspondence. Mapping
changes only the AST, preserving the full output state and uncommitted failure.
Independent structure, joint exactness, and protected-event laws compose under
explicit child assumptions. Concrete identifier and literal children cover
two checked names, empty arrays, numeric arrays, later-child rejection, missing
delimiters, and a trailing comma rejected by the identifier child. Four canonical
lexer fixtures connect directly through initial parser states to actual array
outcomes, with exact spans, ordered diagnostics, and unread following tokens.
These wrappers do not yet supply the general recursive expression contracts.

Checked-name arrays also compose through actual return-only raw and isolated
blocks. Canonical source examples connect directly to both successful execution
and exact child-failure propagation; only outer isolation commits that report
once, recovers an empty body, and restores the parent window and unread tail.
Independent restricted block exactness and raw protected-suffix normalization
use the concrete child laws, with no general expression assumptions.

Leading-dot constructors and their optional argument lists now have independent
successful and rejecting traces, conditional execution contracts, and exact
AST/remainder/report/event correspondence. Boolean-first checked-name events
precede argument events; absent arguments leave the entire state unchanged,
while written empty parentheses remain a present empty list. No-argument and
empty-list consumers require no child contract. Raw dot invocation also covers
missing-dot rejection; erasure into the older dispatcher-selected rejection
grammar explicitly separates that case. Dot/name/argument failures remain
uncommitted, and protected name/argument suffixes retain all metadata and order.
Joint independent exactness requires only child uniqueness and disjointness,
not outcome existence or concrete recursive expression execution.

Canonical constructor fixtures connect actual lexing and initial states to a
three-name successful trace and a two-name prefix before argument rejection.
They retain the separate dot/name/list spans, full parent window, unread tail,
and uncommitted identifier failure with arbitrary incoming diagnostics.

Parenthesized expressions and their comma tails now have independent success
and raw rejection traces, conditional sound/complete correspondence, and joint
uniqueness/disjointness. Empty parentheses form an empty tuple; a singleton
remains a group even with a trailing comma, while larger tuples preserve source
order. Immediate closing bypasses any child and is silent. After a successful
child without a following comma, a failed close expects only `)`, not the generic
comma/closing pair. Raw missing-opening and missing-comma failures are separated
from the older selected ordinary grammar. The tail uses the actual production
fuel after the first child, retains arbitrary reverse prefixes and prior events,
and needs successful child file/full-window preservation, not input validity.
Protected child traces survive normalization; the final report is uncommitted.
Canonical checked-name fixtures verify empty/group/tuple ASTs and two closing
failures, including exact spans, remaining tokens, windows, and ordered events.
These are concrete restricted-child consumers, not general recursive-expression
or mixed-file trace completeness.

Proxy expressions now have independent success/raw-rejection traces and exact
execution correspondences under explicit contracts for the real type parser.
The silent `@` marker retains its own span while the full type AST and every
child event are propagated unchanged. Missing-marker rejection keeps the whole
input state and is separated from selected ordinary erasure; type rejection
retains its complete failure and returned state without committing its report.
Independent joint exactness and protected-suffix laws remain conditional on
type properties. Canonical `@a-b tail` and `@+ tail` consumers independently
execute the real simple-name and rejecting type paths, fixing the hyphen event
or type-specific failure, full windows, cursors, and unread tokens. They do not
establish general recursive type diagnostic contracts or full-file traces.

Named-type finishing now has an unconditional independent diagnostic trace:
exactly an unqualified `mapping` spelling emits the canonical-form constraint,
with a span covering any supplied type arguments. Qualified and other spellings
are silent. Execution always succeeds and changes only the appended events;
the entire type AST, input carrier/window/cursor, prior reports, and duplicates
are exact. Constraint events survive normalization. This finishing-only result
is one compositional stage; recursive type traces remain separate.

Optional lambda return annotations now have independent exact success/rejection
traces under real type-parser contracts. Arrow absence returns `none` with the
whole state unchanged and cannot reject; a present arrow silently forwards the
type AST or complete failure and all child events. The raw missing-arrow case
is therefore not a rejection rule. Structural erasure, joint exactness, and
protected-suffix normalization are separated from child progress/window laws.
Consumers keep duplicate events and failed child states exactly; they remain
conditional, not complete traces for lambda parameters, bodies, or full lambdas.

Qualified names now have unconditional independent success/rejection traces,
five generic execution contracts, and exact complete output-state laws. Every
checked component contributes its spelling event in source order; dots are
silent and absence of the next dot ends the maximal name. A selected dot with
no following identifier rejects at that position, retaining earlier events and
the complete context-specific failure without committing it. Raw tail laws
support arbitrary first/last/reversed prefixes and adequate or production fuel;
the full parser uses its actual post-first-name fuel. No input-validity premise
is needed. Independent joint exactness and protected normalization are public.
Canonical three-name success and two-name-prefix rejection fix all spans,
carriers, windows, cursors, and following tokens in every context and phase.
These close the name component, not argument-list or recursive type traces.

Generic trailing-enabled lists now have independent success/rejection traces
and five execution contracts under explicit child contracts. Commas retain
priority over closing delimiters, including a comma-valued closing symbol;
an immediate post-comma close bypasses the child entirely. Both empty policies,
strict child progress, arbitrary reverse prefixes/prior events, and the actual
post-opening production fuel are exact. Successful child file/full-window
preservation suffices for execution; separate carrier laws support ordinary
erasure. Joint exactness asserts uniqueness/disjointness, not existence.
Canonical checked-name lists cover trailing success, child failure after a
comma, and the distinct ordered comma/closing report when neither is present.
Protected fresh events survive normalization with order and multiplicity intact;
final rejection reports remain uncommitted. This generic boundary does not yet
close real type-argument, lambda-parameter, or recursive expression traces.

Optional named-type arguments now compose the nonempty trailing-enabled list
into independent exact success/rejection traces under nested type contracts.
Absent `<` returns `none` with the entire state unchanged, bypassing every
child. Present arguments retain their complete nonempty carrier and span;
the silent `requireNonempty` conversion cannot fail its defensive invariant
after successful nonempty parsing. Rejection requires positive `<` lookahead
and forwards the complete list failure/state without committing its report.
Independent erasure, uniqueness/disjointness, and protected suffix laws remain
separate from execution and child carrier preservation. Canonical consumers
use the real `typeExpr` child for `<a-b,> tail` and `<a-b,+> tail`, preserving
the prior events, checked-name event, complete state, and unconsumed tail.
These are concrete examples, not general recursive type trace contracts.

Raw named types now compose exact qualified-name, optional-argument, and
finishing traces in that order, with five execution contracts under nested
type contracts. Successful ASTs and all spans are fixed; name/argument failures
retain the exact uncommitted failure and earlier events, without running the
finishing stage. Independent success erases componentwise, while rejection
erases to the existing raw named-type rejection; neither silently assumes the
type dispatcher's priority guards. Joint exactness and protected normalization
are public. Consumers fix arbitrary argument states and events before the
mapping constraint, bypass every nested child when arguments are absent, and
verify canonical `mapping tail` success versus `mapping<+> tail` rejection
with a real type child. The latter emits no premature mapping constraint.
Prior reports, complete states, and unconsumed tokens are retained. General
recursive type traces and prioritized type dispatch still remain separate.

Raw `mapping(key => value)` types now have independent exact success/rejection
traces and five execution contracts under recursive child contracts. The
contextual marker is the actual identifier token, and key events precede value
events. Every AST span and each first failure at marker/open/key/arrow/value/close
is fixed, including the expected contextual marker or single punctuation and
the complete uncommitted report. Raw missing-marker/opening cases stay separate
from the older selected mapping rejection. No child progress is assumed: this
straight-line parser accepts successful non-advancing children, unlike list
loops. Ordinary carrier laws remain separate from runtime source/window framing.
Joint exactness and protected suffixes are public. Canonical real-type-child
success and closing failure retain both checked-name events, full output states,
and following tokens. A reusable positive-fuel checked-name leaf helper supplies
these concrete children without asserting general recursive type contracts.

Raw proxy types `@T` now have independent exact success/rejection traces and
five execution contracts. Success and rejection forwarding require only the
corresponding child contracts, with successful source/window framing proved
separately. The marker and complete proxy AST spans, child state, events, and
uncommitted failure are exact; a missing marker bypasses every child on the
unchanged state. Raw marker failure remains separate from selected ordinary
rejection. Joint uniqueness/disjointness and protected ordered suffixes are
public. Canonical `@a-b tail` and `@+ tail` consumers use the real type child and
verify complete states and unconsumed tails. These type results are distinct
from proxy-expression traces and do not complete general recursive type traces.

Raw `comptime<T>` types now retain the contextual identifier marker, inner AST,
angle and outer spans, and exact nested events under child trace contracts.
All four first failures (marker/opening/child/closing) have exact uncommitted
reports; raw prefix failures remain distinct from selected ordinary rejection.
Success forwarding needs no child frame, while a closing report uses the
successful child's source/full-window frame. Joint uniqueness/disjointness and
protected suffixes are public. Canonical real-type-child success and closing
failure preserve the whole state, remainder, prior events, and following tokens;
raw prefix failures bypass every child.

Raw tuple-type traces now reuse trailing-enabled lists with empty-list priority,
strict child progress, and exact production fuel. Every list arity remains a
tuple type, including `()` and `(a-b,)`; no expression-group reinterpretation
is introduced. Five execution contracts, independent ordinary erasure with
separate carrier laws, joint uniqueness/disjointness, protected suffixes, and
raw/selected rejection separation are public. Canonical real-type-child empty,
singleton, two-element, and missing-separator cases fix the full AST/state,
checked-name event order, and ordered comma/right-paren expectation. These two
raw type slices do not complete recursive type or prioritized dispatch traces.

Optional function-type `returns(...)` clauses now have independent exact
success/rejection traces and five contracts under nested type contracts. An
absent contextual identifier succeeds with `none` on the unchanged whole state;
a present marker delegates to the empty-allowed trailing list, including raw
opening failure. Exact list ASTs, spans, emitted events, and uncommitted failures
are retained. Joint uniqueness/disjointness and protected ordered suffixes are
public. Canonical empty returns bypass every possible child; real-type-child
singleton success and separator failure retain full states and following tokens.
This optional clause does not itself complete function-type or recursive traces.

Raw function types now compose the keyword, parameter list, and optional
returns with exact parameter-before-return diagnostic order. The complete AST
uses the returns-list end span when present and the parameter-list end span
otherwise. Five contracts, exact component success/failure equivalences,
independent ordinary erasure, joint uniqueness/disjointness, and protected
suffixes are public under nested contracts. Raw missing-keyword failure stays
separate from selected ordinary rejection. Canonical real-type-child success
and return-list failure retain both checked-name events, complete states, and
following tokens; missing keywords and absent returns preserve their exact
component states. Reusable checked-type singleton-list helpers supply these
concrete executions without general recursive diagnostic-trace assumptions.

Every successful recursive type parse now unconditionally preserves its full
source file and active window, both at arbitrary explicit fuel and at the
actual production bound. This composes the six raw type frames without
`ValidFor`, carrier-validity, or diagnostic-silence assumptions. Consumers combine
the frame with existing token preservation and execute a deliberately invalid
carrier/window fixture. The frame is not a general recursive trace correspondence;
prioritized trace dispatch and recursive success/rejection composition remain
separate obligations.

One prioritized type-dispatch trace layer now composes all six raw forms and
the final expected-type rejection. Independent selection records every earlier
absence and the exact positive marker or two-token contextual prefix. Raw
prefix failures cannot masquerade as selected failures; named ordinary erasure
receives the comptime/mapping exclusions. Joint uniqueness/disjointness,
carrier-preserving erasure, and protected suffixes are public. Actual positive
fuel has five compositional contracts and success/rejection/full-failure
equivalences under the preceding parser's trace contracts; its source/window
frame is supplied unconditionally. Consumers distinguish keyword tokens from
same-spelling identifiers, bare/mismatched contextual names from special forms,
and hidden backing-array tokens from visible window tokens. Final failure keeps
the whole state and reports the active-window EOF span without emitting an
event. This is one-layer correspondence, not general recursive production
trace completion or an assertion that every input has an ordinary outcome.

Child-relation implication now lifts through trailing lists, all raw type
forms, and the prioritized dispatcher. These monotonicity laws preserve every
indexed AST, token carrier, window, cursor, diagnostic event, and failure report;
they neither add outcomes nor reorder or deduplicate events. Public consumers
forget auxiliary child protection annotations while retaining exact events and
protected normalization. This is infrastructure for recursive trace proofs,
not a recursive completeness or outcome-existence result.

A generic bridge now derives trace completeness from both execution soundness
laws, independent uniqueness/disjointness, and explicit exclusion of invariant
failure. Pointwise and unrestricted versions impose no hidden state-validity or
frame premise. The actual checked-name leaf consumes all four bridges with
arbitrary prior diagnostics. Formal countermodels show why soundness plus joint
exactness cannot replace invariant exclusion, and why even both completeness
contracts can be vacuous rather than assert an ordinary outcome's existence.

General recursive type execution now has unconditional success and rejection
trace soundness, both at explicit resource bounds and at the production parser.
The independent specification is the least closed relation of the selected
type layer, with simultaneous success/rejection queries and exact roll/unroll
and induction laws. It contains no executable parser or resource parameter.
Successful traces erase to ordinary types and preserve the token carrier and
active end index. Both outcomes preserve protected, ordered, duplicate-retaining
events after arbitrary earlier diagnostics; the final rejection report remains
separate. Public consumers use these recursive contracts without child premises
or state validity. Soundness alone does not imply completeness or ordinary
outcome existence.

Canonical public-parser consumers now cover the three-level nested success
`@comptime<a-b> tail` and missing-closing rejection `@comptime<a-b +> tail`.
Constructive component execution and recursive soundness retain the exact
single hyphen event after arbitrary prior diagnostics, complete AST spans and
states, active windows, and untouched following tokens. Rejection reports only
the missing greater symbol and does not commit that report as an event.

Independent recursive type outcomes now have unconditional AST/remainder/event
uniqueness, rejection remainder/report/event uniqueness, and success/rejection
disjointness. A pairwise agreement contract compares distinct child relations
through trailing lists, all raw forms, and the selected dispatcher. Simultaneous
strong induction compares an annotated left derivation with an arbitrary right
derivation, without assuming recursive uniqueness as a premise. Actual-reply
consumers fix every independently claimed event and rule out an opposite
outcome. Pointwise reverse correspondence isolates invariant exclusion as an
explicit premise; the joint specification itself still asserts only uniqueness
and disjointness.

That execution premise is now discharged on arbitrary states. A minimal child
resource contract requires only ordinary execution below its bound, successful
end-index preservation, and strict cursor progress. Actual opening/comma tokens
pay for decreasing bounds before nested execution, so no source, token-carrier,
diagnostic, rejected-state, or global-validity premise is needed. The generic
list loops and all raw type forms compose into unrestricted production totality.
Recursive types consequently have all five diagnostic-trace contracts and
success/rejection/full-Failure equivalences with arbitrary prior diagnostics,
including noncanonical token windows. This is complete type-trace correspondence,
not general expression, statement, or whole-file diagnostic-trace completion.

Separate execution-derived existence theorems provide an actual traced ordinary
reply for every State and a success or rejection derivation for every independent
remainder/source/endByte. They use unrestricted totality plus soundness, not
joint exactness. Reverse-correspondence consumers include foreign reversed token
spans, empty source text, oversized windows, missing backing tokens, and cursors
past the active window, while retaining arbitrary prior events and full
State/Failure results. A synthetic-child list consumer independently verifies
the minimal resource contract: changing source, tokens, endByte, and diagnostics
and overshooting endIndex still permits ordinary execution. That synthetic
contract is not a diagnostic-preservation contract.

Recursive type trace equivalences now reconstruct the complete success and
rejection State. Source preservation is proved separately for primitives,
delimiter loops, raw types, and all recursive bounds without input validity.
Reconstruction retains the independent remainder's tokens, endIndex, and cursor,
the original source/endByte, and exactly the appended diagnostic suffix.
Nested reverse consumers retain full Failure values and following tokens;
separate counterexamples rule out forgetting tokens or endIndex in cursor-only
state updates.

Raw proxy expressions and optional lambda return annotations now instantiate
the concrete unrestricted type contracts. Their five execution contracts,
success/rejection/full-Failure equivalences, independent joint exactness, and
protected suffixes no longer require caller-supplied child contracts. Consumers
start from independent type derivations and preserve arbitrary earlier events.
These are two type-bearing components, not complete expression or lambda traces.

Typed and error parameter finishers now have independent event judgments with
existence, uniqueness, and cascade protection. Exact execution fixes their full
AST and State: only an outer comptime type adds its type-span constraint;
proxy-of-comptime remains silent. Finishing never replays earlier name/type
events, and duplicate constraints retain their order. Both missing-type error
constraints retain their specified spans. These are finishing-only components;
full parameter composition remains separate from these finishing leaves.

Named-parameter tails now compose those finishers with the actual recursive
type parser. Independent success and rejection judgments have unique, disjoint
outcomes and protected events. All five execution contracts, whole-State and
full-Failure equivalences, and ordinary execution hold on arbitrary inputs.
An absent colon produces an error-valued success without advancing; a present
colon runs the type before finishing, and a type rejection skips finishing.
Constructive reverse consumers retain nested comptime/name events in order,
duplicate earlier constraints, exact spans and windows, and untouched following
tokens. Terminal type-failure reports remain uncommitted. This is the raw tail,
not itself selected parameter-core or public recovery trace completion.

Ordinary parameter-name checking now has an independent finishing trace and
a checked-prefix composition that retains identifier-before-warning order.
Whole-Reply continuation laws preserve all earlier events without replay or
deduplication. The same exact contextual-name pair guard is reflected for both
function and lambda cores, including active-window limits and missing backing
tokens. Separate source laws cover all raw function/lambda parameter helpers
and cores, not public recovery. Consumers verify window-dependent selection,
duplicate warnings, and the absence of an ordinary-name warning after a
selected comptime marker. Guard reflection remains separate from a full core
trace contract.

Both raw named-parameter paths now have unconditional five trace contracts,
independent exactness/protection, ordinary execution, and complete State/Failure
equivalences. Ordinary names run their spelling check before the tail, while
names after a comptime marker receive identifier checking only. Every raw
first-failure stage is represented. Reverse consumers distinguish the raw paths
on the same input and retain name-before-type-before-finishing events.

The selected non-recovering function-parameter core now has the same complete
trace correspondence on arbitrary states. Explicit pair guards exclude the
raw comptime marker/name failures when that branch is selected. Independent
joint exactness is distinct from execution-derived outcome existence, which is
also provided for every State and independent remainder. Consumers reconstruct
whole replies, preserve arbitrary earlier events through lexical filtering,
and verify that diagnosed ordinary success wins over a bypassed raw failure.
Public named-parameter and lambda-parameter rewind/recovery are composed below;
whole-file traces remain a separate obligation.

Lambda-parameter tails now have unconditional five trace contracts and exact
whole-State/full-Failure correspondence. Typed paths preserve the named-tail
trace while retagging its complete AST. Missing colons infer ordinary names
silently but produce a covered missing-type error for comptime names. Reverse
consumers preserve earlier duplicates and forward child rejection unchanged;
these are tail contracts, not full lambda-parameter or expression completion.

Standalone function-parameter recovery now has unconditional exact traces and
whole-State/full-Failure equivalences. It consumes a mandatory first token before
checking later comma/right-paren stops. Missing backing ends an established scan
but rejects an initial recovery attempt, even inside the numeric window. Only
one recovery event is appended; an earlier committed report is not re-emitted.
Recovery events are lexical-cascade candidates, with separate explicit keep/drop
conditions, not unconditional protected events. Public named rewind composition
is covered separately below.

The public named-parameter parser now has unconditional five trace contracts,
complete State/Failure equivalences, and separate execution-derived outcome
existence on every State and independent remainder. Its independent judgment
preserves the failed carrier and end index while rewinding only the cursor.
Boundary rejection commits no terminal report; otherwise the original report is
committed once before recovery. A recovery rejection retains its distinct,
uncommitted terminal report even when its payload equals the committed original.
Reverse consumers check cursor rewind, unchanged prior duplicates, no repeated
identifier checks while skipping, and protected name events through conditional
filtering of the committed report and recovery event. This completes the public
named-parameter slice, not general expressions or file traces; lambda parameters
are handled separately below.

Both raw lambda-parameter paths and their selected non-recovering core now have
unconditional five trace contracts and exact whole-State/Failure equivalences.
Explicit pair guards select ordinary inference, typed parameters, or marked
missing-type error success without admitting bypassed raw failures. The core has
separate actual and independent outcome existence on arbitrary inputs. Reverse
consumers reconstruct nested name/type/finishing events, silence after a second
comptime name, exact missing-type covers, and full child failure; arbitrary
earlier events and protected core suffixes are retained. Public lambda rewind
and recovery are handled below; lambda expressions remain a separate composition.

Standalone lambda recovery now inherits exact function-recovery traces, changing
only the recovered error AST's carrier. It has unconditional five contracts,
whole-State/Failure equivalences, independent joint exactness, and conditional
recovery-event filtering. Reverse consumers reuse the function fixtures for
mandatory consumption, later delimiter stops, missing backing, and prior reports.

The public lambda-parameter parser now also has unconditional five contracts,
exact whole-State/Failure equivalences, and separate actual/independent trace
existence. Its cursor-only rewind, boundary report policy, and one original-report
commitment match the independent specification without validity assumptions.
Reverse consumers preserve prior duplicates and mixed diagnostic filtering;
ordinary inference and marked missing-type error success explicitly bypass
recovery. Both public parameter slices are complete at this trace boundary.
Parameter lists are composed below; lambda expressions, general recursive
expressions, and whole-file traces remain separate obligations.

The actual function-parameter list and inline lambda-parameter list now have
unconditional five trace contracts, complete State/Failure equivalences, and
independent joint exactness. Production totality uses the public parameter's
strict progress and successful end-index frame, with no validity requirement;
separate totality and soundness prove trace existence for every State and
independent remainder. Both lists allow empty input lists and a trailing comma,
and retain all child recovery events. The lambda law targets the existing inline
parser rather than adding a new runtime helper. These list results do not assert
unconditional cascade protection, signature traces, or complete lambda expressions.

Independent reverse consumers now cover both actual lists on shared token
carriers: empty, single and optional-trailing-comma success, comma-first
`[comma, rightParen]` delimiter failure, first-child boundary rejection, and
recovered children with arbitrary duplicate prior diagnostics. The same untyped
name is erroneous for a function but inferred for a lambda; the exact AST,
remaining semicolon, complete Failure, and ordered event suffix are checked.
Separate consumers retain outcome existence on a numerically invalid window.

Raw lambda-expression traces now compose the concrete recovering parameter list,
optional recursive return type, and an explicitly supplied body relation. The
five contracts require only the corresponding body contracts; success and reject
soundness/completeness do not require a body frame. Whole-State equivalences state
successful or rejected body file/window preservation separately. Independent
joint exactness requires the body's joint specification, while separate trace
existence uses body ordinary execution and its two soundness laws, not completeness
or joint exactness. All four first failures preserve complete terminal reports,
and pointwise laws show early failures bypass any body parser. Parameter and body
events are filtered explicitly around the protected return-type events. This is
a raw, body-conditional composition, not a complete recursive expression parser
or an atom-dispatch result. Concrete `lam(+) -> a-b {}` consumers retain parameter
recovery reports/events before the return-name warning and supplied body events,
including arbitrary prior diagnostics and complete body Failure/State forwarding.
Marker, hidden list-opening, and return-type failures bypass any body parser;
mixed filters explicitly suppress recovery events while retaining the return
warning. A real empty Core block bypasses any supplied statement parser and
leaves the following semicolon unread; general nonempty body behavior stays
explicitly conditional.

Expression-atom lookahead now has a separate independent eight-way selection
judgment, including the final fallback. Every later branch retains all earlier
failed guards. Selection exists uniquely on arbitrary token remainders, and
equal current-token observations suffice even across different carriers and
cursor positions. The actual core has exactly the selected raw parser's whole
Reply with no recursive-child contract. Concrete consumers cover all branches,
Boolean keywords versus identifiers, hidden/missing backing, invalid windows,
unselected child independence, and the final uncommitted expression report.
These are dispatch-selection laws, not recursive trace outcome existence.

One selected atom-core layer now has independent success/rejection traces and
all five execution contracts over explicit nested-expression and body relations.
Literal/name leaves, proxy types, lambda parameters, and return types use their
concrete contracts. Nested collection traces require successful child file/window
frames; a final lambda body needs only its corresponding soundness/completeness
law. No rejection frame, progress, validity, or ordinary premise is needed for
these four trace laws. Suffix and full-Failure equivalences retain all ordered
events; successful whole-State reconstruction adds the body success context,
while rejected reconstruction states only a core file/end-byte frame and permits
the returned token carrier/endIndex to differ. Independent exactness assumes
nested/body joint exactness. Neither these contracts nor uniqueness establishes
recursive production totality or trace outcome existence.

Separate raw-collection, lambda, and selected-core rejection context laws now
preserve the file and an explicitly chosen window observation. The whole-window
and end-byte-only specializations require corresponding rejected-child frames
and the nested expression's success context, but no body success, token-carrier,
progress, validity, or ordinary contract. The weaker law permits rejected children
to change both token arrays and end indices without preventing exact State
reconstruction or later cursor-only rewind.

Standalone expression-atom recovery now has unconditional five trace contracts,
independent joint exactness, source/full-window frames, and complete State/Failure
equivalences. It consumes a mandatory first token, follows the existing boundary
scan, and emits exactly one recovered-expression event at the error AST's span.
An unavailable initial token rejects without committing its report; missing
backing after consumption terminates the scan successfully. Recovery-event
filtering is explicitly conditional. Caller report commitment and the public
atom's rewind/recovery composition are covered separately below under explicit
core contracts.

Independent recovery consumers now reconstruct exact replies for initial
semicolon/else consumption, subsequent else/semicolon stopping, skipped
hyphenated identifiers without replayed checks, initial missing-backing rejection
versus established-scan success, and hidden first/following tokens. They retain
arbitrary prior and duplicate events, leave the stopping token unread, and show
both concrete lexical-filter retention and removal of the recovery event.

The public atom wrapper now has independent core-or-recovered success and
boundary-or-recovery rejection traces over explicit core relations. Runtime
soundness/completeness and complete State/Failure equivalences require the
matching core contracts and rejected file/end-byte frame, not unchanged token
arrays or end indices. Successful State reconstruction additionally uses the
core's successful file/end-byte frame. Only the cursor is rewound; the original
report is committed exactly once on the non-boundary path, and the recovery
terminal report remains separate. Full-window context is a stronger, separately
stated law. Independent joint exactness is conditional on core exactness;
non-vacuous State/remainder outcome existence separately requires core ordinary
execution and soundness. This is a conditional wrapper, not general expression
or file trace completion.

A concrete stationary-child counterexample now verifies the limit of the trace
contracts: both children have all five contracts, ordinary execution, and exact
joint specifications, yet the selected parenthesized atom reports a `noProgress`
invariant. Completeness together with that exact execution rules out both
independent trace outcomes for this input. Neither child ordinary execution nor
joint uniqueness substitutes for the strict progress needed by collections.

The selected core and public wrapper are now instantiated as one independent
atom-layer trace relation over only nested-expression and block relations. Four
trace laws use the corresponding child contracts and weak rejected file/end-byte
frames; the separate full-window success context states stronger rejected-child
frames explicitly. Raw groups/tuples, dot arguments/constructors, arrays, selected
core, and public recovery additionally have ordinary execution on arbitrary States
under an explicit remaining-count bound and a three-field nested contract:
successful endIndex preservation, strict cursor progress, and bounded ordinary
execution. The body needs only ordinary execution for this totality result.
It does not require child validity, token/source/end-byte preservation, or any
rejected-state frame. Combining totality with soundness separately establishes
actual core/public traced outcomes and independent public outcomes under the
same bound; this is not a completed general recursive expression parser.

A changed-carrier reverse consumer now exercises a rejected child that replaces
both the tokens and endIndex. The original opening parenthesis is not a boundary,
but the failed carrier's leading semicolon is a boundary after cursor-only rewind.
Exact core and public State/Failure equivalences retain that carrier, the child
event, and arbitrary duplicate prior events without committing the terminal report.

Concrete public-atom reverse consumers use the real literal leaf as the nested
parser. In `.a-b(+) ;`, the checked-name event precedes the exact literal failure;
rewind/recovery then commits that report once and stops before the right parenthesis,
without replaying the skipped name warning. Full State/Failure checks also cover
name-success bypass, immediate boundary rejection, and missing backing where the
core and recovery reports have equal payloads but only the original is committed.
Mixed lexical filtering drops the committed report/recovery event while retaining
the protected name warning and arbitrary prior duplicates remain intact.

Literal-child totality consumers now instantiate the three-field contract at
every child budget. They cover overshot cursors, stored-but-hidden tokens, missing
backing storage, exact end-byte failures, and the single report commitment at a
numerical gap. Independent group/tuple derivations reconstruct full successful
States even when source/window validity fails. These are one-layer consumers;
the displayed loop and child bounds remain explicit.

Maximal postfix tails now have independent success/rejection traces for index,
call, and checked-identifier field suffixes, retaining branch priority, exact
AST spans, ordered child/name events, and all seven first-failure positions.
Nested joint exactness supplies result uniqueness and disjointness, not existence.
Both runtime soundness directions hold at every tail fuel under nested trace
soundness and successful source/full-window context. They add no child progress,
validity, ordinary-execution, or rejected-state frame premise. Index traces do
not inherit the call-argument list's strict-progress check.

Each finite postfix derivation now executes at every fuel above its own threshold
under child completeness and successful context; rewinding index children remain
allowed, so that threshold is not identified with remainingCount. Separately,
the minimal child endIndex/progress/bounded-ordinary contract and explicit loop
and child budgets establish unrestricted ordinary execution, including the
production tail budget. Soundness then supplies actual and independent trace
existence without joint-exactness premises. Joint exactness plus this invariant
exclusion supplies fixed-fuel completeness. Pointwise success and rejection
equivalences reconstruct every State/Failure field; only rejection reconstruction
needs the explicit weak child file/endByte frame. All-fuel context laws preserve
full successful windows or a caller-selected rejected window observation. These
remain tail-layer results, not complete recursive expression traces.

Concrete progress-boundary consumers now show why these distinctions matter.
A stationary child has an independent successful index trace, while a call
with the same child reaches noProgress and has no independent success. A child
that rewinds and replaces tokens still satisfies all five trace contracts,
full-window context, and ordinary execution. Its finite two-index derivation
executes at fuel three, yet the initial production budget of two is exhausted.
Both independent derivations feed reverse completeness; arbitrary incoming
diagnostic multiplicity and the exact final carrier are retained.

An empty token carrier has its own complete normal-output contract: retained
comments and lexical diagnostics, no AST items, and no parser diagnostics.
Validation alone suffices at the token boundary; canonical lexing supplies it
for empty, whitespace-only, comment-only, and lexically diagnosed tokenless
source. Separate compositional laws distinguish ordinary sequencing, which
retains both executed diagnostic suffixes, from transactional choice, which
retries the right alternative on the original state and discards the rejected
left alternative's diagnostics. Those laws explicitly assume branch execution
and are not presented as independent grammar judgments.

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
