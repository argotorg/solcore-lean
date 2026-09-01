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
optional trailing comma. Their prioritized optional wrapper records the
absence of a leading `<` in its absent branch, so the declarative judgment
matches the executable branch choice exactly. Both the list and
optional-wrapper parsers have unconditional success soundness and
source-validity compositions.

Algebraic enums now have exact parser-independent coverage from the contextual
`enum` marker through the closing brace. Constructor payloads are selected by
a leading `(`; when present, they may contain zero fields but cannot have a
trailing comma. Enum bodies may be empty, admit an optional trailing comma,
and retain constructors in forward source order. Every successful enum
declaration is unconditionally grammar-sound. It retains an already supplied
derive attribute in its AST field and uses that attribute's span as the outer
span start; source validity composes with the supplied derive contract.

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

Predicates and optional `where` clauses also have exact component grammars and
unconditional success soundness. Bare sequences retain forward predicate
order and distinguish a final predicate from a trailing comma; grouped
sequences reuse the nonempty trailing-delimiter grammar. The transactional
grouped-or-bare parser is currently specified by the union of its successful
branches. The grammar does not yet add a negative grouped-derivation premise
to a bare fallback that starts with `(`: deriving that stronger priority fact
requires a converse completeness theorem for grouped parsing, which is not yet
proved.

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

Trait declarations now extend that signature boundary through exact method
semicolons and brace-delimited bodies. `TraitMethodTailParses` preserves source
order while recording closing-brace priority, and the fuel-bounded executable
loop reflects diagnostic freedom backward through every retained method.
Complete diagnostic-free trait success therefore derives
`TraitDeclParses`, including its contextual marker, required generics,
optional `where`, body span, method list, and final remainder. Method, body,
and declaration soundness all compose with source validity and are exported
through the public syntax umbrella.

Ordinary function declarations and implementations now have parametric
parser-independent judgments over an abstract block relation. Function
soundness composes the exact location-specific signature, isolated body,
outer cover span, and final remainder. Implementation soundness additionally
retains optional-`default` priority, nonempty trailing-comma head arguments,
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
pattern layer; Core `let`, `return`, assignment, block, `while`, `if`, `break`,
and `continue` statements; and inline-Yul name sequences, the public
expression layer, and its basic controls. Transactional constructor and call
arguments carry explicit declarative rejection specifications whose
disjointness laws preserve parser priority. The remaining work is to finish
the larger Core and Yul statement forms, close the fuel-indexed mutual
recursion, and instantiate the abstract file boundary with those concrete
relations.

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
and recovery exclusion by diagnostic commitment. They remain parameterized
only by the expression and block relations used inside functions and
contracts. Recovered malformed output remains separate so that recovery is
not confused with language acceptance.

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
