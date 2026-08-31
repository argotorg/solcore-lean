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

Canonical Solcore syntax is implemented as a fresh `Solcore.Syntax` layer
under ADR-0153. Its executable lexer and parser target `solcore-rs` PR #20 at
commit `18fd9f75d290df0070e21ee56e0a5691f232596f` and do not reuse the Surface v1
or Multi AST and parser definitions. Oracle v4 remains available only as a
frozen historical compatibility interface. Formal parser proofs continue
after the executable grammar; this does not block use of the Lean parser API.

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

Formal provenance laws prove source identity, the exact full-file span, and
exact retention of the lexer carriers. The public lexer is proved total: its
character-count fuel bound always suffices, so the reserved
`internalFuelExhausted` result cannot occur. Every returned `LexedFile`
satisfies the complete lexical contract. Its tokens and comments have
nonempty, UTF-8-valid spans in source order without overlap, and every retained
lexical diagnostic has a valid source span.

Parser preflight is proved equivalent to that lexical contract, and every
result from the public lexer passes it. Consequently, a public parser error
cannot originate in lexing or preflight; it occurs only after both have
succeeded and the grammar parser has started. Successful public parses expose
the same carrier guarantees directly.

Parser state, primitive consumers, and cursor/lookahead laws preserve valid
spans, file ownership, the immutable token carrier, and the relevant source
order. These compositional guarantees now cover qualified names, module paths,
selector and operator names, literals and primitive token parsers, generic
delimited lists, pragma declarations, Yul name and literal leaves, and derive
targets. Diagnostic filtering can only remove diagnostics and preserves span
validity.

The remaining proof work covers the deeper recursive AST, validity of every
parser-generated diagnostic, provenance and unreachability of grammar
invariant failures, parser resource bounds, and soundness against a
declarative grammar.
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
