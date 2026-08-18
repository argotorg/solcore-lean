# solcore-lean

`solcore-lean` builds an executable formal specification of the Solcore language
in Lean 4, intended to become the reference implementation for semantic
differential fuzzing.

The project has completed the internal **M2a Surface parser proof kernel** and
is preparing its separate M2b publication layer. The published reference
boundary remains M1c: `solcore/0.1.0-draft.3`, profile `core-m1c-v1`, Semantic
Core v2, and Oracle v3. M2a adds an internal parse-only frontend without
widening any published Oracle. The draft.1/Oracle v1 and draft.2/Oracle v2
contracts remain frozen for compatibility.

## What M0 fixes

- exact pin to Lean `v4.32.1`
- draft language version `solcore/0.1.0-draft.1`
- canonical Core profile `core-v1`
  - canonical solver policy is `tabled`
  - M0 enables no language feature whose normative semantics are complete
  - the Core profile does not include an EVM revision
  - UTF-8 byte spans
  - gas-free value observation
  - canonical Lean JSON digest
    `sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8`
- upstream Haskell baseline
  `1d490d8bb5f374356f06e0720655496482eb1fb4`
- comparison Rust baseline
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`
- revision, byte size, SHA-256, and fileset digest for the six upstream standard
  library files
- NDJSON request/response contract for `solcore-oracle/v1`
- separation of `accepted / rejected / unsupported / inconclusive / executed /
  internalError` from protocol errors

## What M1a implements

- bounded word values represented by `Fin (2^256)`
- immutable lexical bindings represented by de Bruijn indices
- condition-first, selected-branch-only conditionals
- soundness and completeness of the executable checker with respect to
  declarative typing
- bidirectional correspondence between declarative big-step evaluation and the
  fuelled CEK machine
- transition determinism, progress, and preservation
- finite-fuel termination and machine-fault unreachability for well-typed
  closed programs

The detailed semantic choices are recorded in
[`ADR-0009`](docs/adr/0009-m1a-core-machine-and-evaluation-order.md).

## What M1b publishes

- the `solcore/0.1.0-draft.2` language version and `core-m1a-v1` profile
- five fine-grained normative features covering only the completed fragment
- the strict `solcore-semantic-core/v1` JSON codec
- canonical 256-bit words encoded as fixed-width lowercase hexadecimal
- deterministic type diagnostics with AST paths and structured arguments
- the `solcore-oracle/v2` `capabilities`, `coreCheck`, and `coreEval` queries
- distinct `inconclusive` outcomes for Core input limits and evaluation fuel
- mixed v1/v2 NDJSON streams and a canonical golden corpus

The publication boundary and v1 compatibility are recorded in
[`ADR-0010`](docs/adr/0010-m1b-core-wire-and-oracle-v2.md).

## What M1c publishes

- the `solcore/0.1.0-draft.3` language version and `core-m1c-v1` profile
- boolean negation `boolNot` and `wordNot`, the complement of all 256 bits of a
  word
- word addition, subtraction, and multiplication modulo `2^256`
- total unsigned word division and remainder, returning zero for a zero divisor
- word equality and unsigned greater-than
- 256-bit `and`, `or`, and `xor`, plus logical shifts that return zero for a
  shift amount greater than or equal to 256
- exactly-once unary evaluation and exactly-once, left-to-right binary operand
  evaluation
- four fine-grained normative features: `coreBoolNot`,
  `coreWordArithmetic`, `coreWordComparison`, and `coreWordBitwise`
- the closed `solcore-semantic-core/v2` wire format, which adds tagged unary and
  binary expressions without widening Semantic Core v1
- the `solcore-oracle/v3` `capabilities`, `coreCheck`, and `coreEval` queries

The proof coverage extends over the M1c expressions: executable type inference
is sound and complete; detailed checking agrees with declarative typing;
primitive application is total and result-type preserving for well-typed
operands; evaluation and CEK transitions are deterministic; big-step and CEK
evaluation correspond in both directions; and progress, preservation,
sufficient-fuel completion, and typed-machine fault unreachability continue to
hold. Semantic Core v2 also has bounded decoder/encoder round-trip and
canonicalization theorems.

Short-circuit `&&` and `||` are deliberately not eager primitives. Their future
source elaboration must use selected-branch-only conditionals. Boolean/word
conversions and other unlisted primitive families are also deferred, as are
functions, closures, application, and return.

The primitive audit found upstream behavior that is evidence, not specification
authority: both primitive tables type direct word equality incorrectly, the
Haskell partial evaluator covers only a subset of operations, large Haskell
shifts can pass through a host `Int`, and both standard libraries currently
encode boolean conjunction/disjunction as eager functions despite noting that
they should short-circuit. See the
[compatibility matrix](docs/COMPATIBILITY_MATRIX.md) and
[`ADR-0011`](docs/adr/0011-m1c-primitive-semantics-and-publication.md).

The Haskell and Rust implementation defaults are not specification authority.
They are isolated in [`Solcore/Baseline.lean`](Solcore/Baseline.lean) as evidence
for differential investigation.

## What the M2a work implements internally

- a source-owned Surface AST independent of Oracle wire types
- half-open UTF-8 byte spans for tokens, comments, names, operators, and nodes
- ASCII-only maximal-munch lexing with line comments and nested block comments
- exact lexical source partition checks for tokens, comments, and discarded
  whitespace
- raw decimal and hexadecimal literal spelling
- unresolved names and generic calls, without spelling-based intrinsics
- explicit grouping, unit syntax, and keyword conditionals
- the pinned implementations' shared precedence and associativity
- a closed single-function fixture envelope with typed immutable bindings and a
  final return
- an independent maximal-munch lexical judgment with an executable checker
- an independent full-token difference-list grammar judgment
- executable span, grammar-shape, and AST/token correspondence checks connected
  to declarative predicates
- success provenance theorems linking the public parser to the exact lexer
  result, complete token correspondence, grammar validity, and a `FileParses`
  derivation
- global uniqueness of accepted lexical partitions and reachability of every
  public source-level lexical rejection
- relational determinism for every parser grammar layer
- reverse executor completeness for every `FileParses` derivation over the
  exact lexer output
- proved lexer and parser fuel sufficiency at the configured input-derived
  bounds

`true` and `false` remain unresolved names. Word-not and shift syntax remains
ordinary calls to such names as `bnotWord`, `bshlWord`, and `bshrWord` until
resolution can identify canonical declarations. Source integer conversion,
name resolution, type checking, and Core elaboration are not part of M2a.

The M2a proof kernel is complete at its internal boundary. The public lexer
gates success with the independent lexical judgment, and accepted lexical
partitions are globally unique. Every public source-level lexer failure is
connected to an implementation-reached cursor and the executable local
rejection judgment. `parseLexed` accepts only the exact lexer result; its
private parser constructs a declarative derivation alongside the AST. Public
success implies grammar shape, full AST/token correspondence, and
`FileParses`, while every `FileParses` derivation for the exact lexer stream
makes the executor return that tree. The grammar is relationally
deterministic. Input-derived lexer and parser fuel bounds are proved sufficient,
so public execution cannot report fuel exhaustion. The lexer's defensive
output-validation error is also proved unreachable from raw executor
soundness.

The parser is deliberately not exposed by Oracle v1, v2, or v3. A later,
additive parser publication will require a closed Surface wire AST, a new
grammar version and frontend profile, and a new Oracle version. The exact
internal boundary is recorded in
[`ADR-0012`](docs/adr/0012-m2a-surface-parser-kernel.md).

## Running

```sh
lake --wfail build
lake --wfail test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
lake exe solcoreOracle --help
lake exe solcoreOracle --version
lake exe solcoreOracle capabilities
lake exe solcoreOracle capabilities-v2
lake exe solcoreOracle capabilities-v3
```

For compatibility, `--version` retains its original Oracle v1 meaning and
prints the draft.1 specification ID. Use `capabilities-v3` for the current M1c
language, profile, schema, and digest binding.

To verify the raw bytes of the canonical standard library as well, run
`node scripts/verify-metadata.mjs --canonical-source-root <solcore>/std` against
the pinned upstream checkout. CI requires this verification.

When invoked without arguments, the Oracle reads one NDJSON request per line
from standard input and emits one response per line in the same order. In
Oracle v1, only `capabilities` succeeds; source-level queries remain
`unsupported`. In Oracle v2, `coreCheck` and `coreEval` are available for the
M1b profile's Semantic Core v1. Oracle v3 provides the same Core-level queries
for the M1c profile and requires Semantic Core v2 input. No published Oracle
currently parses or elaborates a `.solc` workspace, so this is not yet
source-level differential conformance.

## Specification documents

- [Specification charter](docs/SPEC_CHARTER.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Compatibility matrix](docs/COMPATIBILITY_MATRIX.md)
- [M1 Semantic Core plan](docs/M1_PLAN.md)
- [M2 frontend plan](docs/M2_PLAN.md)
- [Architecture decision records](docs/adr)
- [Checked-in core profile](profiles/solcore-0.1.0-draft.1-core.json)
- [Checked-in M1b Core profile](profiles/solcore-0.1.0-draft.2-core-m1a.json)
- [Checked-in M1c Core profile](profiles/solcore-0.1.0-draft.3-core-m1c.json)
- [Oracle v1 JSON Schema](schema/oracle-v1.schema.json)
- [Oracle v2 JSON Schema](schema/oracle-v2.schema.json)
- [Oracle v3 JSON Schema](schema/oracle-v3.schema.json)
- [Semantic Core v1 JSON Schema](schema/semantic-core-v1.schema.json)
- [Semantic Core v2 JSON Schema](schema/semantic-core-v2.schema.json)
- [M1c primitive semantics and publication ADR](docs/adr/0011-m1c-primitive-semantics-and-publication.md)
- [M2a Surface parser kernel ADR](docs/adr/0012-m2a-surface-parser-kernel.md)

## Implementation roadmap

1. **M0 — contract:** version/profile, ADRs, baselines, Oracle schema, CI
2. **M1 — semantic core:** Core AST, typing relation, small-step/CEK semantics,
   executable evaluator, correspondence theorems
3. **M2 — frontend:** parser, name resolution, elaboration,
   modules/type classes/comptime
4. **M3 — contracts:** ABI, storage, transaction observation
5. **M4 — differential fuzzing:** generator/shrinker, three-implementation
   comparison, regression corpus

A feature becomes `implemented` only when it has a declarative judgment, a
decision procedure, a soundness/completeness theorem connecting them (or an
explicitly documented one-way theorem), an Oracle observation, and conformance
tests.
