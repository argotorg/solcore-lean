# solcore-lean

`solcore-lean` is an executable formal specification of Solcore in Lean 4. It
is intended to become the reference implementation for semantic differential
fuzzing, but the repository does not yet specify the whole source language.

The newest internal milestone is an unconditional executable parser for the
M2c Multi Surface grammar. The published compatibility boundary remains
unchanged: Oracle v3 exposes the closed M1c Semantic Core, and Oracle v4
exposes the smaller M2b parse-only Surface language.

## Five-minute status

| Boundary | What runs today | What is proved | Published? |
| --- | --- | --- | --- |
| M1c Semantic Core | Type checking and evaluation of the closed Core fragment | Checker soundness/completeness, CEK correspondence, progress, preservation, sufficient fuel, and typed fault unreachability | Yes: `solcore-oracle/v3`, `solcore/0.1.0-draft.3`, `core-m1c-v1` |
| M2b Surface | One-file lexing and parsing through Oracle v4 | Exact lexer provenance, grammar and token correspondence, parser determinism/completeness, and sufficient fuel | Yes: `solcore-oracle/v4`, `solcore/0.1.0-draft.4`, `frontend-m2b-v1` |
| M2c Multi Surface | One `WorkspaceFile` can be lexed and parsed by `executeObservedContextualFrontend`; owned tokens can be parsed by `executeObservedContextualParse` | Bounded parser normalization is unconditional for the fixed grammar; selected results agree with the chart implementation; every returned parse or diagnostic satisfies its declarative judgment | No: internal Lean API only |
| M2c workspace identity | Pure validation of canonical logical paths and closed workspaces | Validator soundness/completeness, unique output, canonical errors, lookup and measure invariants | No: internal kernel only |
| Resolution and later phases | Not available through a complete executable frontend | ADR work exists, but no published resolver/checker/elaborator/evaluator boundary | No |

For a guided tour, start with the [documentation guide](docs/README.md). The
[current status](docs/CURRENT_STATUS.md) is the revision-local implementation
ledger, [architecture](docs/ARCHITECTURE.md) explains the proof and execution
boundaries, and the [development guide](docs/DEVELOPMENT.md) gives the build and
review workflow.

“Unconditional parser” has a precise meaning here: callers no longer supply a
rank potential, a successful bounded-search proof, or a normalization-progress
assumption. It does **not** mean that every source is accepted; lexical and
parse errors are ordinary results.

## Current M2c Multi parser API

The token-level entry point is defined in
[`ParseOutcomeTotality.lean`](Solcore/Surface/Multi/ParseOutcomeTotality.lean):

```text
executeObservedContextualParse :
  (file : WorkspaceFile) ->
  (tokens : List Token) ->
  TokensOwnedBy file tokens ->
  Except ParseDiagnostic ParsedModuleV1
```

Use this when the caller already has the exact token stream and its
source-ownership proof. Its companion theorems are:

- `executeObservedContextualBoundedDottedPotentialSearchSucceeds`, which closes
  bounded rank synthesis for the concrete chart;
- `executeObservedContextualValueWorklistMulti_rootlessExecutableProgress`,
  which supplies normalization progress;
- `executeObservedContextualParse_selected`, which identifies the returned
  value with the chart implementation's selected outcome; and
- `executeObservedContextualParse_sound`, which proves that success satisfies
  `Parses` and failure satisfies `ParseDiagnostic.Applies`.

The file-only entry point is defined in
[`Properties.lean`](Solcore/Surface/Multi/Properties.lean):

```text
executeObservedContextualFrontend :
  WorkspaceFile -> Except SurfaceDiagnostic ParsedModuleV1
```

It runs `lexModule`, derives `TokensOwnedBy` from successful lexing, and then
calls `executeObservedContextualParse`. Lexical failures are returned as
`SurfaceDiagnostic.lexical`; parser failures are returned as
`SurfaceDiagnostic.parse`. This particular path does not run the later
structural-validation phase, so `SurfaceDiagnostic.structural` is unreachable.
The theorem `executeObservedContextualFrontend_sound` states exactly:

- an accepted module comes from the exact successful lexer result and satisfies
  `Parses`;
- a lexical diagnostic satisfies `LexicalDiagnostic.Applies`;
- a parse diagnostic comes from the exact successful lexer result and satisfies
  `ParseDiagnostic.Applies`; and
- the structural branch is impossible.

This API is the simplest executable path for the internal Multi grammar. It is
not the published Oracle v4 parser and is not yet the ADR-0015 certified
`Multi.parseModule` boundary.

## Why bounded parsing is now unconditional

The fixed Multi grammar has 2,378 dotted right-hand-side states. The repository
enumerates every row and checks the rank constraints needed by prediction,
direct epsilon advance, and completion. The static certificate is split into
one 640-row shard, eighteen 96-row shards, and a final 10-row tail, then
assembled by
`dottedStaticRankTable_eq_true` in
[`RootlessNormalizationDottedStaticCertificate.lean`](Solcore/Surface/Multi/RootlessNormalizationDottedStaticCertificate.lean).

The rank combines three coordinates:

1. a static strongly-connected-component rank for the dotted grammar state;
2. the input origin, which breaks consuming completion cycles; and
3. a within-component phase for nullable completion edges.

The checked data uses component ranks at most 162 and a phase width of 10. The
capacity theorem places the resulting lexicographic potential inside the
generic finite search bound. The table certificate is then connected to actual
reached parser items by
[`RootlessNormalizationDottedStaticTotality.lean`](Solcore/Surface/Multi/RootlessNormalizationDottedStaticTotality.lean),
yielding `boundedFrontierDottedGrammarRankSearchSucceeds` for every greatest
reachable cursor.

The final certificate theorem depends only on Lean's `propext` and
`Quot.sound`. The public totality, selection, and soundness theorems depend only
on `propext`, `Classical.choice`, and `Quot.sound`. There are no project-specific
axioms or admitted proof holes in this chain.

## Important performance limitation

The M2c Multi parser is executable but not yet practical. In one development
runtime smoke, even an empty-input parse had not completed after more than
226 seconds. That observation is not a semantic limit or a stable benchmark;
it shows that the proof-oriented chart representation and bounded-search path
still need substantial runtime optimization.

Consequences:

- do not put an end-to-end Multi parse smoke into the ordinary fast test suite;
- do not interpret logical totality as a latency claim;
- use cached proof shards for normal verification; and
- treat the current Multi executor as a formal reference path, not a production
  parser.

Practical optimization, profiling, and a fast regression harness remain open
work.

## What is still not implemented

The internal Multi frontend currently stops after lexing and parsing. It does
not yet provide a complete executable path for:

- aggregation of structural diagnostics into an ADR-0015 certified module;
- parsing every reachable file of a workspace;
- module graph construction, imports, exports, or name resolution;
- selectors, intrinsic identity, or standard-library declaration resolution;
- source type checking or class/instance solving;
- elaboration from Multi Surface into Semantic Core;
- ABI, storage, transactions, contract execution, or EVM observations; or
- a new wire schema, profile, capability report, or Oracle query.

ADR-0015 and ADR-0016 are accepted internal designs for the Multi parser and
structural syntax identity. ADR-0017 remains proposed for module and lexical
name resolution. None of them changes the frozen Oracle v1-v4 publication
boundaries without a later publication ADR.

## Published boundaries retained for compatibility

### M0 contract

- Lean is pinned exactly to `v4.32.1`.
- `solcore/0.1.0-draft.1` and `core-v1` define the original contract boundary.
- The canonical solver policy is `tabled`; M0 enables no completed language
  feature and includes no EVM revision.
- Spans use UTF-8 byte offsets and Core value observation is gas-free.
- The canonical Lean JSON digest is
  `sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8`.
- The pinned Haskell baseline is
  `1d490d8bb5f374356f06e0720655496482eb1fb4`; the pinned Rust baseline is
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`.
- Oracle v1 fixes the NDJSON contract and separates language verdicts from
  protocol errors.

### M1 Semantic Core

M1a implements 256-bit words as `Fin (2^256)`, de Bruijn lexical bindings,
selected-branch-only conditionals, a sound and complete checker, declarative
big-step evaluation, and a fuelled CEK machine with correspondence,
determinism, progress, preservation, termination at sufficient fuel, and fault
unreachability for well-typed closed programs.

M1b publishes `solcore/0.1.0-draft.2`, `core-m1a-v1`, Semantic Core v1, and
Oracle v2 `coreCheck`/`coreEval`. It fixes strict codecs, canonical fixed-width
lowercase hexadecimal words, deterministic structured type diagnostics,
resource-limit `inconclusive` results, and mixed-version compatibility tests.

M1c publishes `solcore/0.1.0-draft.3`, `core-m1c-v1`, Semantic Core v2, and
Oracle v3. Its closed fragment adds boolean and word negation; word addition,
subtraction, multiplication, total division and remainder; equality and
unsigned greater-than; bitwise `and`/`or`/`xor`; and logical shifts. Arithmetic
is modulo `2^256`; division or remainder by zero returns zero; shifts by at
least 256 return zero; operands are evaluated exactly once and binary operands
left to right.

Short-circuit `&&` and `||` are deliberately not eager primitives. Their future
source elaboration must use selected-branch-only conditionals. Boolean/word
conversions, functions, closures, application, and return remain outside the
published Core fragment.

### M2b published Surface parser

M2b publishes `solcore/0.1.0-draft.4`, `frontend-m2b-v1`, Surface v1,
parse-result v1, and Oracle v4. The profile enables exactly `surfaceGrammar`.
It fixes source-owned ASTs, half-open UTF-8 byte spans, ASCII maximal-munch
lexing, comments and whitespace partitioning, raw integer spelling, unresolved
names and calls, grouping, unit syntax, keyword conditionals, and the pinned
implementations' shared precedence and associativity for its closed fixture
grammar.

Oracle v4 parses one content string with a nonempty opaque source label. The
label is copied unchanged into spans and is never treated as a path. The
`sourceBytes` limit counts only content UTF-8 bytes; an over-limit request is
`inconclusive`. Oracle v4 does not load a workspace, resolve names or imports,
type-check source, elaborate to Core, or execute a program.

Oracle v1 through v3 and every draft.1 through draft.3 artifact remain frozen.
The M2c internal work does not change their schemas, capability bytes, golden
streams, or behavior, and it does not change Oracle v4.

The Haskell and Rust defaults are evidence for differential investigation, not
specification authority. They remain isolated in
[`Solcore/Baseline.lean`](Solcore/Baseline.lean).

## Verification

The normal repository checks are:

```sh
lake --wfail build
lake --wfail test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
lake env lean -DwarningAsError=true Solcore.lean
```

`scripts/check-kernel.mjs` rejects the exact pattern
`/\b(sorry|admit|partial|unsafe|axiom|noncomputable|extern|implemented_by)\b/`
in the semantic kernel. The static rank certificate is intentionally split
across modules so a cold kernel check can be cached incrementally.

To verify the raw bytes of the canonical standard library, also run:

```sh
node scripts/verify-metadata.mjs --canonical-source-root <solcore>/std
```

CI requires this check against the pinned upstream checkout.

## Running the published Oracle

```sh
lake exe solcoreOracle --help
lake exe solcoreOracle --version
lake exe solcoreOracle capabilities
lake exe solcoreOracle capabilities-v2
lake exe solcoreOracle capabilities-v3
lake exe solcoreOracle capabilities-v4
```

With no arguments, the Oracle reads one NDJSON request per line and emits one
response per line in order. `--version` retains the original Oracle v1 meaning
and prints the draft.1 specification ID. Oracle v2 exposes M1b Core queries,
Oracle v3 exposes M1c Core queries, and Oracle v4 exposes only capabilities and
the M2b one-file parse query.

## Documents and schemas

- [Documentation guide](docs/README.md)
- [Current implementation status](docs/CURRENT_STATUS.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Development guide](docs/DEVELOPMENT.md)
- [Specification charter](docs/SPEC_CHARTER.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Haskell/Rust compatibility matrix](docs/COMPATIBILITY_MATRIX.md)
- [M1 Semantic Core plan](docs/M1_PLAN.md)
- [M2 frontend plan](docs/M2_PLAN.md)
- [Architecture decision records](docs/adr)
- [M1c primitive semantics and publication ADR](docs/adr/0011-m1c-primitive-semantics-and-publication.md)
- [M2a Surface parser kernel ADR](docs/adr/0012-m2a-surface-parser-kernel.md)
- [M2b Surface parser publication ADR](docs/adr/0013-m2b-surface-parser-publication.md)
- [M2c workspace identity ADR](docs/adr/0014-m2c-workspace-identity.md)
- [M2c Multi Surface parser ADR](docs/adr/0015-m2c-multi-surface-parser.md)
- [M2c structural syntax identity ADR](docs/adr/0016-m2c-structural-syntax-identity.md)
- [Proposed M2c resolution ADR](docs/adr/0017-m2c-module-resolution.md)
- [M0 profile](profiles/solcore-0.1.0-draft.1-core.json)
- [M1b profile](profiles/solcore-0.1.0-draft.2-core-m1a.json)
- [M1c profile](profiles/solcore-0.1.0-draft.3-core-m1c.json)
- [M2b profile](profiles/solcore-0.1.0-draft.4-frontend-m2b.json)
- [Oracle v1 schema](schema/oracle-v1.schema.json)
- [Oracle v2 schema](schema/oracle-v2.schema.json)
- [Oracle v3 schema](schema/oracle-v3.schema.json)
- [Oracle v4 schema](schema/oracle-v4.schema.json)
- [Semantic Core v1 schema](schema/semantic-core-v1.schema.json)
- [Semantic Core v2 schema](schema/semantic-core-v2.schema.json)
- [Surface v1 schema](schema/surface-v1.schema.json)
- [Parse result v1 schema](schema/parse-result-v1.schema.json)

## Roadmap

1. **M0 — contract:** version/profile, ADRs, baselines, Oracle schema, CI
2. **M1 — Semantic Core:** typing, execution, CEK correspondence, publication
3. **M2 — frontend:** Multi parser optimization, structural certification,
   resolution, source checking, elaboration, modules/type classes/comptime
4. **M3 — contracts:** ABI, storage, transaction observation
5. **M4 — differential fuzzing:** generators, shrinkers, cross-implementation
   comparison, and regression corpus

A feature becomes published `implemented` only when its normative judgment,
executor, correspondence proof, version/profile decision, Oracle observation,
and conformance tests are all present. An internal Lean theorem or executable
definition alone does not widen a published profile.
