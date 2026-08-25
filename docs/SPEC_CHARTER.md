# Solcore Lean Specification Charter

- Status: Draft
- Target published specification: `solcore/0.1.0-draft.4`
- Current internal parser milestone: M2c Multi Surface
- Adopted: 2026-07-23

## Read this first

`solcore-lean` has two published executable reference boundaries and several
newer internal kernels. “Implemented in Lean” and “published by an Oracle
profile” are deliberately different claims.

| Boundary | Current status | External contract |
| --- | --- | --- |
| M1c Semantic Core | Closed checker and evaluator with correspondence proofs | Published by Oracle v3 as `solcore/0.1.0-draft.3` / `core-m1c-v1` |
| M2b Surface | Closed one-file parser with lexer/parser correspondence proofs | Published by Oracle v4 as `solcore/0.1.0-draft.4` / `frontend-m2b-v1` |
| M2c Multi Surface | Unconditional executable lexer/parser path with selected-result and soundness theorems; pure 20-rule structural validator awaiting judgment correspondence | Internal Lean API; no new schema, profile, capability, or Oracle query |
| M2c workspace and syntax identity | Pure workspace validation and accepted structural-identity design | Internal only |
| Resolution, checking, elaboration, execution | Not connected as one executable source frontend | Not published |

The [documentation guide](README.md) links the repository's reader paths. Use
[current status](CURRENT_STATUS.md) for the revision-local completion ledger,
[architecture](ARCHITECTURE.md) for module and proof boundaries, and the
[development guide](DEVELOPMENT.md) for reproducible build and audit commands.

The newest implementation result is the M2c Multi parser and its separate
structural validator. The parser entry point no longer requires a
caller-supplied rank certificate or progress premise, and the validator emits
the complete canonical structural diagnostic list. The validator has not yet
been connected to independent judgments or a certified parsed result. None of
this widens Oracle v4, certifies a whole workspace, resolves a name, assigns a
type, elaborates to Core, or executes a contract.

## Purpose

`solcore-lean` is developed independently of the Haskell and Rust
implementations. Its eventual purpose is to serve as the reference oracle for
semantic differential fuzzing: each implementation should be compared under
the same version, feature profile, source or Core input, resource limits,
standard library, and observation policy.

The specification consists of three connected layers:

1. declarative judgments for the language rule being specified;
2. deterministic executable definitions; and
3. correspondence proofs connecting executor results to those judgments.

A Lean definition is useful internal progress, but it becomes a published
language feature only after an Accepted publication decision fixes its version,
profile, schemas, Oracle observation, limits, and conformance tests.

## Current M2c Multi executable boundary

### Entry points

The owned-token entry point is defined in
[`ParseOutcomeTotality.lean`](../Solcore/Surface/Multi/ParseOutcomeTotality.lean):

```text
executeObservedContextualParse :
  (file : WorkspaceFile) ->
  (tokens : List Token) ->
  TokensOwnedBy file tokens ->
  Except ParseDiagnostic ParsedModuleV1
```

`TokensOwnedBy file tokens` states that every token span belongs to the input
file. Given that premise, the caller does not provide a rank potential,
bounded-search success proof, or normalization-progress theorem.

The file-only entry point is defined in
[`Properties.lean`](../Solcore/Surface/Multi/Properties.lean):

```text
executeObservedContextualFrontend :
  WorkspaceFile -> Except SurfaceDiagnostic ParsedModuleV1
```

It runs `lexModule`, obtains token ownership from the lexer proof, and invokes
`executeObservedContextualParse`. Its result mapping is closed:

- lexer failure becomes `SurfaceDiagnostic.lexical`;
- parser failure becomes `SurfaceDiagnostic.parse`;
- parser success returns `ParsedModuleV1`; and
- `SurfaceDiagnostic.structural` cannot be constructed by this path because
  the later structural-validation phase is not run here.

This is not yet the ADR-0015 `Multi.parseModule` interface returning a
`CertifiedParsedModule` and aggregated structural diagnostics.

### What is proved

The new public Lean theorems form the following chain:

1. `dottedStaticRankTable_eq_true` proves the fixed static table is accepted.
2. `boundedFrontierDottedGrammarRankSearchSucceeds` turns that table into
   bounded search success at every greatest reachable cursor.
3. `executeObservedContextualBoundedDottedPotentialSearchSucceeds` specializes
   the result to the concrete chart executor.
4. `executeObservedContextualValueWorklistMulti_rootlessExecutableProgress`
   supplies the progress premise used by parse-outcome totality.
5. `executeObservedContextualParse_selected` proves that the unconditional
   token-level function is exactly the chart implementation's selected result.
6. `executeObservedContextualParse_sound` proves that success satisfies
   `Parses` and failure satisfies `ParseDiagnostic.Applies`.
7. `executeObservedContextualFrontend_selected` performs the corresponding
   selection statement across lexing and parsing.
8. `executeObservedContextualFrontend_sound` proves exact lexer provenance for
   successful and parse-error results, lexical diagnostic soundness, parse
   diagnostic soundness, and impossibility of the structural branch.

These are soundness and implementation-selection claims. They do not by
themselves certify structural acceptance, resolution, typing, or elaboration.

### Why the rank search closes

The fixed Multi grammar contains exactly 2,378 enumerated dotted
right-hand-side states. The static checker covers every row and all three edge
families used by normalization:

- prediction into a nonempty production;
- direct epsilon advance; and
- completion into a waiting continuation.

The potential is lexicographic. A static strongly-connected-component rank
handles edges between components, the origin coordinate handles consuming
completion cycles, and a within-component phase handles nullable completion
edges. The checked constants are a maximum component rank of 162 and a phase
width of 10; a separate capacity theorem places the values inside the generic
finite search space.

The 2,378 rows are split into one 640-row shard, eighteen 96-row shards, and a
final 10-row tail, then assembled in
[`RootlessNormalizationDottedStaticCertificate.lean`](../Solcore/Surface/Multi/RootlessNormalizationDottedStaticCertificate.lean).
The grammar-wide certificate is connected to contextual parser reachability in
[`RootlessNormalizationDottedStaticTotality.lean`](../Solcore/Surface/Multi/RootlessNormalizationDottedStaticTotality.lean).

The table theorem reports only `propext` and `Quot.sound` under `#print axioms`.
The final totality, selection, and soundness theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. No project-specific axiom or admitted
proof is part of this chain.

### Performance status

Logical totality is not a performance guarantee. In one earlier development
runtime smoke, an empty-input Multi parse had not completed after more than 226
seconds. Investigation found a Phase C runner that continued after its queues
were empty; that path now stops immediately. The executor also avoids
recomputing Phase A saturation after the worklist result has already certified
it, classifies completion items once, rejects incompatible prediction
candidates before rebuilding the waiting production, indexes complete-item
recognition, removes whole-item self comparisons from the role-directed
completion scan, and materializes the Phase A evidence table in a linear bulk
step.
Phase B checks the eight finalization slots for each guard through the coherent
hash index, then batches the proved-fresh block. Exact-equivalence theorems
preserve the checked reference result for these execution changes. The counter
retains `usedRev` as its proof
ledger and uses a coherent hash set to make duplicate checks fast. The proved
agreement between these two views ensures that only lookup cost changes;
charge order, failures, and resulting states do not.

On the development host, the native `tiny` benchmark (`data A;`) took about
89.0 seconds before these passes and 2.339 and 2.425 seconds across two
fresh-process runs afterward (about 2.38 seconds). The latest observed `empty`
elapsed time was 0.365 seconds. `/usr/bin/time` reported a maximum resident set
size of 59,965,440 bytes for `tiny`.
These observations are neither normative limits nor stable benchmarks;
broader runtime and memory behavior remains uncharacterized.

Therefore:

- the current Multi executor is a formal reference path, not a production
  parser;
- wall-clock parser measurements remain outside the ordinary fast suite;
- static proof shards should be cached during routine verification; and
- profiling and optimization remain incomplete, while the native benchmark now
  provides a reproducible regression entry point.

## Published version and profile boundaries

### M0 contract

M0 fixes Lean `v4.32.1`, `solcore/0.1.0-draft.1`, and `core-v1`. The canonical
solver policy is `tabled`; the profile enables no feature whose normative
semantics were complete at M0 and fixes no EVM revision. Spans use UTF-8 byte
offsets and Core value observation is gas-free.

The canonical Lean JSON digest is
`sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8`.
The evidence baselines are Haskell
`1d490d8bb5f374356f06e0720655496482eb1fb4` and Rust
`38f4778ea461edfe59106bdb1f9f08c3307b0fc0`. Oracle v1 fixes the original
NDJSON request/response contract and verdict taxonomy.

### M1b and M1c Semantic Core

M1b publishes `solcore/0.1.0-draft.2`,
[`core-m1a-v1`](../profiles/solcore-0.1.0-draft.2-core-m1a.json), Semantic Core
v1, and Oracle v2. Its `coreCheck` and `coreEval` queries use strict codecs,
canonical 256-bit words, deterministic structured diagnostics, and explicit
`inconclusive` outcomes for limits.

M1c publishes `solcore/0.1.0-draft.3`,
[`core-m1c-v1`](../profiles/solcore-0.1.0-draft.3-core-m1c.json),
[`solcore-semantic-core/v2`](../schema/semantic-core-v2.schema.json), and
[`solcore-oracle/v3`](../schema/oracle-v3.schema.json). ADR-0011 fixes the
publication boundary.

The M1c fragment includes boolean and word negation; word addition,
subtraction, multiplication, total unsigned division and remainder; word
equality and unsigned greater-than; 256-bit `and`, `or`, and `xor`; and logical
shifts. Arithmetic is modulo `2^256`; division and remainder by zero return
zero; shifts by at least 256 return zero. Unary operands are evaluated exactly
once, and binary operands exactly once from left to right.

For this fragment, declarative and executable typing/evaluation are connected
by soundness, completeness, determinism, CEK correspondence, progress,
preservation, sufficient-fuel completion, and typed-machine fault
unreachability. Semantic Core v2 also has bounded codec round-trip and
canonicalization theorems.

Short-circuit conjunction/disjunction are not eager primitives. Boolean/word
conversions and the Core meanings of functions, closures, application, and
return remain outside the published fragment.

### M2b published Surface

M2b publishes parsing as `solcore/0.1.0-draft.4`,
[`frontend-m2b-v1`](../profiles/solcore-0.1.0-draft.4-frontend-m2b.json),
[`solcore-surface/v1`](../schema/surface-v1.schema.json),
[`solcore-parse-result/v1`](../schema/parse-result-v1.schema.json), and
[`solcore-oracle/v4`](../schema/oracle-v4.schema.json). The profile enables
exactly `surfaceGrammar`; it enables no Core query or source semantic phase.

Oracle v4 `parse` accepts one content string and a nonempty opaque source
label. The label is copied exactly into spans and is not normalized, resolved,
or used for file I/O. The default `sourceBytes` limit is 1,048,576 and counts
only content UTF-8 bytes. An over-limit input is `inconclusive` before lexing.

The published proof boundary includes maximal-munch lexical correctness,
global uniqueness of accepted lexical partitions, source-level rejection
reachability, exact lexer-result provenance, full token correspondence,
grammar validity, a `FileParses` derivation, relational parser determinism,
reverse parser completeness, and sufficient lexer/parser fuel. Public
execution cannot report fuel exhaustion, and the lexer's defensive
output-validation failure is unreachable.

Oracle v4 still does not load a workspace, interpret the label as a path,
resolve imports or names, assign types, elaborate to Core, or execute a
program.

### Frozen compatibility

All draft.1 through draft.3 language/profile documents, digests, Core and
Oracle schemas, capability bytes, and golden streams remain immutable. Oracle
v2 remains bound to Semantic Core v1; Oracle v3 remains bound to Semantic Core
v2; Oracle v4 remains bound to the M2b Surface v1 parser. M2c internal modules
do not alter those bytes or behaviors.

## M2c internal design status

[`ADR-0014`](adr/0014-m2c-workspace-identity.md) accepts pure canonical logical
paths, structured library/source/module identities, and deterministic
validation of a closed workspace. It does not authorize host filesystem access
or resolution.

[`ADR-0015`](adr/0015-m2c-multi-surface-parser.md) accepts the closed,
source-preserving Multi Surface grammar and the target certified parser
boundary. The unconditional lexer/parser executor described above closes a
major totality prerequisite, but the current file-only API still returns raw
`ParsedModuleV1`, not `CertifiedParsedModule`.

[`ADR-0016`](adr/0016-m2c-structural-syntax-identity.md) accepts structural
syntax identity over certified parser output.

[`ADR-0017`](adr/0017-m2c-module-resolution.md) remains Proposed. No module or
lexical resolver is authorized as a published feature. A later publication ADR
must assign new language, profile, wire, limit, capability, and golden-stream
versions before any resolver observation becomes public.

## Specification authority

Sources of semantic information have this order of precedence:

1. the versioned Lean declarative specification;
2. Accepted ADRs and the version manifests designated by those ADRs;
3. Lean executors proved to correspond to the declarative specification;
4. normative conformance tests; and
5. existing documentation, Haskell and Rust implementations, the standard
   library, and historical test corpora.

A higher-ranked source prevails over a lower-ranked source. Agreement between
the two existing implementations, majority behavior, inclusion in a corpus,
or long-standing behavior is evidence, not a specification decision. A
conflict between a declarative relation and its executor is a defect in the
executor or proof connection.

Every new normative choice or observable change requires an Accepted ADR. All
affected grammar, static-semantics, dynamic-semantics, ABI, and storage-layout
versions must be updated.

## Design principles

- Keep Surface, Resolved, and Semantic Core boundaries explicit.
- Preserve source order, UTF-8 byte spans, and syntactic boundaries in Surface.
- Represent closures, pattern matching, type application, class evidence, and
  comptime/runtime stages directly in Semantic Core when those features are
  specified.
- Treat Hull, Yul, and EVM bytecode as future lowering targets, not the
  specification kernel.
- Keep the semantic kernel pure and total, without real I/O or unchecked escape
  hatches.
- Give potentially unbounded evaluation or search an explicit resource limit.
  Exhausting a limit may produce `inconclusive`; it never changes the language
  semantics into rejection.
- Make the host, block context, state, and transaction sequence explicit inputs.
- Exclude generated names, internal map order, English prose, and presentation
  layout from semantic observations unless a future profile says otherwise.

## Versions, features, and comparison baselines

`LanguageVersion` records grammar, static-semantics, dynamic-semantics, ABI,
and storage-layout versions, the standard-library digest, and known feature
IDs. An incomplete component has version `none`. EVM revisions and gas
schedules belong to a contract-scoped `ContractRuntimeProfile`, not pure Core.

Feature state distinguishes known, designed, normative, enabled, and
implemented. A successful published query requires:

```text
implemented ⊆ enabled ⊆ normative ⊆ known
```

The Haskell/Rust commits, solver mode, dispatch setting, backend, limits, and
similar conditions belong to an `ImplementationBaseline`; changing an
implementation does not change the language version.

Every comparison must align:

- language version and feature profile;
- standard-library contents;
- solver policy;
- reached phase, such as frontend, specialization, or dispatch;
- EVM revision and deterministic host where relevant;
- initial state and transaction sequence; and
- semantic observation policy.

Oracle responses include the request ID, specification, profile ID and digest,
and query kind so the comparison conditions remain identifiable. Capability
reports are complementary: v3 describes the M1c Core boundary; v4 describes
the M2b parse-only boundary. Neither claims full source-level conformance among
Lean, Haskell, and Rust.

## Verdicts

The six language verdicts are:

| Verdict | Meaning |
| --- | --- |
| `accepted` | The requested static phase completed successfully |
| `rejected` | The input violates a rule defined by the selected profile |
| `unsupported` | Required semantics are not defined or enabled by the profile |
| `inconclusive` | A resource limit prevented a definitive observation |
| `executed` | A dynamic query completed with a normative observation |
| `internalError` | The Oracle encountered an invariant violation or defect |

Malformed JSON, duplicate keys, unknown schemas, empty source labels, and
similar envelope failures are `protocolError`, outside the language verdicts.

The following reinterpretations are forbidden:

- an unimplemented feature is not `rejected`;
- exhausted time, solver fuel, or evaluation fuel is not `rejected`;
- a crash or invariant violation is not source-program rejection; and
- a defined `revert` or `trap` is not `internalError`.

## Observational equivalence

Static queries compare diagnostic codes, phases, severities, UTF-8 byte spans,
and structured arguments. English messages and display layout are not
normative.

Value evaluation compares canonical values and halt status. Future contract
execution observations must distinguish return, revert, and trap and compare
return/revert data, storage and balance deltas, logs, external-call traces, and
created-contract address/code. Gas is excluded from the standard profile until
a dedicated profile fixes the EVM revision, gas schedule, and warm/cold state.

## Non-goals and current exclusions

The project does not currently aim to:

- reproduce Haskell or Rust behavior unconditionally;
- define Lean semantics through a backend or match Hull/Yul/bytecode output;
- prove both implementations correct in their entirety at once;
- guess unresolved ABI, storage, inline-Yul, resolver, or intrinsic behavior;
- compare diagnostic prose, colors, or presentation order;
- compare gas in the standard profile;
- treat resource exhaustion as rejection; or
- describe the current M2c parser as runtime-optimized or production-ready.

## Verification and conformance requirements

The [development guide](DEVELOPMENT.md) is the operational companion to this
charter. It explains the expected build, test, metadata, kernel-policy, and
theorem-dependency review workflow.

The repository verification path is:

```sh
lake --wfail build
lake --wfail test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
lake env lean -DwarningAsError=true Solcore.lean
```

The kernel policy rejects the exact pattern
`/\b(sorry|admit|partial|unsafe|axiom|noncomputable|extern|implemented_by)\b/`
under the semantic roots. Public theorem dependencies are also audited with
`#print axioms`. The static rank proof is sharded for bounded compilation and
incremental caching; the shards still produce ordinary kernel-checked proof
terms.

Every published normative rule should normally have:

1. a minimal positive witness;
2. a minimal negative witness violating only that rule;
3. the expected verdict and failure phase;
4. a theorem or property test connecting executor and declarative relation;
   and
5. an Oracle golden test for canonical serialization.

Additionally:

- minimized Haskell/Rust discrepancies belong in the normative corpus only
  after the specification decision is fixed;
- semantically irrelevant input/key/map ordering must preserve canonical
  output;
- tests must distinguish `unsupported`, `inconclusive`, and `internalError`
  from `rejected`;
- future contract tests must align EVM revision, initial state, and transaction
  sequence;
- revert tests must verify rollback;
- ABI tests must cover metadata, selector spelling, decode, encode, and
  collision detection; and
- the semantic kernel must remain free of the forbidden declarations checked
  above.

The corpus is evidence, not authority. Updating an expected result requires the
corresponding specification or ADR change.

## Completion and publication gates

### Historical M0 gate

M0 is complete: version/profile/baseline boundaries, NDJSON schema, verdict
taxonomy, capability reporting, unsupported behavior, canonicalization, path
validation, and streaming tests are fixed.

### Historical M1c gate

M1c is published because the primitive semantics are independent of compiler
defaults; typing/evaluation relations cover every published expression;
executors are proof-connected; progress, preservation, sufficient fuel, and
fault unreachability hold; Semantic Core v2 and Oracle v3 are closed and
version-bound; and earlier Oracle artifacts retain their bytes.

### Current M2b publication gate

M2b is published because `surfaceGrammar` closes its lexer, grammar, spans,
comments, AST, and source diagnostics; parser success and rejection are
proof-connected; determinism, reverse completeness, lexical uniqueness, and
sufficient fuel hold; Surface v1, parse-result v1, and Oracle v4 are closed and
version-bound; the source label is opaque; and earlier artifacts remain frozen.

### Internal M2c parser gate

The current internal milestone closes unconditional bounded parsing for the
fixed Multi grammar and exposes token-level and file-only executable APIs with
selection and soundness theorems. It does not complete M2c publication.

Before a complete M2c frontend can be claimed, at least the following remain:

- connect the file-only result to structural validation and
  `CertifiedParsedModule`;
- optimize runtime behavior enough for practical regression tests;
- define and implement reachable-workspace parsing;
- accept and implement the resolver boundary;
- connect source checking and elaboration to declarative judgments; and
- publish new version/profile/wire/Oracle contracts through a separate ADR.

Until those gates close, M2b remains the published parser reference and M2c
remains an internal, formally justified but performance-limited parser kernel.
