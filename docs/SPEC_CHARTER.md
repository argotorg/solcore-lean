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
| M2c Multi Surface | Unconditional chart-based lexer/parser path with selected-result, soundness, and parser-wide location-validity theorems; separately certified 20-code structural validator with two-way correspondence; exact-token dispatch and the certified frontend core are implemented but final root closure is pending; bound functions exist while unit-accounting sufficiency and the fast parser remain pending | Internal Lean API; no new schema, profile, capability, or Oracle query |
| M2c workspace and syntax identity | Pure workspace validation and accepted structural-identity design | Internal only |
| Resolution, checking, elaboration, execution | Not connected as one executable source frontend | Not published |

The [documentation guide](README.md) links the repository's reader paths. Use
[current status](CURRENT_STATUS.md) for the revision-local completion ledger,
[architecture](ARCHITECTURE.md) for module and proof boundaries, and the
[development guide](DEVELOPMENT.md) for reproducible build and audit commands.

The newest implementation result is the M2c Multi parser and its separate
structural validator. The parser entry point no longer requires a
caller-supplied rank certificate or progress premise, and the validator emits
a canonical diagnostic list spanning all 20 structural codes. An independent
`Applies` relation covers all 26 diagnostic forms represented by
`MSS0001`–`MSS0020`,
and `StructurallyAccepts` is proved equivalent to having no applicable
diagnostic. Primitive rules are exact, the executable layers are connected,
and executable diagnostics are exactly the applicable diagnostics. The
module-derived traversal fuel is sufficient, and validator success is exactly
structural acceptance. Successful parses now also carry a proof that every AST
location is valid for its source and properly nested. Exact token
root closure, complete resource accounting, and the proof-argument-free
certified file wrapper remain. None of this widens
Oracle v4, certifies a whole workspace, resolves a name, assigns a type,
elaborates to Core, or executes a contract.

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

The kernel-checked parser proof has four user-visible consequences:

- the fixed grammar has a finite decreasing rank, so callers do not supply a
  termination or progress proof;
- the token-level and file-level functions return exactly the chart-selected
  outcome; and
- successful parsing satisfies `Parses`, while lexical and parse failures
  satisfy their independent diagnostic judgments with exact source
  provenance; and
- `Parses.everyLocationValid` proves that every successfully parsed module has
  source-valid locations and direct parent-child nesting throughout its AST.

These are soundness and implementation-selection claims. They do not by
themselves certify structural acceptance, resolution, typing, or elaboration.

### Why the rank search closes

The fixed Multi grammar has a finite, checked table covering every parser state
and every normalization transition. Each transition decreases a
lexicographically ordered potential, so the executable parser terminates
without asking callers for a progress proof.

Kernel auditing finds only Lean's expected logical dependencies: `propext`,
`Quot.sound`, and, for executable selection, `Classical.choice`. No
project-specific assumption is part of this chain. The table layout and audit
commands are recorded in the [development guide](DEVELOPMENT.md).

### Performance status

Logical totality is not a performance guarantee. In one earlier development
runtime smoke, an empty-input Multi parse had not completed after more than 226
seconds. The empty-queue loop was fixed, repeated work was removed, and parser
lookups and evidence handling were indexed or streamed. Phase B now consumes
its evidence into a temporary cache-only state. Checked correspondence with the
reference path preserves selected output, failures, counter state, and charge
order. Detailed engineering notes remain in the
[development guide](DEVELOPMENT.md).

All six representative cases pass. Five fresh-process runs on the development
host produced the following measurements:

| Case | Elapsed seconds (range) | Median | Maximum RSS (bytes) |
| --- | ---: | ---: | ---: |
| `empty` | 0.014303167–0.014395000 | 0.014339333 | 42,647,552 |
| `tiny` | 0.090263250–0.096705291 | 0.090872417 | 60,375,040 |
| `import-path` | 0.221413542–0.227876417 | 0.223409167 | 90,275,840 |
| `return-literal` | 0.863788792–0.887059959 | 0.868775750 | 210,714,624 |
| `data-constructors` | 0.387477833–0.433975625 | 0.392871250 | 139,575,296 |
| `contract-field` | 0.536238167–0.599856583 | 0.567094417 | 169,820,160 |

This is a large speed improvement from the earlier roughly 89-second `tiny`
result.

These observations are neither normative limits nor stable benchmarks.
Cache-only Phase B lowers retained memory, but the Phase A evidence
enumeration, lookup cache, and proof-carrying counter ledger/index still grow
cubically with token count. Large-file readiness is unproved, and memory
optimization remains necessary.

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

`StructureJudgment.lean` supplies the independent declarative side of
structural validation. Its applicability relation covers all 26 diagnostic
constructors represented by `MSS0001`–`MSS0020`; its structural-acceptance
judgment is proved equivalent to the absence of an applicable diagnostic.
Duplicate, source-span, and least-span primitives are exact. Import, export,
and pragma families have local exactness and top-level soundness. Signature
families are locally exact and sound at every reached signature. Fallback and
constructor declarations also have exact local specifications and soundness,
including a fuel-free grouped-unit return check. All six recursive fuel
collectors are sound for arbitrary fuel. Structural paths are bounded by the
module AST measure, so the executable list and declarative applicability agree
in both directions. Canonical reports are duplicate-free and ordered, and
validator success is equivalent to structural acceptance. Formal resource
accounting and the certified frontend connection remain. Location
certification is complete: the executable inventory, token order, parser-span
geometry, and assembly-location facts compose into
`Parses.everyLocationValid` for every successful parse. Exact token
correspondence is the remaining source-fidelity proof.

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

- implement the separate fast parser and prove exact result equality with the
  chart reference, including its stated parser work bound;
- prove the quadratic `structureBound` sufficient for the exact six-family
  structural ledger; every family is already counted, both canonical-list
  passes have insertion-square bounds, and `astNodeMeasure` is related to a
  concrete enumeration of the full AST carrier;
- prove exact token correspondence for successful parses, including retained
  leaves, grouping, literal spelling, and the absence of parser normalization;
- connect the already certified structural phase to `CertifiedParsedModule`
  and the file-only frontend with the specified diagnostic precedence;
- reduce the cubic evidence/cache/counter memory cost and validate
  progressively larger inputs;
- define and implement reachable-workspace parsing;
- accept and implement the resolver boundary;
- connect source checking and elaboration to declarative judgments; and
- publish new version/profile/wire/Oracle contracts through a separate ADR.

Until those gates close, M2b remains the published parser reference and M2c
remains an internal, formally justified but performance-limited parser kernel.
