# Feature matrix

This document is the human-readable implementation ledger for `solcore-lean`.
Accepted ADRs and the declarative Lean definitions remain authoritative; this
matrix records what is published, what exists only as an internal kernel, and
what is still missing.

## How to read the status columns

Specification status:

- `directionAccepted`: an ADR fixes the direction, but the complete rules are
  not yet normative;
- `normative`: the declarative rules and conformance conditions are complete;
- `proposed`: a decision is still under review;
- `deferred`: intentionally left for a later milestone; and
- `unsupported`: intentionally has no semantics in the current version.

Lean status for profile features:

- `implemented`: executable behavior, correspondence proofs, and conformance
  tests are complete for the published boundary;
- `partialSupport`: only the named subset is complete;
- `planned`: implementation has not reached the feature;
- `blocked`: implementation must wait for an Accepted decision or prerequisite;
  and
- `unsupported`: the Oracle explicitly returns `unsupported`.

Internal M2 components use `complete`, `partial`, `design only`, and `not
started`. These labels do **not** enable a profile feature or change a wire
protocol.

## Published profiles

| Profile | Language | Scope | Enabled features | Current role |
| --- | --- | --- | --- | --- |
| `core-m1c-v1` | `solcore/0.1.0-draft.3` | Core | the five M1b features plus four M1c primitive features | closed Core checking and evaluation through Oracle v3 |
| `frontend-m2b-v1` | `solcore/0.1.0-draft.4` | frontend | `surfaceGrammar` only | closed single-file parse-only observations through Oracle v4 |

The profiles are complementary. The frontend profile does not inherit Core
features, and neither profile exposes the internal M2c workspace or Multi
Surface work.

## Normative and planned feature matrix

| Feature ID | Description | Specification status | Lean status | Milestone | Basis |
| --- | --- | --- | --- | --- | --- |
| `meta.versioning` | separation of language version, profile, and baseline | normative | implemented | M0 | ADR-0001 |
| `meta.verdicts` | six language verdicts are distinct from protocol errors | normative | implemented | M0 | ADR-0003 |
| `meta.observation` | versioned observation envelope | directionAccepted | partialSupport | M0 | ADR-0008 |
| `coreUnit` | unit type, literal, value, typing, and evaluation | normative | implemented | M1b | ADR-0010 |
| `coreBool` | bool type, literals, values, typing, and evaluation | normative | implemented | M1b | ADR-0010 |
| `coreWord` | range-checked 256-bit word type, literal, and value | normative | implemented | M1b | ADR-0010 |
| `coreImmutableLet` | initialized immutable de Bruijn binding | normative | implemented | M1b | ADR-0010 |
| `coreConditional` | condition-first, selected-branch-only conditional | normative | implemented | M1b | ADR-0010 |
| `corePrimitives` | aggregate primitive family; only the M1c subset is complete | directionAccepted | partialSupport | M1 | ADR-0009, ADR-0011 |
| `coreBoolNot` | total boolean negation | normative | implemented | M1c | ADR-0011 |
| `coreWordArithmetic` | modular add/subtract/multiply and total unsigned divide/modulo | normative | implemented | M1c | ADR-0011 |
| `coreWordComparison` | word equality and unsigned greater-than | normative | implemented | M1c | ADR-0011 |
| `coreWordBitwise` | 256-bit not/and/or/xor and bounded logical shifts | normative | implemented | M1c | ADR-0011 |
| `core.function` | function definition, application, and return | directionAccepted | planned | M1 | ADR-0002, ADR-0005 |
| `core.let` | aggregate source-level local-binding feature | directionAccepted | partialSupport | M1 | ADR-0009 |
| `core.assignment` | mutable local assignment | directionAccepted | planned | M1 | ADR-0002 |
| `core.if` | aggregate source-level conditional feature | directionAccepted | partialSupport | M1 | ADR-0009 |
| `core.product` | product/tuple values | directionAccepted | planned | M1 | ADR-0002 |
| `core.sum` | sum values | directionAccepted | planned | M1 | ADR-0002 |
| `core.adt` | user-defined algebraic data types | directionAccepted | planned | M1 | ADR-0002 |
| `core.match` | direct pattern matching | directionAccepted | planned | M1 | ADR-0002 |
| `core.lambda` | lexical closures | directionAccepted | planned | M1 | ADR-0002, ADR-0005 |
| `surfaceGrammar` | published M2b lexer, restricted Surface syntax, parser, spans, comments, and diagnostics | normative | implemented | M2b | ADR-0012, ADR-0013 |
| `syntax.for-post-let` | `let` in a `for` post clause | proposed | blocked | M2 | requires re-verification against the current baseline |
| `modules.import-export` | module graph, imports, exports, and lexical resolution | proposed | blocked | M2c | ADR-0017 is Proposed; syntax recognition alone is not resolution |
| `types.polymorphism` | parametric polymorphism | directionAccepted | planned | M2 | ADR-0002 |
| `classes.tabled` | tabled class resolution and evidence | directionAccepted | planned | M2 | ADR-0004 |
| `staging.comptime` | comptime/runtime staging | proposed | blocked | M2 | requires a staging ADR |
| `contracts.main` | zero-argument source runtime entry point | directionAccepted | planned | M3 | ADR-0005 |
| `contracts.dispatch` | generated external dispatch | directionAccepted | blocked | M3 | ADR-0006 |
| `abi.support-rule` | complete metadata/signature/decode/encode path | directionAccepted | planned | M3 | ADR-0006 |
| `abi.uint256` | external `uint256` | proposed | planned | M3 | requires a current standard-library audit |
| `abi.address` | external `address` | proposed | planned | M3 | requires a current standard-library audit |
| `abi.bytes32` | external `bytes32` | proposed | planned | M3 | requires a current standard-library audit |
| `abi.string` | external `memory(string)` | proposed | planned | M3 | requires a current standard-library audit |
| `abi.bytes` | external `memory(bytes)` | proposed | planned | M3 | requires a current standard-library audit |
| `abi.unit` | external unit | proposed | planned | M3 | requires a current standard-library audit |
| `abi.word` | external ABI for source `word` | unsupported | unsupported | M3 | insufficient standard-library evidence |
| `abi.bool-input` | boolean parameter decoding/signature | unsupported | unsupported | M3 | insufficient standard-library evidence |
| `abi.user-adt` | external ABI for user ADTs | unsupported | unsupported | M3 | ADR-0006 |
| `abi.nested-tuple` | wire mapping for nested tuple boundaries | proposed | blocked | M3 | requires a tuple ABI ADR |
| `abi.selector-collision` | pre-generation rejection of signature/selector collisions | directionAccepted | planned | M3 | ADR-0006 |
| `runtime.storage` | concrete storage layout and operations | deferred | blocked | M3 | requires a layout ADR |
| `runtime.revert` | revert and state rollback | directionAccepted | planned | M3 | ADR-0008 |
| `runtime.external-call` | call traces and external state transitions | proposed | planned | M3 | ADR-0008 |
| `assembly.inline-yul` | inline Yul/EVM semantics | deferred | unsupported | M4 | ADR-0002 |
| `observation.gas` | fork-pinned gas observation | deferred | unsupported | M4+ | ADR-0008 |

## Internal M2 implementation ledger

These components are prerequisites for a future multi-file frontend. None is
published by Oracle v4 or enabled by `frontend-m2b-v1`.

| Internal component | Design status | Lean status | What is established now | Still outside the boundary |
| --- | --- | --- | --- | --- |
| Workspace identity and validation | ADR-0014 Accepted | complete | canonical ASCII `.solc` paths; structured library/source/module IDs; pure validation; all eight error families; soundness, completeness, uniqueness, lookup, measure, and permutation invariants | standard-bundle assembly, parsing, resolution, wire format |
| Multi source, token, and AST algebra | ADR-0015 Accepted | implemented | `SourceId`-owned UTF-8 byte spans; 30 hard keywords, 2 contextual keywords, 4 pragma names, 40 symbols; recovery-free source-preserving `ParsedModuleV1`; imports, exports, declarations, statements, patterns, types, and expressions | no external schema or profile |
| Multi lexer | ADR-0015 Accepted | complete for the implemented boundary | pure total maximal-munch lexer; nested comments; exact strings and UTF-8 spans; opaque balanced assembly slices; declarative lexical soundness/completeness; explicit sufficient bound | no workspace-wide traversal |
| Multi grammar and parser core | ADR-0015 Accepted | implemented | 75 grammar rules, 736 EBNF sites, 1,039 production/action IDs; typed reductions; contextual chart; closed parse diagnostics; source-backed `Parses` judgment | separate fast executor and work bound, final certified wrapper, and published parser API |
| Static parser totality certificate | ADR-0015 Accepted | complete | a kernel-checked table covers all 2,375 fixed dotted-rank rows; it closes bounded rank search without `native_decide` or extra axioms | certificate is grammar-specific and internal |
| Unconditional file-only frontend | ADR-0015 Accepted | implemented and sound | `executeObservedContextualFrontend` always selects lexical failure, parse failure, or a parsed module; successful and diagnostic branches satisfy their declarative judgments | it cannot emit or check structural diagnostics; it is not an Oracle query |
| Structural acceptance pass | ADR-0015 Accepted | executable pass, logical correspondence, and resource bound complete | all 20 structural conditions and 26 diagnostic forms are covered; `diagnosticCandidates` membership is exactly `Applies`; module-derived traversal fuel is sufficient; canonical reports are sorted and duplicate-free; `validateStructure` succeeds exactly for `StructurallyAccepts` modules; all six charged families have exact accounting and their combined total satisfies the fixed quadratic bound | final exact-token closure, certified wrapper, and publication remain |
| Multi source-location evidence | ADR-0015 Accepted | parser-wide proof complete | one executable inventory covers all 54 located AST carriers and 12 retained raw spans; token order, parser-span containment, and assembly-internal facts compose into `Parses.everyLocationValid`, so every successful parse has valid and properly nested locations | final exact-token closure, certified wrapper, and publication remain |
| Canonical six-file parser gate | ADR-0015 Accepted | partial | canonical raw bytes, metadata, strict UTF-8 round trip, lexer fingerprints, and lexer success are checked | kernel-checked parsing and structural acceptance of all six files are not yet present |
| Structural syntax identity | ADR-0016 Accepted | design only | role-tagged address, scope, prepared-module, index, and identity rules are fixed by the ADR | no `Surface/Multi/Structural` implementation or tests exist yet |
| Module and lexical resolution | ADR-0017 Proposed | blocked / not started | proposed graph, interface fixed point, scope, intrinsic, and standard verification rules are documented | no `Solcore/Resolution` code, resolver theorem, or resolve query exists |
| Multi wire and publication | no publication ADR | not started | none | new Surface schema, limits, profile, capabilities, Oracle query, and golden streams |

## M1c publication boundary

The four M1c feature rows denote exactly these primitive tags:

- unary: `boolNot`, `wordNot`;
- arithmetic: `wordAdd`, `wordSub`, `wordMul`, `wordDiv`, `wordMod`;
- comparison: `wordEq`, `wordGt`; and
- bitwise: `wordAnd`, `wordOr`, `wordXor`, `wordShl`, `wordShr`.

Arithmetic is modulo `2^256`; unsigned division and modulo by zero return zero.
Shifts take `(value, amount)` and return zero when `amount >= 256`. Binary
operands are evaluated exactly once, left to right. Derived `wordNe`, `wordLt`,
`wordLe`, and `wordGe` do not expand the primitive tag set.

Short-circuit boolean conjunction/disjunction, conversions, signed operations,
exponentiation, ternary modular operations, byte selection, arithmetic shift,
count-leading-zero, functions, closures, application, and return remain outside
M1c. A query needing them cannot succeed under `core-m1c-v1`.

M1c is exposed through `solcore-semantic-core/v2`, `solcore-oracle/v3`, and
`solcore-capabilities/v3`. All earlier profile arrays, digests, schemas,
capability bytes, and golden streams remain immutable.

## M2b publication boundary

[ADR-0012](adr/0012-m2a-surface-parser-kernel.md) defines the restricted
single-file parser kernel. [ADR-0013](adr/0013-m2b-surface-parser-publication.md)
publishes that exact fragment as `surfaceGrammar` under
`solcore/0.1.0-draft.4`, with `grammarVersion = 1`. Oracle v4 exposes
`solcore-surface/v1` inside `solcore-parse-result/v1` through only
`capabilities` and `parse`.

The request contains one source string and a nonempty opaque label. The label
is copied unchanged into spans and is never interpreted as a path. The parser
preserves half-open UTF-8 byte spans, comments, raw integer spelling, grouping,
calls, and keyword conditionals for the published restricted fixture. A
`sourceBytes` overflow is `inconclusive`, not `rejected`.

The internal Multi frontend is additive and separate. It uses structured
`SourceId`s and a much larger AST, but does not modify Surface v1, Oracle v4,
or the meaning of `surfaceGrammar`.

## Profile inclusion rules

- `known` means only that a stable feature ID exists.
- Only `normative` features may appear in `enabledFeatures`.
- A query succeeds only when every required feature is enabled and implemented;
  therefore `implemented ⊆ enabled ⊆ normative ⊆ known`.
- A query requiring a `directionAccepted`, `proposed`, `deferred`, or
  `unsupported` feature returns `unsupported`.
- `partialSupport` maintains an explicit allowlist; it does not make the
  aggregate feature implemented.
- Internal implementation progress does not change a profile. Publication
  requires the feature row, language/profile version, schemas, capabilities,
  limits, and golden artifacts to change together under an Accepted ADR.
