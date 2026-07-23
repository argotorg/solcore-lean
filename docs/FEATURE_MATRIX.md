# Feature matrix

This document tracks the scope of the Solcore specification and the
implementation stages of `solcore-lean`. The declarative Lean specification and
Accepted ADRs are authoritative for semantic details; this table does not
define new semantics by itself.

## Status

Specification status:

- `directionAccepted`: an ADR has established the design direction, but the
  rules and observations are not yet complete
- `normative`: all declarative rules, observations, and conformance conditions
  are normatively defined
- `proposed`: not yet decided and therefore not enabled in a normative profile
- `deferred`: not specified until a later milestone
- `unsupported`: intentionally has no semantics in the current language version

Lean status:

- `implemented`: the decision procedure, correspondence proof, and conformance
  tests are complete
- `partialSupport`: only part is implemented, and queries requiring the entire
  feature do not yet succeed
- `planned`: scheduled for the specified milestone
- `blocked`: must not be implemented until an additional ADR is Accepted
- `unsupported`: the Oracle explicitly returns `unsupported`

## Matrix

| Feature ID | Description | Specification status | Lean status | Milestone | Basis |
| --- | --- | --- | --- | --- | --- |
| `meta.versioning` | separation of language version, profile, and baseline | normative | implemented | M0 | ADR-0001 |
| `meta.verdicts` | separation of the six language verdicts from protocol errors | normative | implemented | M0 | ADR-0003 |
| `meta.observation` | versioned observation envelope | directionAccepted | partialSupport | M0 | ADR-0008 |
| `coreUnit` | unit type, literal, value, typing, and evaluation | normative | implemented | M1b | ADR-0010 |
| `coreBool` | bool type, literal, value, typing, and evaluation | normative | implemented | M1b | ADR-0010 |
| `coreWord` | bounded 256-bit word type, literal, and value; excludes operations | normative | implemented | M1b | ADR-0010 |
| `corePrimitives` | aggregate feature including primitive operations | directionAccepted | partialSupport | M1 | ADR-0009 |
| `core.function` | function definition, application, and return | directionAccepted | planned | M1 | ADR-0002, ADR-0005 |
| `coreImmutableLet` | initialized immutable de Bruijn binding | normative | implemented | M1b | ADR-0010 |
| `core.let` | aggregate feature for source-level local bindings | directionAccepted | partialSupport | M1 | ADR-0009 |
| `core.assignment` | local assignment | directionAccepted | planned | M1 | ADR-0002 |
| `coreConditional` | condition-first, selected-branch-only conditional | normative | implemented | M1b | ADR-0010 |
| `core.if` | aggregate feature for source-level conditionals | directionAccepted | partialSupport | M1 | ADR-0009 |
| `core.product` | product/tuple value | directionAccepted | planned | M1 | ADR-0002 |
| `core.sum` | sum value | directionAccepted | planned | M1 | ADR-0002 |
| `core.adt` | user-defined algebraic data type | directionAccepted | planned | M1 | ADR-0002 |
| `core.match` | direct pattern matching | directionAccepted | planned | M1 | ADR-0002 |
| `core.lambda` | lexical closure | directionAccepted | planned | M1 | ADR-0002, ADR-0005 |
| `syntax.for-post-let` | `let` in a `for` post clause | proposed | blocked | M2 | requires re-verification against the current baseline |
| `modules.import-export` | modules, imports, and exports | proposed | blocked | M2 | requires a shadowing ADR |
| `types.polymorphism` | parametric polymorphism | directionAccepted | planned | M2 | ADR-0002 |
| `classes.tabled` | tabled class resolution and evidence | directionAccepted | planned | M2 | ADR-0004 |
| `staging.comptime` | comptime/runtime staging | proposed | blocked | M2 | requires a staging ADR |
| `contracts.main` | zero-argument source runtime entry point | directionAccepted | planned | M3 | ADR-0005 |
| `contracts.dispatch` | generated external dispatch | directionAccepted | blocked | M3 | ADR-0006 |
| `abi.support-rule` | completeness of metadata/signature/decode/encode | directionAccepted | planned | M3 | ADR-0006 |
| `abi.uint256` | external `uint256` | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.address` | external `address` | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.bytes32` | external `bytes32` | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.string` | external `memory(string)` | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.bytes` | external `memory(bytes)` | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.unit` | external unit | proposed | planned | M3 | requires a new audit of the current standard library |
| `abi.word` | external ABI for source `word` | unsupported | unsupported | M3 | insufficient standard-library evidence |
| `abi.bool-input` | boolean parameter decoding/signature | unsupported | unsupported | M3 | insufficient standard-library evidence |
| `abi.user-adt` | external ABI for user ADTs | unsupported | unsupported | M3 | ADR-0006 |
| `abi.nested-tuple` | wire mapping for nested tuple boundaries | proposed | blocked | M3 | requires a tuple ABI ADR |
| `abi.selector-collision` | pre-generation rejection of signature/selector collisions | directionAccepted | planned | M3 | ADR-0006 |
| `runtime.storage` | concrete storage layout and operations | deferred | blocked | M3 | requires a layout ADR |
| `runtime.revert` | revert and state rollback | directionAccepted | planned | M3 | ADR-0008 |
| `runtime.external-call` | call traces and external state transitions | proposed | planned | M3 | ADR-0008 |
| `assembly.inline-yul` | inline Yul/EVM primitive | deferred | unsupported | M4 | ADR-0002 |
| `observation.gas` | fork-pinned gas observation | deferred | unsupported | M4+ | ADR-0008 |

## Rules for profile inclusion

- `known` means only that a stable feature ID exists; it does not mean that the
  specification is complete.
- Only `normative` features may appear in `enabledFeatures`.
- A query may succeed only when every feature it requires is both `enabled` and
  `implemented`. Therefore, the invariant
  `implemented ⊆ enabled ⊆ normative ⊆ known` must hold.
- A query requiring a feature whose status is `directionAccepted`, `proposed`,
  `deferred`, or `unsupported` returns `unsupported`.
- `partialSupport` maintains a separate allowlist of supported types and
  operations; it does not make the entire feature `enabled` or `implemented`.
- A feature status change must update the compatibility matrix and any required
  ADRs in the same change.
