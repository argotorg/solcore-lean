# Feature matrix

This is the human-readable implementation ledger. It does not enable a profile
or alter a published protocol.

Status meanings:

- complete: executable behavior and the required proof boundary exist;
- active: implementation is currently being developed;
- planned: the feature has an implementation order but no complete code;
- blocked: a semantic decision or prerequisite is missing;
- frozen: retained at a versioned boundary with no active expansion;
- unsupported: the selected public profile deliberately has no meaning for it.

## Published and stable features

| Feature | Specification | Implementation and proof | Published | Syntax coupling |
| --- | --- | --- | --- | --- |
| Version and profile separation | Normative | Complete | Oracle v1 and later | None |
| Verdict categories | Normative | Complete | Oracle v1 and later | None |
| Core unit, bool, word | Normative | Complete | Oracle v2/v3 | None |
| Immutable Core binding | Normative | Complete | Oracle v2/v3 | None |
| Core conditional | Normative | Complete | Oracle v2/v3 | None |
| M1c primitive subset | Normative | Complete | Oracle v3 | None |
| Surface v1 parser | Normative | Complete | Oracle v4 | High; frozen |

The M1c primitive subset contains boolean and word negation, modular word
addition/subtraction/multiplication, total unsigned division/modulo, word
equality and greater-than, bitwise operations, and bounded logical shifts.

## Active Semantic Core work

| Feature | Decision | Lean status | Required proof boundary | Syntax coupling |
| --- | --- | --- | --- | --- |
| Binary products and projections | ADR-0019 Accepted | Complete | typing/checker equivalence, CEK/big-step correspondence, safety, sufficient fuel, and old-wire rejection complete | None |
| Functions and application | Direction accepted | Planned | typing, closure evaluation, application order, machine and safety | None |
| Lexical closures | Direction accepted | Planned with functions | capture typing, environment correspondence, invocation | None |
| Recursion and divergence | Decision incomplete | Blocked | divergence/resource model and replacement for finite termination | None |
| Mutable locals and assignment | Direction accepted | Planned | cell identity, evaluation order, state typing, preservation | None |
| Sum values | Direction accepted | Planned | injections, elimination, value typing, safety | None |
| User algebraic data | Direction accepted | Planned | constructor identity and value algebra | Low |
| Direct pattern matching | Direction accepted | Planned | matching order, exhaustiveness, failure policy | Low |
| Additional conversions and primitives | Per-feature decisions needed | Planned | total application and typed results | None |

## Static semantics after Core

| Feature | Status | Missing work | Syntax coupling |
| --- | --- | --- | --- |
| Abstract resolved-name language | Planned | structured identities, declarations, occurrences, scopes | Low |
| Source type checking | Planned after resolved IR | type and effect rules over abstract identities | Medium |
| Parametric polymorphism | Planned | type application and preservation | Low |
| Tabled class resolution | Planned | evidence language, finite search, inconclusive boundary | Low |
| Comptime/runtime staging | Blocked | staging decision and effect rules | Low |
| Surface-to-Resolved adapter | Frozen | wait for a stable Surface version | High |
| Surface-to-Core elaboration | Frozen | adapter plus type/effect/stage preservation | High |

## Contract and runtime semantics

| Feature | Status | Missing decision or implementation | Syntax coupling |
| --- | --- | --- | --- |
| Contract entry | Planned | return, payability, fallback, constructor rules | Low |
| Explicit runtime state | Planned | accounts, frames, transactions, balances | None |
| Revert and rollback | Planned | nested rollback and surviving observation policy | None |
| Storage | Blocked | storage-layout ADR | Low |
| External calls and creation | Planned | host transition and call-depth rules | None |
| Logs and canonical observations | Planned | value schemas and normalization | None |
| ABI support rule | Planned | complete metadata/signature/decode/encode path | Medium |
| Selector collision rejection | Planned | canonical signatures and collision executor | Low |
| EVM revision policy | Direction accepted | execution implementation absent | None |
| Gas observation | Deferred | fork and gas schedule | None |
| Inline Yul execution | Unsupported | separate future language boundary | High |

## Frozen frontend snapshot

| Internal component | State at freeze |
| --- | --- |
| Workspace identity and validation | Complete and proved |
| Multi lexer | Complete for the frozen token language |
| Multi chart parser | Total selected result and soundness for the frozen grammar |
| Structural validator | Complete executable/declarative correspondence |
| Source locations | Parser-wide validity and nesting proof complete |
| Retained tokens | Exact correspondence complete for all frozen grammar rules |
| Certified one-file frontend | Complete internal proof-carrying result |
| Fast parser | Finite schedule and terminal base only; full executor incomplete |
| Structural identity | Accepted design, no implementation |
| Module/name resolution | Proposed design, no implementation |

No frozen row is a promise that the same AST or grammar will be used by the
next Surface version.

## Public compatibility rule

Semantic Core v1, Semantic Core v2, and Surface v1 are closed algebras.
Internal Core vNext values and expressions must fail their old wire projection.
Publication occurs only through a new additive version.
