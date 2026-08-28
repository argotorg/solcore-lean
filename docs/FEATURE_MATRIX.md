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

## Internal Semantic Core roadmap

| Feature | Decision | Lean status | Required proof boundary | Syntax coupling |
| --- | --- | --- | --- | --- |
| Binary products and projections | ADR-0019 Accepted | Complete | typing/checker equivalence, CEK/big-step correspondence, safety, sufficient fuel, and old-wire rejection complete | None |
| Functions and application | ADR-0020 Accepted | Complete | typing/checker equivalence, ordered application, correspondence, logical-relations totality, safety, and old-wire rejection complete | None |
| Lexical closures | ADR-0020 Accepted | Complete | capture typing, environment correspondence, invocation, and fault exclusion complete | None |
| Sum values | ADR-0021 Accepted | Complete | injections, exhaustive elimination, checker equivalence, CEK correspondence, logical-relations totality, safety, and old-wire rejection complete | None |
| First-order local cells | ADR-0022 Accepted | Complete | explicit store threading, checker correspondence, CEK/big-step correspondence, store-indexed safety, sufficient fuel, and old-wire rejection complete | None |
| Named algebraic data | ADR-0023 Accepted | Complete | whole-table validity, nominal constructor typing, recursive and mutually recursive finite-value safety, totality, sufficient fuel, diagnostics, and old-wire rejection complete | None |
| Direct normalized matching | ADR-0023 Accepted | Complete | constructor-order exhaustiveness, payload binding, selected-branch store threading, CEK/big-step correspondence, safety, exact fuel, and diagnostics complete | None |
| Boolean/word conversions | ADR-0024 Accepted | Complete | derived-expression typing and inference, exact values, exactly-once store-threaded evaluation, weakening, and version-boundary tests complete | None |
| Word zero test | ADR-0025 Accepted | Complete | derived word-to-word expansion, typing, inference, zero/nonzero and store-threaded evaluation, weakening, effects, fuel, and version-boundary coverage complete | None |
| Short-circuit boolean operators | ADR-0026 Accepted | Complete | expansion, typing, inference, four store-threaded branches, selected effects/faults, exact fuel, weakening, and exact v1/v2 wire projection complete | None |
| Word nonzero test | ADR-0027 Accepted | Complete | canonical expansion, typing, inference, general and zero/nonzero store evaluation, weakening, exactly-once effects, exact fuel and v1/v2 boundaries complete | None |
| Word comparison flags | ADR-0028 Accepted | Complete | named expansions, typing, inference, general and four-case store evaluation, weakening, effects, exact fuel, bool preservation, and v1/v2 boundaries complete | None |
| Renaming and environment insertion | ADR-0029 Accepted | Complete | syntax renaming, typing preservation, value/environment/store relations, full evaluation simulation, CellPayload exactness, head-insertion word theorem, and static/dynamic tests complete | None |
| Derived boolean word comparisons | ADR-0030 Accepted | Complete | four expansion/typing/infer/rename/weaken APIs, untyped wordNe/wordLe and typed wordLt/wordGe store evaluation, eight truth cases, values/types/fuel/fault/effects, v1 rejection, and exact v2 projection/round-trip tests complete | None |
| Derived word comparison flags | ADR-0031 Accepted | Complete | four builders and expansion/type/infer/rename/weaken APIs, four general and eight case evaluations, value/type/fuel/fault/effect tests, v1 rejection, and exact v2 projection/round trips complete | None |
| Derived-builder arbitrary renaming laws | ADR-0032 Accepted | Complete | exactly eight laws in their owning modules, rename_boolToWord relocation, swap01 free-variable goldens, and three-family runtime-environment regressions complete | None |
| Direct unary primitive interface | ADR-0033 Accepted | Complete | named raw boolNot/wordNot APIs, zero/maximum/involution facts, exact fuel, fault/effect/store tests, v1 rejection, and exact v2 projection/round trips complete | None |
| Totalized unsigned division and modulo interface | ADR-0034 Accepted | Complete | four Word, two apply, and six evaluation theorems; ordered zero-divisor effects/faults, exact fuel, and v1/v2 regressions complete | None |
| Bounded logical shift interface | ADR-0035 Accepted | Complete | six Word, two apply, and six evaluation theorems; value-left/shift-right boundaries, effects, exact fuel, and v1/v2 plus JSON round trips complete | None |
| Modular word arithmetic interface | ADR-0036 Accepted | Complete | eight Word, three apply, and three evaluation theorems; normal/wrapped values, strict order, effects/fuel, and v1/v2 Core plus JSON round trips complete | None |
| Binary bitwise logic interface | ADR-0037 Accepted | Complete | nine Word, three apply, and three evaluation theorems; masks, strict order, effects/fuel, and v1/v2 Core plus JSON round trips complete | None |
| Direct word comparison interface | ADR-0038 Accepted | Complete | two apply and six evaluation theorems; boolean equality and strict unsigned greater-than with values, types, ordered faults/effects, exact fuel, and v1/v2 Core/JSON regressions complete | None |
| Word leading-zero count | ADR-0039 Accepted | Complete | internal UnaryOp.wordClz and Word.clz; five Word, one apply, and five evaluation theorems; value/type/fault/effect/fuel tests and frozen v1/v2 rejection complete | None |
| Word byte selection | ADR-0040 Accepted | Complete | internal BinaryOp.wordByte and big-endian Word.byteAt; five Word, one apply, and three evaluation theorems; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Arithmetic right shift | ADR-0041 Accepted | Complete | internal BinaryOp.wordSar and two's-complement Word.shiftArithmeticRight; five Word, one apply, and five evaluation theorems; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Modular exponentiation | ADR-0042 Accepted | Complete | internal BinaryOp.wordPow and proved square-and-multiply Word.pow; eight Word, one apply, and five evaluations; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Signed word greater-than | ADR-0043 Accepted | Complete | exact eleven-theorem boolean wordSgt basis; sign boundaries, types, ordered faults/effects, exact fuel, and frozen v1/v2 plus v2-op rejection complete; audit clean | None |
| Derived signed word less-than | ADR-0044 Accepted | Complete | effect-safe nested-let wordSlt; five static and five evaluation theorems; values/types/fault order/effects/store/fuel and frozen v1/v2 rejection complete; audit clean | None |
| Signed word comparison flags | ADR-0045 Accepted | Complete | two exact builders; ten static and ten evaluation laws; sign/value/type/fault/effect/store/fuel and frozen v1/v2 rejection complete; audit clean | None |
| Signed non-strict word comparisons | ADR-0046 Accepted | Complete | derived boolean wordSle and wordSge; exact twenty-theorem interface; sign/type/fault/effect/store/fuel and frozen-Wire regressions complete; audit clean | None |
| Word sign extension | ADR-0047 Accepted | Complete | internal index-left/value-right wordSignExtend; exact ten theorems and index/value/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Signed word division and remainder | ADR-0048 Accepted | Complete | internal dividend-left/divisor-right wordSdiv and wordSmod; exact fourteen theorems and sign/zero/minimum/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Signed non-strict comparison flags | ADR-0049 Accepted | Complete | derived wordSleFlag and wordSgeFlag; exact twenty theorems and canonical/truth/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Ternary modular arithmetic | ADR-0050 Accepted | Complete | internal wordAddMod/wordMulMod and Expr.ternary; full-precision reduction, exact fourteen focused theorems, generic static/safety support, exact fuel, and frozen v1/v2 rejection complete; audit clean | None |
| Further Core conversions and primitives | Per-feature decisions needed | Planned | separate closed decisions, total application, and typed results | None |
| Recursion and divergence | Decision incomplete | Blocked | divergence/resource model and replacement for finite termination | None |

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
| Canonical runtime scalar observations | Complete | Strict Bytes/Address/Word text and Word big-endian bytes; exact sixteen theorems; boundary, rejection, canonicality, `Word.byteAt`, and frozen-Wire output compatibility tests complete; Wire codecs unchanged; audit clean | None |
| Contract frame halt outcomes | Complete | Parametric return/revert/trap carrier and four observations; exactly six laws and 10 executable runtime assertions cover empty versus absent payloads, zero-octet preservation, distinct trap reasons, and constructor boundaries; no state or publication; audit clean | None |
| Strict Address↔Word bridge | Complete | Lossless widening and strict non-truncating narrowing; two definitions, exactly six axiom-free laws, and 10 runtime assertions cover zero, one, middle, maximum, and overflow rejection; no source, ABI, state, or publication; audit clean | None |
| Strict 20-byte Address representation | Complete | Two definitions, exactly six laws, and 10 runtime assertions cover leading zeros, exact width, 19/21-byte rejection, representative round trips, injectivity, and all 20 widened-Word suffix indices; no ABI, state, or publication; audit clean | None |
| Address text and byte coherence | Complete | No public executable API; 15 private helpers, exactly four public laws, and eight runtime assertions connect canonical text, exact bytes, and arbitrary-input decoder agreement; no ABI, state, or publication; audit clean | None |
| Minimal Account and WorldState carrier | Complete | Two public carriers backed only by private semantic lookup functions, eight public operations, exactly twelve laws, and twelve runtime assertions; no concrete map representation, rollback, balances, code, calls, ordering, serialization, or publication; audit clean | None |
| Frame-outcome WorldState resolution | Complete | One internal operation, exactly three constructor laws, and three runtime assertions select working/checkpoint state while leaving trap disposition open; no nested rollback, surviving effects, ABI, EVM, or publication | None |
| WorldState observational update algebra | Complete | No executable API, carrier, or instance; exactly six extensionality/overwrite/commutation laws, two compile-time examples, and four runtime assertions complete; no new state meaning or publication | None |
| WorldState storage-write algebra | Complete | No executable API, carrier, or instance; one private helper, exactly four sequential/commutation/zero-deletion laws, and four runtime assertions complete; no operational or publication decision | None |
| External-checkpoint frame run result | Complete | One public semantic carrier and one named resolver; exactly three constructor laws and three runtime assertions pair speculative working state with an outcome while checkpoint ownership remains external | None |
| Parametric frame effect journal policy | Complete | One public two-snapshot carrier and one resolver; exactly five axiom-free laws and five runtime assertions separate rollback-scoped state from an opaque surviving trace without concrete event order | None |
| Synchronized frame state/effect resolution | Complete | No new carrier, instance, or helper; one resolver, exactly five laws, and three runtime assertions select WorldState and effects from one outcome branch | None |
| Synchronized child-frame composition | Active | Proof-only; no carrier, API, instance, or helper; exactly two nested non-simp laws and two runtime assertions planned with opaque accumulated trace ownership | None |
| Contract entry | Planned | return, payability, fallback, constructor rules | Low |
| Explicit contract runtime state | Planned | accounts, frames, transactions, balances; distinct from the implemented Core-local cell store | None |
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

Semantic Core v1, Semantic Core v2, and Surface v1 are closed algebras. New Core
vNext constructors outside those algebras must fail their old wire projection.
This includes the cell forms accepted by ADR-0022 and every named-data form or
nonempty definition table accepted by ADR-0023. ADR-0024 adds no constructor:
its conversions expand into existing expressions, so each projection treats
them exactly like the corresponding handwritten expansion. Publication of any
new tag still requires a new additive version. ADR-0025 likewise adds no tag:
wire v1 rejects its primitive expansion and wire v2 projects existing forms.
