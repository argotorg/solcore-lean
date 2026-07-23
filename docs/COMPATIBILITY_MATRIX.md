# Haskell/Rust compatibility matrix

This document is an evidence ledger for tracking differences from the existing
implementations; it is not the language specification itself. Agreement between
the existing implementations does not establish conformance when their behavior
conflicts with the Lean declarative specification or an Accepted ADR.

## M0 comparison baseline

| Target | Revision / digest |
| --- | --- |
| Haskell `argotorg/solcore` | `1d490d8bb5f374356f06e0720655496482eb1fb4` |
| Rust `argotorg/solcore-rs` | `38f4778ea461edfe59106bdb1f9f08c3307b0fc0` |
| canonical upstream std | `3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22` |
| Rust std Git tree | `c58489d2d544b314b7fa843b331062f6f5129655` |
| Rust compatibility std snapshot | `c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430` |

The current Rust vendored std is not identical to the canonical upstream std.
Both implementations must therefore be aligned to the same snapshot before
comparison. A verdict from an earlier parity TSV must not be reused as a result
for this baseline when it was produced from another revision, with the legacy
solver, or with dispatch disabled.

The tabled/dispatch/Osaka settings in the metadata form the
`targetComparisonProfile` for rerunning comparisons; they are not an executed
baseline for the current corpus under those settings. The external Yul compiler
target is also not yet pinned for either Haskell or Rust.

## Implementation-status vocabulary

- `conformant`: agrees with the normative result under the same profile
- `divergent`: differs from the normative result even under the same profile
- `mode-dependent`: varies with a setting such as solver mode
- `phase-dependent`: varies with the reached phase, such as frontend,
  specialization, or dispatch
- `partial`: implements only some required paths
- `unsupported`: does not implement the required path
- `unverified`: has not been reproduced on the baseline

## Candidate decisions and historical evidence

Every implementation column below remains `unverified` until the corpus is
rerun with the current revision, tabled solver, identical std, and identical
phase. The rightmost column contains investigation hypotheses from an older
baseline, not current results.

| Rule ID | ADR direction or candidate | Current Haskell | Current Rust | Older-baseline observation |
| --- | --- | --- | --- | --- |
| `syntax.for-post-let` | candidate: permit the same form as `init` | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.call-non-function` | reject values other than functions/invokables | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.explicit-closure` | permit correct invokable evidence | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.instance-member` | candidate: reject an inconsistent instantiated signature | unverified | unverified | Haskell divergent / Rust conformant |
| `solver.recursive-table-reuse` | accept when the tabled solver can resolve it | unverified | unverified | Haskell mode-dependent / Rust conformant |
| `staging.runtime-to-comptime` | candidate: reject in the staging phase | unverified | unverified | both phase-dependent |
| `contract.main-arity` | source runtime `main` has zero parameters | unverified | unverified | Haskell divergent / Rust conformant |
| `contract.dispatch-imports` | candidate: reject failed dispatch dependency resolution | unverified | unverified | both phase-dependent |
| `abi.word` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.bool-input` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.user-adt` | unsupported until layout and codec are decided | unverified | unverified | Haskell partial / Rust rejection |
| `abi.unknown-type` | return a structured outcome without crashing | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.duplicate-signature` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.selector-collision` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.nested-tuple-boundary` | unsupported until decided | unverified | unverified | both flatten the top boundary |

`conformant rejection` means that the existing Rust compiler rejects safely.
Because the Lean oracle returns `unsupported` for a feature whose semantics are
undefined by the language profile, this term does not require the wire-level
verdict names to be identical.

## M1a source-inspection evidence

The following table records implementation paths investigated for the choices
in ADR-0009. It does not make either compiler normative and is not an end-to-end
conformance run under the current profile.

| Rule | Haskell evidence | Rust evidence | ADR-0009 |
| --- | --- | --- | --- |
| let binder scope | introduces the binder after resolving the initializer | introduces the binder after resolving the initializer | evaluates the initializer in the current environment, then adds it at index 0 |
| eager operand order | lowers to Hull/Yul in source order | lowers to Yul in source order | future primitives evaluate left to right; M1a has none |
| conditional branch | some paths precompute both branches | executes the selected branch inside a switch | condition first, selected branch only |
| word representation | applies a `2^256` mask when constructing a word | 256-bit modular value | the Core value is bounded; source modulo behavior belongs to M2 |

The Haskell conditional path can execute effects from the unselected branch and
is therefore a candidate `implementation defect`. End-to-end differential
classification is deferred until M2 can elaborate an M1a Core fixture from
source.

## M1b Oracle boundary

`solcore-oracle/v2` accepts `solcore-semantic-core/v1` directly and returns
either a type-checking result or a canonical value observation. This fixes the
boundary for generating, shrinking, and replaying fixtures within Lean. Because
the Haskell and Rust implementations do not accept this Core wire format
directly, the current matrix makes no claim of end-to-end conformance among all
three implementations.

M2 will provide the same source witness to each compiler and reach the same Core
observation through normative elaboration on the Lean side. The M1b golden
corpus serves as the standard that keeps the comparison adapter from conflating
`rejected`, `inconclusive`, `executed`, and protocol errors.

## Historical std external ABI evidence

The following table summarizes path inspection from an older snapshot; it is
not a conformance result for the current canonical six-file bundle. To classify
a public source type as supported, the ABI metadata, canonical input signature,
calldata decode, and result encode paths must all be re-audited against the
current bundle.

| Source type | Metadata/signature | Decode | Encode | Status |
| --- | --- | --- | --- | --- |
| `uint256` | yes | yes | yes | complete |
| `address` | yes | yes | yes | complete |
| `bytes32` | yes | yes | yes | complete |
| `memory(string)` | yes | yes | yes | complete |
| `memory(bytes)` | yes | yes | yes | complete |
| `()` | yes | yes | yes | complete |
| `bool` input | no | no | yes | output-only |
| primitive `word` | metadata only | no | no | unsupported |
| pair/tuple | component-dependent | component-dependent | component-dependent | partial |
| user ADT | generic helper exists | consistency with structural signature unverified | consistency with generic codec unverified | unsupported |

`complete` in this table is historical evidence; it does not imply conformance
with the current canonical std, Lean M0/M1, or the target comparison profile.

## Comparison requirements

- Align class resolution to tabled mode.
- Enable dispatch in both implementations for contract fixtures.
- Dispatch may be disabled in both implementations for isolated frontend
  fixtures, but the verdict must record that phase.
- Do not conflate frontend-only comptime failures with results after
  specialization.
- Use std snapshots with identical contents.
- Execute bytecode with the same EVM revision, initial state, and transaction
  sequence.
- Do not use contract results obtained through Yul as conformance evidence for
  the current baseline until both external Yul compiler targets are pinned.
- Treat timeouts and bounded solver failures as inconclusive rather than reject
  differences.
- Do not count Rust-only negative import fixtures as language differences.

## Update rules

A change that adds or resolves a discrepancy must perform all of the following
together:

1. Record the baseline and execution settings.
2. Preserve a minimal witness showing only that discrepancy.
3. Classify it as `language difference`, `solver mode`, `phase`,
   `shared std defect`, or `implementation defect`.
4. Create an ADR when a normative judgment is required.
5. After resolution, remove the allowance and add a regression test for the
   corrected implementation together with a Lean conformance test.
