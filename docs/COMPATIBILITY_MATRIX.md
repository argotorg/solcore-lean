# Haskell/Rust compatibility matrix

This document is an evidence ledger for tracking differences between existing
implementations; it is not the language specification itself. Agreement between
existing implementations is not specification conformance if their behavior
conflicts with the declarative Lean specification or an Accepted ADR.

## M0 comparison baseline

| Target | Revision / digest |
| --- | --- |
| Haskell `argotorg/solcore` | `1d490d8bb5f374356f06e0720655496482eb1fb4` |
| Rust `argotorg/solcore-rs` | `38f4778ea461edfe59106bdb1f9f08c3307b0fc0` |
| canonical upstream std | `3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22` |
| Rust std Git tree | `c58489d2d544b314b7fa843b331062f6f5129655` |
| Rust compatibility std snapshot | `c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430` |

The standard library currently vendored by Rust is not identical to the canonical
upstream standard library. Both implementations must therefore be aligned to the
same snapshot before comparison. If a historical parity TSV was generated at a
different revision, with the legacy solver, or with dispatch disabled, its
verdicts must not be reused as results for this baseline.

The tabled, dispatch, and Osaka settings in metadata constitute the
`targetComparisonProfile` for rerunning the comparison; they do not constitute an
executed baseline of the current corpus under those settings. The external Yul
compiler target is also not yet pinned for either Haskell or Rust.

## Implementation-status vocabulary

- `conformant`: agrees with the normative result under the same profile
- `divergent`: differs from the normative result under the same profile
- `mode-dependent`: varies with settings such as solver mode
- `phase-dependent`: varies with the reached phase, such as frontend,
  specialization, or dispatch
- `partial`: implements only some required paths
- `unsupported`: does not implement the required paths
- `unverified`: has not yet been reproduced against the baseline

## Candidate decisions and historical evidence

All implementation columns below remain `unverified` until the corpus is rerun at
the current revisions with the tabled solver, the same standard library, and the
same phase. The rightmost column contains investigation hypotheses from an older
baseline, not current results.

| Rule ID | ADR direction or candidate | Current Haskell | Current Rust | Old-baseline observation |
| --- | --- | --- | --- | --- |
| `syntax.for-post-let` | candidate: allow the same form as `init` | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.call-non-function` | reject values that are neither functions nor invokables | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.explicit-closure` | admit correct invokable evidence | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.instance-member` | candidate: reject an inconsistent instantiated signature | unverified | unverified | Haskell divergent / Rust conformant |
| `solver.recursive-table-reuse` | accept when the tabled solver can solve it | unverified | unverified | Haskell mode-dependent / Rust conformant |
| `staging.runtime-to-comptime` | candidate: reject during the staging phase | unverified | unverified | both phase-dependent |
| `contract.main-arity` | source runtime `main` has zero parameters | unverified | unverified | Haskell divergent / Rust conformant |
| `contract.dispatch-imports` | candidate: reject failed dispatch dependency resolution | unverified | unverified | both phase-dependent |
| `abi.word` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.bool-input` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.user-adt` | unsupported until layout and codec are decided | unverified | unverified | Haskell partial / Rust rejection |
| `abi.unknown-type` | structured outcome without a crash | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.duplicate-signature` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.selector-collision` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.nested-tuple-boundary` | unsupported until decided | unverified | unverified | both flatten the top boundary |

`conformant rejection` means that the existing Rust compiler rejects safely. The
Lean Oracle returns `unsupported` for a feature whose meaning is undefined by the
language profile, so this term does not imply that the wire-level verdict names
are identical.

## M1a source-inspection evidence

The following table does not make either compiler normative. It records
implementation paths inspected in relation to the decisions in ADR-0009 and is
not an end-to-end conformance run under the current profile.

| Rule | Haskell evidence | Rust evidence | ADR-0009 |
| --- | --- | --- | --- |
| let binder scope | introduces the binder after resolving the initializer | introduces the binder after resolving the initializer | evaluate the initializer in the current environment, then prepend it at index 0 |
| eager operand order | lowers to Hull/Yul in source order | lowers to Yul in source order | future primitives evaluate left to right; none are introduced in M1a |
| conditional branch | some paths precompute both branches | executes the selected branch inside a `switch` | condition first, selected branch only |
| word representation | applies a `2^256` mask when converting to a word | 256-bit modulo value | Core values are range-bounded; source modulo belongs to M2 |

Because the Haskell conditional path can execute effects from an unselected
branch, it is classified as a candidate `implementation defect`. End-to-end
differential classification is deferred until M2 can elaborate an M1a Core
fixture from source.

## Historical std external ABI evidence

The following table summarizes path inspection against an older snapshot; it is
not a conformance result for the current canonical six-file bundle. Before a
public source type is classified as supported, ABI metadata, canonical input
signature, calldata decoding, and result encoding must all be audited again
against the current bundle.

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
| user ADT | generic helper present | consistency with structural signature unverified | consistency with generic codec unverified | unsupported |

`complete` in this table is historical evidence. It does not establish
conformance with the current canonical standard library, Lean M0/M1, or the
target comparison profile.

## Comparison requirements

- Use tabled mode for class resolution in both implementations.
- Enable dispatch for contract fixtures in both implementations.
- Dispatch may be disabled for isolated frontend fixtures, but the reached phase
  must be recorded in the verdict.
- Do not conflate frontend-only comptime failures with results after
  specialization.
- Use standard-library snapshots with identical content.
- Execute bytecode with the same EVM revision, initial state, and transaction
  sequence.
- Until the external Yul compiler target is pinned for both implementations,
  contract results obtained through Yul are not conformance evidence for the
  current baseline.
- Classify timeouts and bounded solver failures as inconclusive rather than
  counting them as rejection differences.
- Do not include Rust-only negative import fixtures in the language-difference
  count.

## Update rules

When a change adds or resolves a difference, perform all of the following
together.

1. Record the baseline and execution configuration.
2. Preserve a minimal witness that exhibits exactly one difference.
3. Classify it as `language difference`, `solver mode`, `phase`,
   `shared std defect`, or `implementation defect`.
4. Create an ADR if a normative decision is required.
5. After resolution, remove the allowance and add both a regression test for the
   corrected implementation and a Lean conformance test.
