# Haskell/Rust compatibility matrix

This document is an evidence ledger that tracks differences between existing
implementations; it is not itself the language specification. Even when the
existing implementations agree, their behavior is not considered conformant
if it conflicts with the declarative Lean specification or an Accepted ADR.

## M0 comparison baseline

| Target | Revision / digest |
| --- | --- |
| Haskell `argotorg/solcore` | `1d490d8bb5f374356f06e0720655496482eb1fb4` |
| Rust `argotorg/solcore-rs` | `38f4778ea461edfe59106bdb1f9f08c3307b0fc0` |
| canonical upstream std | `3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22` |
| Rust std Git tree | `c58489d2d544b314b7fa843b331062f6f5129655` |
| Rust compatibility std snapshot | `c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430` |

The current Rust vendored std is not identical to the canonical upstream std.
The implementations must therefore be aligned to the same snapshot before
comparison. A verdict from a historical parity TSV must not be reused as a
result for this baseline if it was produced with a different revision, the
legacy solver, or dispatch disabled.

The tabled/dispatch/Osaka settings in the metadata constitute the
`targetComparisonProfile` for rerunning the comparison. They are not an
executed baseline of the current corpus under those settings. The external Yul
compiler targets for both Haskell and Rust also remain unspecified.

## Implementation-status vocabulary

- `conformant`: agrees with the normative result under the same profile
- `divergent`: disagrees with the normative result under the same profile
- `mode-dependent`: varies with settings such as the solver mode
- `phase-dependent`: varies with the phase reached, such as frontend,
  specialization, or dispatch
- `partial`: implements only some required paths
- `unsupported`: does not implement a required path
- `unverified`: has not been reproduced against the baseline

## Candidate decisions and historical evidence

Every implementation column below remains `unverified` until the corpus is
rerun with the current revision, the tabled solver, the same std, and the same
phase. The final column records investigation hypotheses from an older
baseline, not current results.

| Rule ID | ADR direction or candidate | Current Haskell | Current Rust | Old-baseline observation |
| --- | --- | --- | --- | --- |
| `syntax.for-post-let` | candidate: permit the same forms as the initializer | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.call-non-function` | reject anything other than a function or invokable value | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.explicit-closure` | permit valid invokable evidence | unverified | unverified | Haskell divergent / Rust conformant |
| `typing.instance-member` | candidate: reject an instantiated-signature mismatch | unverified | unverified | Haskell divergent / Rust conformant |
| `solver.recursive-table-reuse` | accept when tabled resolution succeeds | unverified | unverified | Haskell mode-dependent / Rust conformant |
| `staging.runtime-to-comptime` | candidate: reject during the staging phase | unverified | unverified | both phase-dependent |
| `contract.main-arity` | source runtime `main` has zero parameters | unverified | unverified | Haskell divergent / Rust conformant |
| `contract.dispatch-imports` | candidate: reject failure to resolve dispatch dependencies | unverified | unverified | both phase-dependent |
| `abi.word` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.bool-input` | unsupported in the current profile | unverified | unverified | both unsupported |
| `abi.user-adt` | unsupported until the layout and codec are decided | unverified | unverified | Haskell partial / Rust rejection |
| `abi.unknown-type` | produce a structured outcome without crashing | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.duplicate-signature` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.selector-collision` | reject before code generation | unverified | unverified | Haskell divergent / Rust conformant |
| `abi.nested-tuple-boundary` | unsupported until decided | unverified | unverified | both flatten the top boundary |

`conformant rejection` means that the existing Rust compiler rejects the input
safely. The Lean oracle returns `unsupported` for a feature whose meaning is
undefined by the language profile, so this label does not imply that the
wire-level verdict names are identical.

## Historical std external ABI evidence

The following table summarizes path investigation against an older snapshot;
it is not a conformance result for the current canonical six-file bundle. To
classify a public source type as supported, ABI metadata, the canonical input
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
| user ADT | generic helper exists | consistency with structural signature unverified | consistency with generic codec unverified | unsupported |

`complete` in this table is historical evidence. It does not establish
conformance with the current canonical std, Lean M0/M1, or the target comparison
profile.

## Comparison requirements

- Class resolution must use tabled mode.
- Contract fixtures must enable dispatch in both implementations.
- Isolated frontend fixtures may disable dispatch in both implementations, but
  the verdict must record the phase.
- A comptime failure from a frontend-only result must not be confused with a
  result after specialization.
- The std snapshots must have identical content.
- Bytecode must be executed with the same EVM revision, initial state, and
  transaction sequence.
- Until the external Yul compiler target is fixed for both implementations, a
  contract result produced through Yul must not be used as conformance evidence
  for the current baseline.
- Timeouts and bounded solver failures are inconclusive and must not be counted
  as rejection differences.
- Rust-only negative import fixtures must not be included in the language
  difference count.

## Update rules

A change that adds or resolves a difference must perform all of the following
together:

1. Record the baseline and execution settings.
2. Preserve a minimal witness that demonstrates exactly one difference.
3. Classify the difference as `language difference`, `solver mode`, `phase`,
   `shared std defect`, or `implementation defect`.
4. Create an ADR if a normative decision is required.
5. After resolution, remove the allowance and add both a regression test for
   the corrected implementation and a Lean conformance test.
