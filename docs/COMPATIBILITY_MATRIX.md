# Haskell/Rust compatibility and evidence matrix

This document records evidence about the pinned Haskell and Rust
implementations. It is not the language specification: agreement between the
two compilers does not establish conformance when an Accepted ADR or Lean's
declarative rules say otherwise.

For the implementation/publication split, see [current status](CURRENT_STATUS.md)
and the [feature matrix](FEATURE_MATRIX.md).

## Pinned comparison baseline

| Target | Revision / digest |
| --- | --- |
| Haskell `argotorg/solcore` | `1d490d8bb5f374356f06e0720655496482eb1fb4` |
| Rust `argotorg/solcore-rs` | `38f4778ea461edfe59106bdb1f9f08c3307b0fc0` |
| canonical upstream std | `3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22` |
| Rust std Git tree | `c58489d2d544b314b7fa843b331062f6f5129655` |
| Rust compatibility std snapshot | `c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430` |

The Rust vendored standard library is not identical to the canonical upstream
bundle. Both implementations must use identical source bytes before an
end-to-end result can be compared. Results from another revision, an older
parity TSV, the legacy solver, or a different dispatch setting are not results
for this baseline.

The tabled/dispatch/Osaka settings in metadata define the
`targetComparisonProfile` for a rerun; they are not evidence that the current
corpus has been executed under those settings. The external Yul compiler
target is also not pinned for either implementation.

## Status vocabulary

- `conformant`: agrees with the normative result under the same profile;
- `divergent`: differs from the normative result under the same profile;
- `mode-dependent`: varies with a solver or compiler setting;
- `phase-dependent`: varies with the phase reached;
- `partial`: implements only some required paths;
- `unsupported`: has no required path; and
- `unverified`: has not been reproduced at the pinned baseline with aligned
  inputs and settings.

`conformant rejection` means an existing compiler rejects safely. Lean may
return `unsupported` when the current profile has no semantics; wire-level
verdict spelling need not be identical for that phrase to apply.

## What can be compared today

| Lean boundary | Haskell/Rust adapter status | Claim that can be made now |
| --- | --- | --- |
| Oracle v3 / Semantic Core v2 | neither compiler consumes this wire directly | Lean is a closed Core reference; no source-level three-way conformance claim |
| Oracle v4 / Surface v1 | parser-level source fixtures can be shared | restricted parser differences can be measured; no resolution or semantic claim |
| M2c workspace identity | internal Lean values only | logical identity and validation rules are specified/tested; no external protocol parity claim |
| M2c Multi lexer | internal Lean API; six canonical files have fixed lexer fingerprints | lexical/source-shape investigations are possible; no published result schema |
| M2c Multi parser | internal unconditional chart parser with selection/soundness proofs; executable 20-rule structural validator; performance work in progress | formal parser behavior and structural diagnostics are available internally; independent structural correspondence, the canonical-standard parse gate, and an external adapter are incomplete |
| structural syntax identity | ADR-0016 design only | no executable comparison yet |
| module/name resolution | ADR-0017 Proposed; no Lean implementation | every resolver classification remains unverified |

## Candidate decisions and historical evidence

Every implementation column remains `unverified` until the current baseline is
rerun with identical standard bytes, tabled solving, and the same phase. The
last column is older-baseline investigation evidence, not a current verdict.

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

## M1 source-inspection evidence

### M1a choices

These paths were inspected for ADR-0009. They are not an aligned end-to-end
run and do not make either compiler normative.

| Rule | Haskell evidence | Rust evidence | ADR-0009 decision |
| --- | --- | --- | --- |
| let binder scope | introduces the binder after resolving the initializer | introduces the binder after resolving the initializer | evaluate the initializer in the current environment, then add it at index 0 |
| eager operand order | lowers to Hull/Yul in source order | lowers to Yul in source order | future primitives evaluate left to right; M1a has none |
| conditional branch | some paths precompute both branches | selected branch executes inside a switch | condition first, selected branch only |
| word representation | masks with `2^256` when constructing a word | 256-bit modular value | bounded Core value; source modulo behavior belongs to M2 |

The inspected Haskell conditional path can execute effects from the unselected
branch and is a candidate implementation defect. Classification waits for an
M2 source-to-Core fixture.

### M1b boundary

`solcore-oracle/v2` accepts `solcore-semantic-core/v1` and returns checking or
canonical value observations. Haskell and Rust do not accept this Core wire, so
the boundary supports Lean fixture generation, shrinking, and replay but not a
three-implementation source claim. The M1b golden corpus prevents adapters from
conflating `rejected`, `inconclusive`, `executed`, and protocol errors.

### M1c primitive evidence

ADR-0011 records source inspection at the pinned revisions. It is not a rerun
of a source corpus and not a claim that either compiler conforms to
`core-m1c-v1`.

| Rule | Haskell evidence | Rust evidence | M1c specification |
| --- | --- | --- | --- |
| word arithmetic | executable paths use bounded/modular word results | executable paths use 256-bit modular words | add, subtract, and multiply modulo `2^256` |
| unsigned division/modulo | executable witness uses unsigned operations | executable witness uses unsigned operations | zero divisor returns zero |
| direct word equality typing | primitive table assigns direct `eqWord` the wrong result type | primitive table assigns direct `eqWord` the wrong result type | `wordEq : word × word -> bool` |
| primitive coverage | partial evaluator implements only a subset | no corresponding partial-evaluator discrepancy is normative | every listed M1c primitive is total on well-typed operands |
| large shifts | sufficiently large amounts can pass through a host `Int` conversion | implementation/EVM-shaped behavior returns zero outside the width | `wordShl` and `wordShr` return zero when amount is at least 256 |
| operand order | lowering visits ordinary primitive operands in source order | lowering visits ordinary primitive operands in source order | evaluate each binary operand once, left to right |
| boolean conjunction/disjunction | standard library uses eager functions and notes the short-circuit gap | no eager-library behavior is adopted as normative | deferred; future elaboration uses selected-branch-only conditionals |

Lean intentionally does not reproduce the result-type error, folding gaps,
host-integer shift path, or eager boolean-library behavior. These are
discrepancy candidates until aligned source fixtures classify them.

### M1c Oracle boundary

`solcore-oracle/v3` accepts only `solcore-semantic-core/v2` under draft.3 and
`core-m1c-v1`. Capabilities v3 fixes the profile digest, Core schema, feature
statuses, limits, and unchanged v1 result/value schemas.

Oracle v1 remains the draft.1 capability protocol; Oracle v2 remains bound to
draft.2, `core-m1a-v1`, and Core v1. Neither upstream compiler consumes Core v1
or v2 directly. Oracle v4 supplies restricted parsing, while the internal
Multi parser still stops before structural certification, resolution,
checking, and elaboration. Oracle v3 therefore remains a closed Core reference.

## Surface parser evidence

### Published M2a/M2b fragment

ADR-0012 chose common syntax visible at the pinned revisions. This is parser
source inspection, not an end-to-end conformance result.

| Surface rule | Haskell evidence | Rust evidence | M2a decision |
| --- | --- | --- | --- |
| function envelope | `Parser/Decl.hs:246-251,279-290` | `parse/items.rs:165-267` | one nullary function with `->` return type |
| initialized typed let | `Parser/Stmt.hs:41-55` | `parse/stmt.rs:136-164` | require type, `=`, initializer, and semicolon |
| final return | `Parser/Stmt.hs:48-55` | `parse/stmt.rs:136-155` | require one value-returning final statement |
| keyword conditional | `Parser/Expr.hs:28-47` | `parse/expr_pat.rs:106-136` | preserve a distinct Surface constructor |
| precedence | `Parser/Expr.hs:52-113` | `parse/expr_pat.rs:256-417` | shared unary/arithmetic/bitwise/relation/equality order |
| comments | `Lexer/SolcoreLexer.hs:23-27` | `lexer.rs:272-330` | retain outer spans and support nesting |
| source offsets | character offsets stored in byte-named fields | UTF-8 byte ranges | normative half-open UTF-8 byte ranges |

The parser does not adopt Rust-only `let :=`, value-free return, or
unparenthesized statement-if extensions. It also does not adopt either
resolver's branch-scope leakage, duplicate-local overwriting, or source literal
wrapping.

Both implementations resolve `true` and `false` as shadowable names. M2b
preserves them as names and defers static meaning. Neither compiler has source
operators for word not or shifts; `bnotWord`, `bshlWord`, and `bshrWord` are
ordinary standard-library calls. M2b parses such calls without assigning
primitive identity from spelling.

### M2b Oracle boundary

Oracle v4 publishes parse-only observations under draft.4 and
`frontend-m2b-v1`. A request contains one source string and nonempty opaque
label. The label is copied unchanged into spans and is not opened or resolved.
`sourceBytes` counts only UTF-8 content bytes; overflow is `inconclusive`.
Accepted results are tied to the exact lexer output, token correspondence,
grammar validity, and `FileParses`.

Oracle v3 and v4 remain complementary: closed Core checking/evaluation versus
closed Surface parsing. Oracle v1 through v3 and all existing profiles,
schemas, capability bytes, and golden streams are frozen. M2b can support
parser-level differential fixtures but not full source semantic conformance.

## Internal M2c evidence

### Workspace identity

ADR-0014 deliberately removes host/filesystem behavior from logical identity.

| Topic | Pinned implementation behavior | Lean M2c rule | Current evidence |
| --- | --- | --- | --- |
| logical paths | both compilers consult host roots; symlink/realpath behavior is not portable | ASCII, case-sensitive logical `.solc` paths; no I/O or normalization | executable parser/renderer and path judgments; accepted/rejected path tests |
| source/module identity | implementation paths and loaded-file structures participate | `{library, canonical path}` only | injective `SourceId.toModuleId`; equal-content/different-library tests |
| workspace order | driver/container order can affect traversal | canonical sorted libraries/files; raw permutations equivalent | validator equivalence and measure tests |
| structural errors | implementations may stop early or use driver errors | complete canonical list of eight error families | sound/complete validation and coexistence tests |
| standard sources | implementation-owned host roots | absent from validated user workspace | proved shape; standard assembly deferred |

This is an internal value boundary, not a published workspace schema.

### Multi lexer and syntax

The larger ADR-0015 parser retains source distinctions needed by future
resolution rather than copying either compiler tree.

| Topic | Haskell evidence | Rust evidence | Multi Surface decision / implementation |
| --- | --- | --- | --- |
| parsed tree | grouping, tuple and body forms are normalized on several paths | retains more shape but includes recovery/error artifacts | recovery-free AST preserving groups, optional fields, tuples, markers, and spelling |
| identifiers | parser/lexer admits implementation-specific Unicode categories | host Unicode property behavior | ASCII identifiers with no normalization; non-ASCII remains valid in strings/comments |
| numeric literals | converts or lowers values on parser paths | retains parser values/spans by implementation rules | exact decimal/hex spelling and digits; no source typing or wrapping |
| comments and offsets | character offsets appear in byte-named fields | UTF-8 byte ranges | exact half-open UTF-8 byte spans and retained outer comments |
| assembly | implementation-owned Yul parsing/lowering | implementation-owned Yul parser/recovery | one balanced opaque source slice; Yul semantics deferred |
| absent syntax | some bodies/branches are normalized | recovery and AST conveniences vary | `none` remains absent; parser invents no located node |
| imports/exports | parser feeds implementation resolver forms | parser feeds implementation resolver forms | source-preserving syntax only; no target or visibility meaning |

Lean tests currently fix every token map, maximal-munch case, diagnostic,
UTF-8 span, assembly slice, grammar-table cardinality, canonical raw metadata,
and six-file lexer fingerprint. They also exercise all 20 structural
diagnostics, their exact spans and payloads, canonical ordering, and loop/lambda
behavior. The proof build supplies the unconditional chart outcome and
soundness boundary. Independent structural correspondence, kernel-checked
parsing and structural acceptance of all six canonical files, and an external
adapter remain open; native runtime measurement now has a dedicated harness.

### Structural identity and resolution

ADR-0016 has Accepted role-tagged structural identity rules, but there is no
`Surface/Multi/Structural` implementation. ADR-0017's resolver is Proposed and
there is no `Solcore/Resolution` code. Its module lookup, fixed-point interface,
shadowing, constructor visibility, intrinsic, and source-instance policies are
design candidates, not current compatibility results. In particular, parsed
import/export syntax must not be reported as module-resolution support.

## Historical standard-library ABI evidence

This table is path inspection from an older snapshot, not conformance for the
current canonical six-file bundle. “Complete” requires a fresh audit of
metadata, signature, decoding, and encoding against the aligned bundle.

| Source type | Metadata/signature | Decode | Encode | Historical status |
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
| user ADT | generic helper exists | structural-signature consistency unverified | generic-codec consistency unverified | unsupported |

Historical `complete` is not a claim of conformance with the current standard
bundle, Lean M0/M1, or the target comparison profile.

## Requirements for a valid comparison run

- Align class resolution to tabled mode.
- Enable dispatch in both implementations for contract fixtures.
- Dispatch may be disabled in both for isolated frontend fixtures, but record
  the reached phase.
- Do not conflate frontend-only comptime failures with post-specialization
  outcomes.
- Use standard-library snapshots with identical contents.
- Execute bytecode with the same EVM revision, initial state, and transaction
  sequence.
- Do not use Yul-backed contract results as current-baseline conformance
  evidence until both external Yul compiler targets are pinned.
- Treat timeouts and bounded solver failures as `inconclusive`, not rejection.
- Do not count Rust-only negative import fixtures as language differences.
- Compare at a boundary both sides actually implement; internal Lean progress
  is not an external wire adapter.

## Update rules

A new or resolved discrepancy must update this ledger together with:

1. the exact baseline and execution settings;
2. a minimal witness isolating the discrepancy;
3. classification as `language difference`, `solver mode`, `phase`, `shared
   std defect`, or `implementation defect`;
4. an ADR when a normative judgment is required; and
5. after resolution, removal of the allowance plus regression tests for the
   implementation and a Lean conformance witness.
