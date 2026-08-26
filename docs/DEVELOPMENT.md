# Development guide

This guide gives the shortest reliable path for building and reviewing
`solcore-lean`. The repository pins Lean exactly, so use the checked-in
`lean-toolchain` rather than a locally chosen compiler version.

## Build and test

From the repository root:

```sh
lake build
lake test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

`lake build` compiles the library, Oracle, and proof modules with warnings
treated as errors. `lake test` builds and runs the test driver, covering unit,
round-trip, protocol, workspace, lexer, grammar-table, and golden-stream
checks. The two Node scripts validate checked-in metadata and enforce the
semantic-kernel source policy.

The metadata verifier checks recorded revisions, sizes, hashes, and filesets.
To verify the canonical standard-library bytes against a pinned upstream
checkout as CI does, run:

```sh
node scripts/verify-metadata.mjs --canonical-source-root <solcore-checkout>/std
```

## Run the Oracle

Useful discovery commands are:

```sh
lake exe solcoreOracle --help
lake exe solcoreOracle --version
lake exe solcoreOracle capabilities
lake exe solcoreOracle capabilities-v2
lake exe solcoreOracle capabilities-v3
lake exe solcoreOracle capabilities-v4
```

With no command-line argument, the Oracle reads one NDJSON request per line
from standard input and emits one response per line in the same order. Requests
select their protocol with the `schema` field; do not infer a protocol from the
latest implementation milestone.

## Review checklist

Before treating a semantic change as complete, check all applicable items:

- the executable definition is total and deterministic at its stated input
  boundary;
- an independent declarative judgment states the intended meaning;
- soundness and completeness are proved, or any deliberately one-way result is
  documented;
- errors and resource exhaustion have closed, deterministic behavior;
- version/profile/feature data changes only when a publication is intended;
- JSON codecs, schemas, capabilities, golden cases, and mixed-version behavior
  agree for a published change;
- old protocols retain their previous meaning and canonical bytes;
- documentation distinguishes implementation, proof, publication, and runtime
  readiness; and
- the full build, tests, metadata check, and kernel policy check pass.

For a proof-heavy change, also inspect the final theorem with Lean's
`#print axioms` and, for the critical certificate boundary, compile an audit
module with `lake env lean --trust=0 path/to/Audit.lean`.

## Semantic-kernel policy

`scripts/check-kernel.mjs` scans the Core, Semantics, Surface, Standard, and
Workspace roots (a missing future root is skipped). It rejects these tokens in
Lean source:

```text
sorry admit partial unsafe axiom noncomputable extern implemented_by
```

This is a repository policy in addition to Lean's type checker. Avoid putting
these words in comments inside audited roots because the policy intentionally
scans source text.

The policy does not mean that Lean proves without foundations. Expected axiom
reports can include `propext`, `Quot.sound`, and `Classical.choice`; document
the actual report for the theorem being audited.

## Where changes belong

| Change | Primary location | Also review |
| --- | --- | --- |
| language/profile metadata | `Solcore/Profile.lean`, `Solcore/Feature.lean` | `profiles/`, manifest, charter, matrices |
| Core syntax or semantics | `Solcore/Core/` | Core wire versions, Oracle v2/v3, tests, ADRs |
| published M2b parser | `Solcore/Surface/` | Surface wire v1, Oracle v4, schemas, golden cases |
| logical workspace identity | `Solcore/Workspace/` | ADR-0014 and workspace tests |
| internal M2c syntax/parser | `Solcore/Surface/Multi/` | ADR-0015/0016, M2 plan, status page |
| resolver design or implementation | future resolver modules | ADR-0017, feature/profile boundary |
| protocol behavior | `Solcore/Oracle/` | schema files and all mixed-version tests |

Do not expose an internal M2c capability by editing Oracle v4. Publication is a
separate compatibility decision with a new closed contract.

## Parser-specific guidance

The M2c parser has a large fixed grammar and proof surface. Keep generated or
mechanically checked facts isolated from conceptual lemmas. If the grammar
changes, re-establish all of the following before claiming parser completion:

1. grammar-table consistency and diagnostic exhaustiveness;
2. lexer ownership and lexical diagnostic soundness;
3. chart invariants and declarative parse soundness;
4. total outcome selection;
5. the finite dotted-rank certificate for the new grammar; and
6. file-only frontend selection and soundness.

Runtime behavior must be measured separately. The native benchmark covers an
empty module, a minimal declaration, and four small examples of everyday
syntax. These cases still do not characterize large programs or interactive
use. Optimization changes should add benchmarks or bounded regression tests
without weakening the proof boundary.

The native frontend benchmark is deliberately outside the default build and
test targets. Build it once, then run each case in a fresh process:

```sh
lake build m2cFrontendBench
.lake/build/bin/m2c-frontend-bench empty
.lake/build/bin/m2c-frontend-bench tiny
.lake/build/bin/m2c-frontend-bench import-path
.lake/build/bin/m2c-frontend-bench return-literal
.lake/build/bin/m2c-frontend-bench data-constructors
.lake/build/bin/m2c-frontend-bench contract-field
```

The cases have deliberately short, readable inputs:

- `empty` parses an empty module;
- `tiny` parses the minimal declaration `data A;`;
- `import-path` parses the dotted import `import lib.core;`;
- `return-literal` parses a function that returns the literal `0`;
- `data-constructors` parses a data declaration with two constructors; and
- `contract-field` parses a contract containing one typed field.

Each command prints one machine-readable line containing the elapsed
nanoseconds and observed result.

Use an external timeout when profiling an untrusted performance change. Do not
turn these wall-clock measurements into normative language limits. The latest
five-run measurements on the development host were:

| Case | Elapsed seconds (range) | Median |
| --- | ---: | ---: |
| `empty` | 0.014303167–0.014395000 | 0.014339333 |
| `tiny` | 0.090263250–0.096705291 | 0.090872417 |
| `import-path` | 0.221413542–0.227876417 | 0.223409167 |
| `return-literal` | 0.863788792–0.887059959 | 0.868775750 |
| `data-constructors` | 0.387477833–0.433975625 | 0.392871250 |
| `contract-field` | 0.536238167–0.599856583 | 0.567094417 |

All six cases parsed successfully. For comparison, `tiny` took about 89.0
seconds before the parser optimization work. `/usr/bin/time` reported these
maximum resident set sizes:

| Case | Maximum resident set size (bytes) |
| --- | ---: |
| `empty` | 42,647,552 |
| `tiny` | 60,375,040 |
| `import-path` | 90,275,840 |
| `return-literal` | 210,714,624 |
| `data-constructors` | 139,575,296 |
| `contract-field` | 169,820,160 |

The counter keeps `usedRev` as the proof-carrying record of charged addresses.
A hash set, proved to contain exactly the same addresses, now handles duplicate
checks without repeatedly scanning that record. Because the two views are kept
coherent, this is a lookup optimization only: charge order, failure behavior,
and resulting state remain the same. Direct completion and
production-activation prechecks use the same indexed membership decision. The
role-directed completion scan also uses the fact that one role cannot be both
waiting and finished, avoiding a whole-item equality check for self pairs; an
exact theorem preserves the reference result. Completion candidates are
grouped by their shared nonterminal and boundary, so the runtime walks only the
opposite-role row that can join the pivot. The rows preserve discovery order,
and their checked stable-filter characterization keeps state and charge order
identical to the full scan. A proof-carrying hash table also groups productions
by their left-hand-side symbol once, retains their original order, and is
reused by all three prediction paths. The duplicate-free initial seed block is
materialized in one certified step with the same list and charge order as
sequential insertion. A second coherent hash set answers raw-item duplicate
checks while the ordered list remains the proof and discovery-order view. Its
membership decision is exactly equal to the retained list search, including
after normalization and bulk seed insertion. These figures are useful for
local regression checks, but none is a normative bound.

Phase B now builds one immutable lookup table from the Phase A evidence and
consumes the evidence list into a cache-only state. The lookup preserves the
list's first-match and missing-entry behavior, while whole-run correspondence
preserves failure, counter state, and sealed output. Generated C performs one
operational cache build and releases list and entry wrappers incrementally as
the streaming fold advances. The cache is discarded before the sealed parser
result is returned.

This reduces retained memory without changing the asymptotic limit. The Phase
A evidence enumeration, the cache, and the proof-carrying counter ledger/index
still grow cubically with token count. Treat the six small cases as local
regression checks, not evidence of large-file or production readiness.

## Structural-certification guidance

`Solcore/Surface/Multi/StructureJudgment.lean` is the independent declarative
side of structural checking. It defines applicability for all 26 diagnostic
constructors represented by `MSS0001`–`MSS0020` and defines structural
acceptance as the absence of an applicable diagnostic. That characterization
is proved in both directions.

The proof bridge is organized in layers. Duplicate,
source-span, and least-span primitives are exact. Imports, exports, and pragmas
have exact local specifications and top-level soundness. Missing signature
types and disallowed modifiers have exact local specifications and are sound
at every reached signature. Fallback and constructor declarations likewise
have exact local specifications and soundness; their grouped-unit return test
is structural rather than fuel-dependent. Each of the six recursive
fuel-bounded collectors is sound for any fuel value. These layers compose to
show that every member of `diagnosticCandidates` is applicable to its module.
The reverse construction follows each reached AST site through a
module-measure-bounded structural path, proving that every applicable
diagnostic is also emitted.

The executable validator already sorts and removes exact duplicates to return
a canonical diagnostic list. Membership in that list is now exactly
declarative applicability, and executable success is exactly
`StructurallyAccepts`.

Traversal fuel is distinct from ADR-0015's numeric structural-resource
contract. The quadratic `structureBound` function now exists; the AST-node
measure is proved equal to a concrete carrier enumeration. All six charged
families have executable traces: node visits, diagnostic insertions,
duplicate-key comparisons, canonical deduplication comparisons, canonical
ordering comparisons, and least-span comparisons. Their public ledger exposes
the exact combined total, and the two canonical-list passes have quadratic
upper bounds in the insertion count. Diagnostic insertions and least-span
comparisons are bounded by the AST measure, aggregate duplicate comparisons
are bounded quadratically, and `structureBound_sufficient` combines those
facts to prove the fixed structural bound sufficient for the complete ledger.

Parser resource accounting is at an earlier integration point.
`ParserResourceAccounting.lean` exposes the fixed, boundary-slot, and
memo-slot components of the quadratic fast-parser schedule. Their capacity
ledger sums definitionally to `parseBound`, and its reduction theorems show
exactly how a counted execution will inherit that bound. This does not count
the current `Chart.G` reference executor: its private counter uses the separate
quartic `chartGBound` address universe. Closing the parser bound still requires
the counted fast executor, a correspondence theorem from its counter to the
public schedule ledger, and proofs of the three component bounds.

`validateStructure` is a certified standalone structural phase. The
proof-carrying `CertifiedParsedModule` and parameterized frontend phase core
now exist, but do not yet describe the raw file frontend as unconditionally
certified: three reachability-sensitive exact-token rules and the final
proof-argument-free wrapper remain. Location certification itself is complete.
The inventory and its executable checks cover the whole AST, and
`Parses.everyLocationValid` combines token ordering, parser-span containment,
and assembly-internal facts to prove valid, properly nested locations for every
successful parse.

## Documentation rule

Keep [current status](CURRENT_STATUS.md) as the implementation ledger. Use
ADRs for durable decisions and rejected alternatives, the charter for
normative authority, and matrices for row-by-row coverage. Avoid copying a long
theorem inventory into every document; link to the architecture or the
relevant ADR instead.
