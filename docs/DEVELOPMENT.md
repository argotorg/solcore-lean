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
| `empty` | 0.014505–0.014781 | 0.014609 |
| `tiny` | 0.093648–0.094299 | 0.093837 |
| `import-path` | 0.233372–0.237631 | 0.234023 |
| `return-literal` | 0.899758–0.921011 | 0.917875 |
| `data-constructors` | 0.411895–0.414846 | 0.412456 |
| `contract-field` | 0.544452–0.568294 | 0.548575 |

All six cases parsed successfully. For comparison, `tiny` took about 89.0
seconds before the parser optimization work. `/usr/bin/time` reported these
maximum resident set sizes:

| Case | Maximum resident set size (bytes) |
| --- | ---: |
| `tiny` | 62,816,256 |
| `return-literal` | 252,198,912 |
| `data-constructors` | 157,237,248 |
| `contract-field` | 199,098,368 |

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

Phase B now builds one immutable lookup table from the Phase A evidence when
it enters the phase and reuses it for every guard check. The lookup is proved
to preserve the evidence list's first-match and missing-entry behavior. The
whole cached runner is also proved to preserve charges, failures, and output
state. The lookup table is temporary execution data and is not retained in the
sealed parser result. This removes repeated evidence-list scans and accounts
for much of the improvement in the representative cases. It does not remove
the cubic-size evidence table or the cache built from it, so large-file memory
readiness is still unproved and memory optimization remains required.

## Structural-certification guidance

`Solcore/Surface/Multi/StructureJudgment.lean` now provides an independent
declarative foundation for structural checking. It describes which typed AST
sites are reachable from a parsed module and supplies small relations for
later duplicates, source-span ordering, least-span selection, and grouped unit
types. It intentionally does not import or restate the executable structural
validator.

This is only the proof foundation. The per-diagnostic applicability judgments,
the final structural-acceptance judgment, and the soundness/completeness
connection to `validateStructure` still have to be implemented. Keep those
claims distinct when reviewing or documenting later work.

## Documentation rule

Keep [current status](CURRENT_STATUS.md) as the implementation ledger. Use
ADRs for durable decisions and rejected alternatives, the charter for
normative authority, and matrices for row-by-row coverage. Avoid copying a long
theorem inventory into every document; link to the architecture or the
relevant ADR instead.
