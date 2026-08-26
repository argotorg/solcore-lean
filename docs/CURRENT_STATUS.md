# Current status

This page is the short, revision-local answer to “what works now?”. It
distinguishes formal completion from publication and practical runtime
readiness.

## Executive summary

The Semantic Core path is implemented, proved, and published through Oracle
v3. The original single-file Surface parser is implemented, proved, and
published as the parse-only Oracle v4 boundary.

The newer M2c path now has a validated workspace identity kernel and a
source-preserving Multi lexer/parser. The parser has an unconditional,
proof-argument-free file API and kernel-checked soundness theorems. A separate
pure structural pass now checks all 20 accepted AST-shape rules and returns the
complete diagnostic list in a deterministic order. An independent declarative
foundation now describes the AST sites visited by that pass, duplicate and
span-order helpers, and grouped unit types. Per-diagnostic applicability, final
structural acceptance, and correspondence with the executable validator are
still missing, so this does not yet complete the full ADR-0015 parser delivery
or the whole frontend.

Module resolution, lexical name resolution, source checking, Core elaboration,
and end-to-end workspace execution are not implemented. The Multi chart
executor also requires optimization before it can be treated as a production
or fuzzing-speed parser.

## Status by milestone

| Area | Implemented | Proved | Published | Practical status |
| --- | --- | --- | --- | --- |
| M0 contract, metadata, profiles, verdicts | Yes | Where applicable | Oracle v1 | Stable and frozen |
| M1a Semantic Core machine | Yes | Yes | Via later Core publications | Complete |
| M1b Core wire boundary | Yes | Yes | Oracle v2 / Core v1 | Stable and frozen |
| M1c primitives and Core wire boundary | Yes | Yes | Oracle v3 / Core v2 | Current public Core boundary |
| M2a single-file parser kernel | Yes | Yes | Via M2b | Complete |
| M2b single-file parser publication | Yes | Yes | Oracle v4 / Surface v1 | Current public parse boundary |
| M2c workspace identity and validation | Yes | Yes | No; internal API | Complete |
| M2c unconditional chart-parser milestone | Yes, through raw file parsing | Selected outcome, soundness, and exact cache equivalence | No; internal API | Total; all six representative benchmarks pass, but large-file memory readiness is unproved |
| M2c structural acceptance | Pure validator and all 20 diagnostics; independent reachability/helper foundation | Canonical output shape; diagnostic and acceptance correspondence pending | No; internal API | Executable and fully fixture-tested, not yet certified or connected to the frontend |
| M2c structural syntax identity | No | No | No | Design accepted in ADR-0016 |
| M2c module and name resolution | No | No | No | ADR-0017 is proposed |
| M2d checking and Core elaboration | No | No | No | Planned |
| M2e polymorphism, staging, and comptime | No | No | No | Planned |
| M3 contracts, ABI, storage, observation | No | No | No | Future work |
| M4 differential fuzzing system | No | No | No | Future work |

“Published” means an external versioned contract exists. Internal completion
does not silently widen Oracle v4.

## What the current Multi parser milestone guarantees

The current internal entry points are:

- `executeObservedContextualParse file tokens owned`, for an already lexed
  token stream whose ownership is proved; and
- `executeObservedContextualFrontend file`, which lexes and parses one
  `WorkspaceFile` without asking its caller for a proof argument.

For the parser entry point, the selected-outcome theorem states that the API
returns exactly the outcome selected by the chart implementation. The
soundness theorem states that success satisfies `Parses`, while failure
satisfies the declarative applicability judgment for that parse diagnostic.

For the file-only frontend, the corresponding soundness theorem covers lexical
failure, parse failure, and successful parsing. This wrapper cannot emit a
structural diagnostic: structural validation is a later phase.

Call `validateStructure module` on a parsed module to run the new structural
phase. It reports every applicable `MSS0001`–`MSS0020` diagnostic, ordered by
code, source, byte range, and payload. Its tests cover exact diagnostic spans,
duplicate handling, fallback rules, required parameter types, match arity, and
the rule that a lambda cannot target an enclosing loop.

The separate `StructureJudgment.lean` module now gives a declarative account
of the typed AST sites reachable from a parsed module. Its helpers also state
later-duplicate, source-span ordering, least-span, and grouped-unit facts
without depending on the validator. It is a foundation only: it does not yet
state all 20 diagnostic-applicability rules or final structural acceptance.

Termination no longer depends on a proof supplied by the caller. A finite
static certificate covers all 2,378 dotted grammar rows and supplies the rank
decrease needed by the bounded search. The certificate is split into one
640-row shard, eighteen 96-row shards, and one 10-row tail so Lean can check it
reliably.

## What is public today

External integrations should use the frozen protocols, not the internal Multi
API:

- `solcore-oracle/v3` with `solcore/0.1.0-draft.3` and `core-m1c-v1` is the
  current Semantic Core checking/evaluation boundary.
- `solcore-oracle/v4` with `solcore/0.1.0-draft.4` and
  `frontend-m2b-v1` is a parse-only, one-source-file boundary.

Oracle v4 does not load a workspace, resolve imports or names, check source
types, elaborate to Core, or evaluate source programs. The internal M2c work
does not change its schema, profile, capabilities report, or behavior.

## Verification state

At this revision the project has been checked with:

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

The full build checks 178 jobs. The semantic-kernel audit rejects `sorry`,
`admit`, `partial`, `unsafe`, `axiom`, `noncomputable`, `extern`, and
`implemented_by` in the audited roots. The final parser certificate is also
checked at `trust = 0`; its dependencies use only Lean's expected logical
axioms (`propext`, `Quot.sound`, and, where executable selection requires it,
`Classical.choice`).

## Known limitation: runtime cost

Formal totality and runtime speed are different claims. An earlier development
smoke run on empty input did not finish within 226 seconds. Investigation found
that one bounded Phase C runner kept applying an empty transition until its
multi-billion-step upper bound was exhausted. It now returns as soon as both
queues are empty. Phase A also no longer recomputes the full saturation merely
to validate a result it has already certified. Completion items are classified
once so incompatible pairs can be skipped. Prediction candidates are rejected
from that classification before rebuilding the waiting production, and
complete-item recognition uses a local hash index. The Phase A evidence table
is materialized in one linear pass instead of repeatedly copying growing
lists. The initial Phase A seed block is likewise proved duplicate-free and
materialized in one step, preserving the exact list and charge order of the
reference insertion loop. The role-directed completion scan also avoids
comparing whole items to detect a self pair: equal roles cannot form a
waiting/finished pair, and the no-op replacement is proved equivalent.
Completion candidates are grouped by the nonterminal and boundary they must
share. A waiting item therefore visits only completed items that can join it,
and a completed item visits only the matching waiting items. Each group retains
discovery order, and a checked equivalence theorem shows that skipping every
other item has exactly the same result as the former full scan.
The discovered raw-item list is likewise retained as the ordered proof view,
while a coherent hash set answers duplicate checks. Normal insertions update
both views together, the seed block extends the existing set in seed order,
and normalization reuses the same set because it preserves membership. The
indexed decision is proved equal to the former list search.
Production candidates are grouped by left-hand-side symbol once, in
source-production order, and the same proved index is shared by Phase A,
contextual recognition, and value evaluation.
Phase B checks all eight finalization slots through the coherent hash index and
then charges the proved-fresh block directly. At Phase-B entry, the executor
also builds one immutable lookup table from the Phase A evidence and reuses it
for every guard. The cache preserves the evidence list's first-match and
missing-entry behavior exactly. The cached runner is proved to preserve
charges, failures, and resulting state, and the cache is not retained in the
sealed parser output. Each faster path has an exact-equivalence theorem against
the retained reference implementation.
The execution counter still keeps `usedRev` as its proof ledger, while a
coherent hash set answers duplicate checks quickly. A maintained theorem says
that the hash set contains exactly the addresses in `usedRev`, so this changes
only how membership is found. Completion and production-activation prechecks
use that same indexed decision procedure; charge order, failures, and resulting
states are unchanged.

All six representative benchmark cases pass. Five fresh-process runs on the
development host produced these elapsed-time results:

| Case | Elapsed seconds (range) | Median |
| --- | ---: | ---: |
| `empty` | 0.014505–0.014781 | 0.014609 |
| `tiny` | 0.093648–0.094299 | 0.093837 |
| `import-path` | 0.233372–0.237631 | 0.234023 |
| `return-literal` | 0.899758–0.921011 | 0.917875 |
| `data-constructors` | 0.411895–0.414846 | 0.412456 |
| `contract-field` | 0.544452–0.568294 | 0.548575 |

`/usr/bin/time` reported maximum resident set sizes of 62,816,256 bytes for
`tiny`, 252,198,912 for `return-literal`, 157,237,248 for
`data-constructors`, and 199,098,368 for `contract-field`. The speed improvement
is substantial: `tiny` took about 89.0 seconds before these optimization
passes. These are machine-dependent observations, not language limits or
performance guarantees. The Phase A evidence and its lookup cache still grow
cubically with the token stream, so large-file readiness is unproved and
memory optimization remains necessary.

## Next work

The shortest path from the current state to an end-to-end executable frontend
is:

1. reduce the Multi parser's cubic evidence/cache memory cost and continue
   profiling it on progressively larger inputs;
2. extend the independent structural foundation with diagnostic-applicability
   and final-acceptance judgments, prove correspondence with the implemented
   validator, and connect structural diagnostics to the file frontend;
3. accept and implement module/name resolution;
4. implement source checking and elaboration into Semantic Core;
5. expose a new versioned workspace Oracle only after its profile, schemas,
   limits, diagnostics, proofs, and compatibility story are fixed.

See the [M2 plan](M2_PLAN.md) for the detailed phase boundaries.
