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
pure structural pass now checks all 20 accepted AST-shape rules and returns a
canonical diagnostic list in a deterministic order. Its independent
specification now covers all 26 diagnostic forms represented by
`MSS0001`–`MSS0020`, defines structural acceptance, and proves that acceptance
means exactly that no structural diagnostic applies. The executable and
declarative sides now agree in both directions: every reported diagnostic
applies, every applicable diagnostic is reported, and the module-derived
traversal fuel is sufficient. Structural validation succeeds exactly for an
accepted module. The source-location proof is now complete across the parser:
the inventory and executable checks cover every located AST field, and
`Parses.everyLocationValid` proves that every successful lex/parse derivation
produces a module whose locations are valid for the source file and properly
nested. The remaining certification work is exact correspondence between the
retained syntax and the original token/comment stream, followed by the
proof-carrying frontend that combines parsing, locations, and structural
acceptance. Formal resource accounting also remains.

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
| M2c structural acceptance | Validator for all 20 codes; independent applicability and acceptance judgments | Two-way correspondence, sufficient traversal fuel, canonical error-list properties, and executable success exactly equivalent to acceptance | No; internal API | Certified as a separate decision procedure; formal resource accounting and file-frontend integration remain |
| M2c source-location evidence | Complete AST inventory and executable validity/nesting checks | `Parses.everyLocationValid` proves validity and direct-parent nesting for every successful parse, using token order, parser-span containment, and assembly-slice facts | No; internal API | Parser-wide location propagation is complete; exact token correspondence and certified frontend integration remain |
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
phase. It returns `MSS0001`–`MSS0020` diagnostics ordered by code,
source, byte range, and payload. Its tests cover exact diagnostic spans,
duplicate handling, fallback rules, required parameter types, match arity, and
the rule that a lambda cannot target an enclosing loop.

The separate `StructureJudgment.lean` module gives a declarative account of
the typed AST sites reachable from a parsed module. Its `Applies` relation
covers all 26 diagnostic constructors behind `MSS0001`–`MSS0020`, and
`StructurallyAccepts` holds exactly when no such diagnostic applies. The
duplicate, source-span, and least-span primitives are proved exact. Imports,
exports, and pragmas have exact local specifications and top-level soundness.
Missing signature types and disallowed modifiers have exact local results and
are sound at every reached signature. Fallback and constructor declarations
also have exact local specifications and soundness, including a fuel-free
grouped-unit return check. The six recursive collectors are sound for every
fuel value, and structural paths are strictly shorter than the module AST
measure. These results compose in both directions: membership in
`diagnosticCandidates` is equivalent to declarative applicability, and the
module-sized traversal fuel reaches every applicable site. Deduplication and
sorting preserve that exact membership. Consequently `validateStructure`
succeeds exactly when `StructurallyAccepts` holds; on failure, its nonempty
report contains exactly the applicable diagnostics, without duplicates and in
canonical order.

The remaining frontend boundary must attach this certified phase to parsing.
All 54 located AST carrier sorts and all 12 retained raw span fields are
covered by one executable inventory. Lexer token ordering, parser-interval
containment, and assembly-internal facts are now carried through every parser
reduction. The resulting theorem, `Parses.everyLocationValid`, says that every
successful parse has valid and properly nested source locations. What is still
missing is exact retained-token correspondence and the
`CertifiedParsedModule`/frontend layer that bundles it with the existing parse,
location, and structural proofs.

The separate numeric resource theorem required by ADR-0015 remains to be
implemented and proved.

Termination no longer depends on a proof supplied by the caller. A finite
static certificate covers all 2,375 dotted grammar rows and supplies the rank
decrease needed by the bounded search. The certificate is split into one
640-row shard, eighteen 96-row shards, and one 7-row tail so Lean can check it
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
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

The full build checks 213 jobs. The semantic-kernel audit rejects `sorry`,
`admit`, `partial`, `unsafe`, `axiom`, `noncomputable`, `extern`, and
`implemented_by` in the audited roots. The final parser certificate is also
checked at `trust = 0`; its dependencies use only Lean's expected logical
axioms (`propext`, `Quot.sound`, and, where executable selection requires it,
`Classical.choice`).

## Known limitation: runtime cost

Formal totality and runtime speed are different claims. An earlier development
smoke run on empty input did not finish within 226 seconds. Investigation found
an executor loop that continued after its work queues were empty. That path now
stops immediately. The parser also reuses completed work, groups compatible
candidates, performs indexed duplicate and production lookups, builds evidence
in bulk, and consumes Phase B evidence into a temporary cache-only state.

Each optimization has a checked correspondence with the retained reference
path: selected output, diagnostic behavior, charge order, and failure behavior
are unchanged. The implementation details and reproduction commands live in
the [development guide](DEVELOPMENT.md).

All six representative benchmark cases pass. Five fresh-process runs on the
development host produced these elapsed-time results:

| Case | Elapsed seconds (range) | Median |
| --- | ---: | ---: |
| `empty` | 0.014303167–0.014395000 | 0.014339333 |
| `tiny` | 0.090263250–0.096705291 | 0.090872417 |
| `import-path` | 0.221413542–0.227876417 | 0.223409167 |
| `return-literal` | 0.863788792–0.887059959 | 0.868775750 |
| `data-constructors` | 0.387477833–0.433975625 | 0.392871250 |
| `contract-field` | 0.536238167–0.599856583 | 0.567094417 |

`/usr/bin/time` reported the following maximum resident set sizes:

| Case | Maximum resident set size (bytes) |
| --- | ---: |
| `empty` | 42,647,552 |
| `tiny` | 60,375,040 |
| `import-path` | 90,275,840 |
| `return-literal` | 210,714,624 |
| `data-constructors` | 139,575,296 |
| `contract-field` | 169,820,160 |

The speed improvement is substantial: `tiny` took about 89.0 seconds before
these optimization passes. These are machine-dependent observations, not
language limits or performance guarantees. Cache-only Phase B lowers retained
memory, but the Phase A evidence enumeration, its lookup cache, and the
proof-carrying counter ledger/index still grow cubically with the token stream.
Large-file readiness is therefore unproved and further memory work remains
necessary.

## Next work

The shortest path from the current state to an end-to-end executable frontend
is:

1. implement the separate fast parser, prove exact result equality with the
   chart reference, and continue memory profiling on larger inputs;
2. complete the ADR-defined formal resource bounds;
3. prove exact token correspondence, then combine the existing parse,
   location, and structural proofs in `CertifiedParsedModule` and the file
   frontend;
4. accept and implement module/name resolution;
5. implement source checking and elaboration into Semantic Core;
6. expose a new versioned workspace Oracle only after its profile, schemas,
   limits, diagnostics, proofs, and compatibility story are fixed.

See the [M2 plan](M2_PLAN.md) for the detailed phase boundaries.
