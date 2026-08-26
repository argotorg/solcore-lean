# M2: Frontend plan and implementation record

M2 turns a closed `.solc` workspace into the published Semantic Core through
separate parsing, structural certification, resolution, checking, and
elaboration phases. Each executor must be paired with an independent
declarative judgment; neither pinned compiler's frontend is the specification.

For a short revision-local summary, see [current status](CURRENT_STATUS.md).
For module boundaries, see [architecture](ARCHITECTURE.md).

## Current status

| Phase | Decision status | Implementation and proof status | Publication |
| --- | --- | --- | --- |
| M2a restricted single-file parser kernel | ADR-0012 Accepted | complete | internal foundation for M2b |
| M2b restricted parser publication | ADR-0013 Accepted | complete | draft.4, Surface v1, Oracle v4 |
| M2c workspace identity | ADR-0014 Accepted | complete and proof-audited | internal only |
| M2c Multi source/token/AST and lexer | ADR-0015 Accepted | complete for the current internal boundary | internal only |
| M2c Multi full-token parser | ADR-0015 Accepted | unconditional parser and file-only lexer/parser wrapper implemented; selected-outcome and soundness theorems complete | internal only |
| M2c structural acceptance | ADR-0015 Accepted | validator and independent judgments implemented; two-way correspondence, sufficient traversal fuel, canonical reports, and success iff acceptance proved; numeric work bound and certified-module integration remain | internal only |
| M2c structural syntax identity | ADR-0016 Accepted | design only; no implementation modules or tests yet | none |
| M2c module and lexical resolution | ADR-0017 Proposed | blocked and not started | none |
| M2d source checking and Core elaboration | decisions incomplete | not started | none |
| M2e polymorphism, classes, and staging | direction accepted in part | not started | none |

The **unconditional raw-parser milestone is complete**: callers can lex and
parse one `WorkspaceFile` without supplying a termination proof. The full
ADR-0015 parser delivery and the whole M2 frontend are not complete because the
implemented structural validator is fully connected to its independent
judgments but is not yet connected to the certified-module boundary, while
resolution, checking, and elaboration do not exist yet.

## Published M2b boundary

M2b remains the only published source frontend. It provides:

- the closed `solcore-surface/v1` wire AST;
- `solcore-parse-result/v1` with stable phase, code, UTF-8 span, and arguments;
- `solcore/0.1.0-draft.4` with `grammarVersion = 1`;
- profile `frontend-m2b-v1`, enabling only `surfaceGrammar`; and
- Oracle v4 `capabilities` and `parse` queries with positive, negative,
  malformed-wire, resource, cross-version, and mixed-stream golden cases.

One request contains source text and a nonempty opaque label. The label is
copied into returned spans and is never interpreted as a path. `sourceBytes`
measures only UTF-8 content bytes; exceeding it is `inconclusive` before
lexing.

M2b does not load a workspace, resolve a name, type-check source, elaborate to
Core, or evaluate. Draft.1 through draft.3, Core v1/v2, Oracle v1 through v3,
and their existing bytes remain frozen.

## Completed M2c workspace identity kernel

[ADR-0014](adr/0014-m2c-workspace-identity.md) implements a pure logical
workspace boundary with no filesystem access:

- ASCII canonical source paths of the form `segment(/segment)*.solc`;
- case-sensitive structured `LibraryId`, `SourceId`, and `ModuleId` values;
- raw and proof-carrying validated workspace types;
- all eight validation-error families in canonical sorted order;
- canonical, duplicate-free file and external-library ordering;
- source lookup, unique entry, exact source-file count, and UTF-8 byte measures;
  and
- soundness, completeness, functional success/rejection, exclusivity, and
  invariance under the specified raw-workspace equivalence.

Equal content or equal relative paths in different libraries do not collapse.
The kernel performs no normalization through cwd, symlinks, host roots, or
file existence. It neither assembles the standard library nor resolves a
module reference.

## Implemented internal Multi frontend

[ADR-0015](adr/0015-m2c-multi-surface-parser.md) defines a separate internal
grammar named `solcore-multi-surface/m2c-v1`. It does not extend Surface v1.

### Source, tokens, and syntax

The implemented algebra includes:

- `SourceId`-owned half-open UTF-8 byte spans and source-located values;
- 30 hard keywords, 2 contextual keywords, 4 pragma names, and 40 symbols;
- source-preserving module references, imports, exports, declarations,
  contracts, functions, classes, instances, data/type declarations, pragmas,
  statements, patterns, types, and expressions;
- explicit grouping, tuple shape, optional `else` and return values, exact
  literal spelling, markers, operators, terminators, and assembly slices; and
- a recovery-free `ParsedModuleV1` with no invented node for absent syntax.

This is a syntactic algebra only. A parsed import is not a resolved edge, and
a parsed identifier is not a declaration or local identity.

### Lexer guarantees

The lexer is pure and total. Its declarative and executable sides establish:

- ASCII maximal munch and exact hard/contextual-keyword behavior;
- nested block comments and retained outer comment spans;
- exact string spelling/decoding and closed lexical diagnostics;
- UTF-8 boundary-valid, source-owned token and comment spans;
- opaque balanced assembly blocks that ignore delimiters inside nested
  comments and strings;
- executor soundness and completeness against the lexical judgment; and
- an input-derived sufficient work bound.

Tests cover path/source ownership, all closed token maps, maximal munch,
Unicode byte spans, lexical errors, opaque assembly scanning, exact grammar
cardinalities, and lexer fingerprints for all six canonical standard files.

### Grammar, chart, and parse diagnostics

The fixed grammar contains 75 named rules, 737 EBNF sites, 1,040 expanded
production/action IDs, 2,378 dotted rows (`D`), and 1,861 contextual frontier
coordinates (`F`). The implementation provides typed action reductions,
context-preserving chart items and edges, declarative `Parses`, closed
unexpected/repeated-nonassociative diagnostics, and a three-phase chart
executor.

The parser preserves nonassociative relational/equality behavior, explicit
group resets, contextual priorities, exact expected-token frontiers, complete
input consumption, and source-backed AST reduction. Parser success and parser
failure are related to independent declarative judgments rather than to
presentation text.

### Unconditional parser and static certificate

The current internal APIs are:

```text
executeObservedContextualParse
  : (file : WorkspaceFile) ->
    (tokens : List Token) ->
    TokensOwnedBy file tokens ->
    Except ParseDiagnostic ParsedModuleV1

executeObservedContextualFrontend
  : WorkspaceFile -> Except SurfaceDiagnostic ParsedModuleV1
```

The parser API returns exactly the chart-selected outcome. On success the
result satisfies `Parses`; on failure its diagnostic satisfies
`ParseDiagnostic.Applies`. The file-only wrapper obtains token ownership from
the lexer and is sound for lexical failure, parse failure, and success. It
cannot construct `.structural`, because structural checking is a later phase.

Termination is no longer a caller premise. A kernel-checked Boolean table
covers all 2,378 dotted rows, proves the grammar-specific decreasing rank, and
closes bounded search. The certificate is checked as one 640-row shard,
eighteen 96-row shards, and a 10-row tail, then composed by
`dottedStaticRankTable_eq_true`. It uses neither `native_decide` nor an
undeclared axiom.

### Practical limitation

Formal totality is not a speed claim. An earlier development smoke run on empty
input did not finish within 226 seconds. The first identified cause was a
bounded Phase C runner continuing after both queues were empty; it now returns
immediately. Phase A also re-uses its certified worklist result instead of
recomputing the complete saturation, caches completion classifications, skips
incompatible prediction candidates before rebuilding the waiting production,
indexes complete-item recognition, and avoids whole-item self comparisons in
the role-directed completion scan. Completion candidates are grouped by the
nonterminal and boundary shared by the waiting and completed sides, preserving
their original discovery order. The executor now visits only the matching
opposite-role row; a stable-filter theorem proves this produces the same state
and charge sequence as the full scan. Its evidence table is built in one
linear pass, and its proved duplicate-free seed block is materialized in one
step with reference-exact ordering. A proof-carrying left-hand-side index
preserves source-production order and supplies candidates to Phase A,
contextual recognition, and value evaluation. Phase B runs each fixed
guard-finalization schedule through the coherent counter index. At entry it
builds one immutable lookup table from the Phase A evidence, consumes the
evidence list into a cache-only state, and shares that table across all guard
checks. Proofs preserve the list's first-match and missing-entry behavior as
well as failures, counter state, and sealed output. Generated C performs one
operational cache build and releases list and entry wrappers incrementally
during the streaming fold. The temporary cache is not part of the sealed
parser output.
The raw-item discovery list is retained, but a coherent structural hash set now
answers duplicate checks. Insertions update both views, normalization reuses
the set after proving membership unchanged, and the fast decision is exactly
equal to the former list search.
Exact-equivalence theorems relate each optimized path to the
retained checked implementation. The counter continues to use `usedRev` as its
proof ledger, with a coherent hash set accelerating duplicate checks. The
proved correspondence between them means that charge order, failures, and
resulting states are unchanged. Direct completion and production-activation
prechecks also use this indexed membership decision.

All six representative cases pass. Five fresh-process runs on the development
host produced the following measurements:

| Case | Elapsed seconds (range) | Median | Maximum RSS (bytes) |
| --- | ---: | ---: | ---: |
| `empty` | 0.014303167–0.014395000 | 0.014339333 | 42,647,552 |
| `tiny` | 0.090263250–0.096705291 | 0.090872417 | 60,375,040 |
| `import-path` | 0.221413542–0.227876417 | 0.223409167 | 90,275,840 |
| `return-literal` | 0.863788792–0.887059959 | 0.868775750 | 210,714,624 |
| `data-constructors` | 0.387477833–0.433975625 | 0.392871250 | 139,575,296 |
| `contract-field` | 0.536238167–0.599856583 | 0.567094417 | 169,820,160 |

This is a large speed improvement from the earlier roughly 89-second `tiny`
baseline. It is not a production-readiness claim. Cache-only Phase B reduces
retained wrappers, but the evidence enumeration, lookup cache, and
proof-carrying counter ledger/index still have cubic growth in the token count.
Large-file readiness is unproved and memory optimization remains.

## Work still required to finish ADR-0015

The current file-only wrapper stops after raw parsing. A pure structural
executor now traverses the complete AST, emits all `MSS0001`–`MSS0020`
diagnostic candidates with their specified spans and payloads, canonicalizes
that list, and accepts clean modules. `StructureJudgment.lean` independently
defines all 26 applicability cases represented by those 20 codes and defines
`StructurallyAccepts`; acceptance is proved equivalent to the absence of any
applicable diagnostic. Duplicate, span-order, and least-span primitives are
exact. Import/export/pragma families have exact local specifications with
top-level soundness. Signature missing-type/modifier families are exact and
sound at every reached signature. Fallback and constructor declarations also
have exact local specifications and soundness, with a fuel-free grouped-unit
return check. All six recursive collectors are sound for arbitrary fuel, and
structural paths are shorter than the module AST measure. Their composite
theorems prove that `diagnosticCandidates` membership is exactly declarative
applicability. The canonical report has the same membership, is ordered and
duplicate-free, and `validateStructure` succeeds exactly when
`StructurallyAccepts` holds.

This closes logical traversal-fuel sufficiency. The separate numeric resource
contract required by the ADR is not yet implemented.

The remaining parser-kernel work is:

1. implement the separate fast `Parser`, prove exact result equality with
   `Chart.G`, and establish its stated parser work bound;
2. implement numeric structural-unit accounting, prove `structureBound`, and
   prove the AST-carrier measure equality;
3. carry the existing complete location inventory, executable checks, token
   order, chart-span geometry, and assembly-location facts through every
   parser reduction; then finish grouping, literal-spelling, exact-token, and
   no-normalization invariants at the certified boundary;
4. define the proof-carrying `CertifiedParsedModule` and the final
   `parseModule` phase precedence;
5. prove that structural success and failure select the corresponding
   certified frontend result;
6. construct and kernel-check parser plus structural certificates for the six
   canonical standard files from the one shared raw-byte source; and
7. add the internal umbrella only after proof, test, kernel-policy, and axiom
   audits pass.

The executable structural pass and its independent specification both exist,
and their correspondence is complete. They are not yet a certified file
frontend until location/token evidence and phase integration are connected.

## Structural syntax identity: accepted design, no code yet

[ADR-0016](adr/0016-m2c-structural-syntax-identity.md) fixes the identity layer
that must follow certified parsing:

- role-tagged absolute addresses from the parsed module root;
- exact direct/list child roles and virtual lexical-scope roles;
- source-ordered, complete node/scope/occurrence enumeration;
- module-local reference sites and prepared graph modules;
- a policy-free canonical module index; and
- injective lift from local to index-scoped identities with total primary
  spans and non-dangling proofs.

No `Solcore/Surface/Multi/Structural` implementation exists yet. The next
implementation phase must follow the ADR's dependency order and prove
selection soundness/completeness, inventory exactness, scope ownership,
identity injectivity, enumeration completeness, and measure equations. A
source span or untagged list index must not be substituted for identity.

## Module resolution: proposed and blocked

[ADR-0017](adr/0017-m2c-module-resolution.md) is still Proposed. There is no
`Solcore/Resolution` implementation, no reachable module graph, no interface
fixed point, no lexical scope resolver, no standard-bundle verifier, and no
resolve query.

Before acceptance, ADR-0017 requires:

- the ADR-0015 canonical parser gate and ADR-0016 identity implementation;
- a pure SHA-256 feasibility boundary;
- exact six-file standard-bundle verification from shared bytes;
- an actual canonical resolver run recording the required finite closure and
  saturation counts; and
- independent review of the interface-rule compiler, lookup automaton,
  diagnostics, certificate replayers, and module DAG.

Once accepted, the intended implementation order is standard verification,
closed-workspace assembly, occurrence-preserving graph discovery, declaration
catalogs, interface closure/saturation, import and module-binding environments,
lexical scopes and lookup, intrinsics/pragmas/constructor shorthand, and the
outer resolver correspondence theorem.

## M2d checking and Core elaboration

Resolution alone does not assign types or Core meaning. M2d must separately
decide and implement:

- source integer-literal typing and conversion to `word`;
- the status and shadowing of `true` and `false`;
- operator and type-class resolution;
- canonical identities for word-not and shift helpers;
- exactly-once left-to-right source argument evaluation before any Core
  reordering;
- receiver/member selection, callability, assignment targets, overload and
  instance applicability;
- short-circuit `&&` / `||` elaboration;
- source diagnostics and unsupported-feature classification; and
- type- and stage-preserving elaboration to one published closed Core version.

An elaborator may map only resolved identities, never a callee spelling, to a
Core primitive.

## M2e and publication

Polymorphism, tabled class resolution, and comptime/runtime staging follow only
after their complete rule sets and resource models are accepted. Search
exhaustion is `inconclusive`, not rejection.

No internal M2c work changes Oracle v4. A future workspace frontend requires a
separate publication ADR defining a new language/profile, Surface and result
schemas, limits, capabilities, Oracle query, diagnostics, canonical encoding,
golden streams, and compatibility classification.

## Roadmap from the current revision

| Order | Deliverable | Exit condition |
| ---: | --- | --- |
| 1 | parser performance and memory pass | representative files retain explicit runtime/memory regressions, and cubic evidence/cache/counter memory is reduced without weakening proofs |
| 2 | ADR-0015 structural certification | `parseModule` returns only certified modules or canonical lexical/parse/structural diagnostics |
| 3 | six-file canonical parse gate | all shared standard bytes lex, parse, structurally pass, and re-encode in the kernel |
| 4 | ADR-0016 structural identity | prepared modules and all identity/selection/enumeration theorems complete |
| 5 | ADR-0017 feasibility and acceptance | SHA and actual canonical resolver gates record reproducible counts |
| 6 | module and lexical resolution | pure resolver is sound, complete, deterministic, and non-dangling |
| 7 | M2d checking and elaboration | accepted source subset elaborates to a published Core with type preservation |
| 8 | workspace publication | new versioned protocol and conformance corpus are frozen additively |

## Completion criteria for every frontend phase

- An Accepted ADR fixes every observable choice.
- An independent declarative judgment exists.
- The executor is pure and total at its stated input boundary.
- Soundness is proved; completeness is proved or its exact limit is recorded.
- Successful output preserves source ownership, valid spans, uniqueness, and
  non-dangling identities as applicable.
- Diagnostics are closed, deterministic, and tied to exact source spans.
- Resource exhaustion is explicit and never becomes rejection.
- Publication waits for a closed version-local wire representation, canonical
  codec, limits, capabilities, mixed-version behavior, and golden cases.
- The full build, tests, metadata validation, kernel policy, formatting, and
  public-theorem axiom audits pass.
