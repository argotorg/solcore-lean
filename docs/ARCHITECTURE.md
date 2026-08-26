# Architecture

`solcore-lean` keeps syntax, static semantics, execution, and observation as
separate layers. Each executable decision procedure is intended to sit beside
an independent declarative judgment and a theorem explaining their
relationship.

## The end-to-end shape

The intended source pipeline is:

```text
raw workspace
  -> canonical workspace validation
  -> per-file lexing and parsing
  -> structural syntax certification
  -> module and lexical name resolution
  -> source checking and Core elaboration
  -> Semantic Core evaluation
  -> versioned observable result
```

The repository implements workspace validation, per-file lexing and parsing,
and structural validation as separate internal M2c kernels. The parser proves
that every successful result has source-valid, properly nested AST locations
and exact retained-token correspondence, and the structural validator is
proof-connected to an independent judgment. These results are assembled by a
proof-argument-free, one-file certified frontend. Resolution, source checking,
and elaboration are future stages. The public Oracle v4 follows the older M2b
single-source parser path and stops after parsing.

## Main components

### Specification and publication metadata

`Solcore/Profile.lean`, `Solcore/Feature.lean`, and `Solcore/Spec.lean` define
language versions, profiles, features, and canonical digests. Checked-in files
under `profiles/` and `schema/` are the external, reviewable forms of those
contracts.

Publication is additive. A new internal implementation does not modify an old
profile or wire schema. Oracle v1 through v4 continue to dispatch by their
explicit schema identifiers.

### Semantic Core

`Solcore/Core/` contains the small typed language used as the semantic
interchange layer:

- syntax and declarative typing;
- executable checking and detailed diagnostics;
- primitive semantics over booleans and 256-bit words;
- a fuelled CEK machine;
- big-step/machine correspondence, determinism, progress, preservation, and
  fault-unreachability results; and
- strict v1 and v2 JSON wire formats.

The public Core boundary is Oracle v3 with Semantic Core v2. Source programs
do not reach this layer until a future elaborator has resolved and checked
them.

### Published single-file Surface parser

`Solcore/Surface/` is the M2a/M2b parser kernel. It owns its AST, lexer,
grammar judgment, parser, proof properties, and Surface v1 wire projection.
Oracle v4 publishes this path for one opaque-labeled source file.

This boundary is intentionally narrow: it parses but does not interpret a
workspace or assign meaning to names.

### Workspace identity kernel

`Solcore/Workspace/` defines logical source identities without consulting the
host filesystem. It provides:

- canonical main, standard-library, and external-library identities;
- raw and validated workspace representations;
- deterministic, canonical structural errors;
- executable validation and independent acceptance/rejection judgments; and
- soundness, completeness, uniqueness, lookup, and measure properties.

Equal textual paths in different libraries remain distinct. Host path
normalization, directory traversal, filesystem reads, and environment-dependent
lookup are outside this kernel.

### Internal M2c Multi parser

`Solcore/Surface/Multi/` contains the broader source-preserving syntax and
grammar used for multi-module work. The grammar has 75 named nonterminals and
covers module references, imports and exports, declarations, contracts,
statements, expressions, patterns, types, pragmas, and embedded assembly
tokens.

The implementation is organized around these responsibilities:

| Responsibility | Principal modules |
| --- | --- |
| source locations, tokens, AST, diagnostics | `Source`, `Token`, `Syntax`, `Diagnostic` |
| executable and declarative lexing | `Lexer`, `LexicalJudgment` |
| fixed grammar data | `Grammar` |
| chart state and execution | `Chart`, `ParserCore` |
| declarative parsing | `ParserJudgment` |
| implementation/proof correspondence | `ChartProperties`, `Properties` |
| fixed resource bounds, finite parser-schedule addresses, and accounting ledgers | `ResourceBounds`, `ParserResourceAccounting`, `ParserSchedule`, `ParserScheduleTrace`, `StructureResourceAccounting`, `StructureResourceBound` |
| AST location inventory, parser-span geometry, and whole-parse location proof | `Location`, `LocationProperties`, `RuleCoherent*`, `EndpointActionIntervalLocation` |
| exact-token visitor, coherent rule closure, and parser lifting | `ExactToken*`, `Coherent*`, `RuleCoherent*` |
| total parse selection | `ParseOutcomeTotality` |
| structural diagnostic order and pure AST validation | `Diagnostic`, `Structure` |
| structural judgments, traversal bounds, and correspondence | `StructureJudgment`, `StructureFuelProperties`, `StructureProperties` |
| certified one-file phase composition | `CertifiedFrontendCore`, `CertifiedFrontend` |
| finite termination certificate | `RootlessNormalizationDottedStatic*` |

The lower-level file-only API is
`executeObservedContextualFrontend : WorkspaceFile -> Except
SurfaceDiagnostic ParsedModuleV1`. It returns lexical or parse diagnostics and
does not perform the later structural phase. The lower-level parser accepts a
token ownership proof internally derived by the lexer.

`ParserResourceAccounting` describes the separate quadratic fast-parser
schedule as fixed, boundary-slot, and memo-slot components. `ParserSchedule`
realizes each component as a typed finite address space, proves its exact
cardinality, and supplies a lightweight component counter.
`ParserScheduleTrace` records distinct ranked addresses, rejects a repeated
charge, proves each component fits its capacity, proves a fresh charge adds one
unit, and bounds every trace total by `parseBound`. The current chart reference
uses its own `chartGBound` counter and is not silently reclassified as that fast
schedule. An executor that actually charges these addresses, its operational
correspondence, and exact equality with the chart result are still required.

`validateStructure : ParsedModuleV1 -> Except (NonemptyList
StructuralDiagnostic) Unit` is the separate structural executor. It traverses
the full AST, including expressions nested in patterns and lambda bodies,
returns every applicable closed diagnostic, and canonicalizes the result. Its
independent applicability and acceptance judgments agree exactly with the
executor, including sufficient module-derived traversal fuel and the returned
error list. `Solcore.Surface.Multi.parseModule` composes it after lexing and
parsing, preserving first-failing-phase precedence. On success it returns a
`CertifiedParsedModule` carrying `Lexes`, `Parses`, `StructurallyAccepts`,
`EveryLocationValid`, and `ExactTokenCorrespondence`. The exact-token root
theorem covers all 75 grammar rules. This facade is an internal Lean API, not
an Oracle v4 capability.

## Why the parser has a static certificate

The chart algorithm must show that normalization cannot continue indefinitely
through rootless prediction, epsilon, and completion edges. The proof assigns
a decreasing finite rank to the fixed grammar's dotted rows.

The executable checker validates a table covering all 2,375 rows. Small Lean
theorems certify chunks of that table, and one final theorem composes the
chunks. The accepted table then supplies the rank facts used by bounded search,
which supplies unconditional parser progress and, finally, the
proof-argument-free internal entry point.

This arrangement keeps the trusted object small in kind: ordinary Lean data,
Boolean computation, and kernel-checked theorems. It does not use a runtime
escape hatch or a proof argument from the API caller.

## Executable and declarative sides

The common proof pattern is:

| Concern | Executable side | Declarative side | Connection |
| --- | --- | --- | --- |
| workspace | pure validator | validation/rejection judgments | soundness and completeness |
| lexing | bounded lexer | lexical judgment and diagnostic applicability | accepted-token and rejection theorems |
| parsing | bounded chart reference; exact finite fast-schedule address spaces and duplicate-rejecting trace without a connected executor | `Parses` and parse-diagnostic applicability | selected-outcome, soundness, parser-wide location validity, and exact-token correspondence for the chart path; every standalone fast-schedule trace is bounded by `parseBound` |
| structural validation | complete pure diagnostic collector | independent acceptance and applicability judgments | two-way correspondence, sufficient traversal fuel, canonical reports, and success iff acceptance; numeric accounting exposes all six charged families and their exact total, with a proved sufficient fixed quadratic bound |
| certified file frontend | `Solcore.Surface.Multi.parseModule` | conjunction of lexical, parse, structural, location, and retained-token properties | proof-argument-free phase composition with deterministic success/failure characterizations |
| Core checking | Boolean/detailed checker | typing relation | soundness and completeness |
| Core execution | fuelled CEK machine | big-step relation | two-way correspondence |

Not every published error is a semantic verdict. Malformed JSON, wrong schema
versions, and invalid protocol envelopes are protocol errors. Valid requests
use the closed verdict categories fixed by the charter.

## Trust boundary

The semantic kernel is checked by Lean and by a repository policy audit. The
audited roots may not contain declarations or escape hatches matching
`sorry`, `admit`, `partial`, `unsafe`, `axiom`, `noncomputable`, `extern`, or
`implemented_by`.

The project still relies on Lean's normal logical foundations. A theorem's
axiom report may therefore include `propext`, `Quot.sound`, or
`Classical.choice`; these are reported explicitly rather than described as
“no axioms”. Upstream Haskell and Rust behavior is comparison evidence only and
is isolated from specification authority.

## External boundaries

| Oracle | Purpose | Language/profile | Input model |
| --- | --- | --- | --- |
| v1 | initial capability contract | draft.1 / `core-v1` | legacy request envelope; workspace is `null` for capabilities |
| v2 | M1b Core checking/evaluation | draft.2 / `core-m1a-v1` | Semantic Core v1 |
| v3 | M1c Core checking/evaluation | draft.3 / `core-m1c-v1` | Semantic Core v2 |
| v4 | M2b parsing | draft.4 / `frontend-m2b-v1` | one opaque-labeled source file |

There is no published M2c workspace parser or resolver protocol yet. Creating
one requires a new profile and versioned wire contract; it must not reinterpret
Oracle v4.
