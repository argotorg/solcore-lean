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

The repository currently reaches the third step on the internal M2c path.
Structural certification, resolution, source checking, and elaboration remain
separate future stages. The public Oracle v4 follows the older M2b
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
| total parse selection | `ParseOutcomeTotality` |
| finite termination certificate | `RootlessNormalizationDottedStatic*` |

The internal file-only API is
`executeObservedContextualFrontend : WorkspaceFile -> Except
SurfaceDiagnostic ParsedModuleV1`. It returns lexical or parse diagnostics and
does not perform the later structural phase. The lower-level parser accepts a
token ownership proof internally derived by the lexer.

## Why the parser has a static certificate

The chart algorithm must show that normalization cannot continue indefinitely
through rootless prediction, epsilon, and completion edges. The proof assigns
a decreasing finite rank to the fixed grammar's dotted rows.

The executable checker validates a table covering all 2,378 rows. Small Lean
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
| parsing | bounded chart executor | `Parses` and parse-diagnostic applicability | selected-outcome and soundness theorems |
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
