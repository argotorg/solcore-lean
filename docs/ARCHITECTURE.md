# Architecture

`solcore-lean` has two executable entry paths. The source-library path checks a
canonical Solcore workspace, specializes one explicit root, and runs a selected
backend. The versioned Oracle path accepts checked Semantic Core programs and
contract scenarios; Oracle v5 does **not** accept Solcore source. Both paths use
Semantic Core, but source compilation and contract execution are different
interfaces. For current coverage and limitations, see [Current status](CURRENT_STATUS.md).

## Layers

```text
Canonical source library                         Versioned Oracle
RawWorkspace                                     Oracle v5 JSON
  → Syntax lexer/parser                            → strict Core Wire v3 decoding
  → Workspace validation and module catalog       → Core checking and admission
  → resolved declarations, signatures, bodies     → checked contract runtime
  → source inference and trait evidence            → canonical observation
  → explicit-root specialization
  → direct Core | finite graph | typed-source runtime
```

The vertical bars in the last line denote deterministic backend selection,
not three interchangeable representations of values or stores.

### Source syntax and identities

`Solcore.Syntax` retains source spelling, tokens, comments, spans, diagnostics,
and a recovery-aware AST. Diagnostic-free parsing admits a source to subsequent
phases; it does not establish name resolution or typing. `Solcore.Workspace`
validates canonical library/module identities. The fresh canonical parser is
independent of `Solcore.Surface`: despite the generic-looking name, `Surface`
is the frozen historical Surface v1 parser and its experimental Multi
frontend, retained for compatibility and proof archaeology. New source parsing,
AST work, and frontend integration belong under `Syntax`; `Surface` is not a
second current representation and must not feed the current source pipeline.

`Solcore.Resolved` already exists. It supplies stable identities and a
syntax-independent **local-expression** foundation with lookup, typing,
evaluation, and Core correspondence. It is not a complete resolved-language
replacement for the canonical source AST. The whole-program path in
`Solcore.Frontend` catalogs declarations, resolves imports and names, builds
signatures and type environments, and retains occurrence-addressed typed
bodies. `Solcore.TypeSystem` supplies source-level types, substitution,
unification, rank-1 schemes, and inference machinery. These types are not
silently identified with monomorphic Core types.

### Declarative source semantics

`Solcore.SourceSemantics` is the independent formal specification over the
resolved, occurrence-addressed source carrier, following
[ADR-0377](adr/0377-declarative-source-semantics-foundation.md) and
[ADR-0378](adr/0378-declarative-resolved-source-semantics.md). It reuses
frontend records as forgeable data, but no static or staging judgment takes
successful inference, checking, specialization, compilation, or execution as
a premise.

The static layer validates type and predicate scope, exact generic and
implementation-head instantiation, retained evidence and coercions, graph
closure and ownership, and every expression and statement form. Forgeable
function and implementation-method bodies are checked against a semantically
validated signature catalog, and `ProgramWellFormed` requires exact body
coverage. Body-wide residual inference variables are admitted separately from
the lexical variables used while checking generalized initializers; the latter
remain part of the rank-1 generalization barrier. `StructuralSubstitution`
gives generic bodies a normative,
syntax-directed substitution operation; a separate correspondence module
proves its explicit equations with the frontend specialization helper.

The dynamic layer owns mathematical values, locations and heaps, closures,
runtime dictionaries, defaults, primitives, patterns, and mutable places. Its
fuel-free big-step relations specify successful evaluation of every retained
expression and statement form, including calls, selected trait and coercion
methods, mutation, matches, loops, recursion, and final semicolon-free results.
Positive fault judgments expose missing occurrences and evidence, invalid
runtime operands, place failures, call failures, and their left-to-right
propagation through expressions, statements, calls, matches, and loops. They
do not assert that every non-successful term has a unique fault.
The staging layer independently classifies occurrences and whole programs as
`comptime`, `runtime`, or `deferred`, and defines a closed materialization
boundary with an explicit representation relation to the frontend staged-value
carrier. Compile-time materialization is parameterized by an ambient
expression-evaluation relation.

This is a resolved-carrier specification, not raw-source/module resolution or
a proof that an executable frontend implements the judgments. Fault-complete
dynamics, trait-search coherence, checker/evaluator correspondence, progress,
determinism, termination, and backend correctness remain open. Successful
whole-language derivations do have subject reduction: structural generic
substitution transports complete static derivations, and evaluation preserves
deep result/control typing, value/annotation agreement in the heap, and
heap-type extension for instantiated runtime contexts whose rigid and lexical
flexible binders are closed while residual admission remains open.

### Source compilation and execution

`Solcore.Frontend.ProgramChecking.checkProgram` validates, parses, resolves,
and checks a raw workspace. `Solcore.Frontend.SourceCompiler.compile` combines
that check with one explicit ground root, specialization, and backend
selection; `compileChecked` reuses a previously checked program. A compiled
entry is reusable and carries its selected backend, source signature, and
stage-specific failures. The older `SourceProgramExecution` API remains a
smaller Core/graph path rather than the canonical three-backend facade.

The selected backends have separate proof and runtime boundaries:

| Backend | Executable role | Value and state carrier |
| --- | --- | --- |
| Direct Core | Lower a supported specialized body to checked Semantic Core | Core values and local store |
| Finite call graph | Retain finite global definitions, recursion, lexical closures, and indirect calls | Graph values and Core store |
| Typed source | Execute supported typed source forms that cannot be lowered through the preceding paths | Source-typed values and heap |

Selection is direct Core, then call graph, then typed source. Failures retain
the reason each backend rejected a plan. These are restricted Lean APIs, not a
published source wire or Oracle protocol. They do not discover an entry
automatically or define a multi-root policy.

### Semantic Core

`Solcore.Core` is a syntax-independent executable semantic language. It owns
its type and value algebras, typing and evaluation judgments, checker,
evaluator, machine, local cell store, and correspondence/safety proofs. Core
v3 is the checked language published through Core Wire v3 and Oracle v5.
Earlier Core and wire versions are closed compatibility boundaries. A source
feature only enters Core when the lowering supports it; source types, names,
trait evidence, and source-typed heap forms are not Core constructs by
default.

The Core layout groups closely related definitions and proofs rather than
giving each small theorem family its own import boundary. In particular,
[`Core/Derived.lean`](../Solcore/Core/Derived.lean) contains the complete
boolean- and word-valued derived-comparison interface, including signed,
non-strict, flag, evaluation, and renaming results.
[`Core/LocalFragment.lean`](../Solcore/Core/LocalFragment.lean) contains the
local-fragment predicate together with its insertion, typing, evaluation,
inference, and local-right-comparison results. These are organization changes,
not new language or wire versions.

### Contract runtime and observation

`Solcore.ContractRuntime` models execution of checked Core code in an explicit
contract world. It owns accounts, persistent storage, balances, logs,
transaction/frame state, nested calls and creation, checkpoints,
commit/rollback, traps, fuel/resumption, and the observations produced by that
execution. The previous name `Solcore.Semantics` was too broad: this layer is
neither the source-language semantics nor Core's own evaluator. A Core-local
cell store is therefore distinct from contract accounts and storage.

`Solcore.Oracle` is the versioned JSON/wire adapter around executable
boundaries. Oracle v5 strictly decodes Core Wire v3 packages and scenarios,
checks and admits their Core programs, materializes the contract-runtime world,
runs `ContractRuntime`, and encodes a canonical observation or diagnostic. It
does not parse canonical Solcore source, define source-language meaning, or own
contract execution rules. See the [Oracle v5 wire
catalog](ORACLE_V5_WIRE.md) for the exact public protocol.

### Canonical standard-library data

`Solcore.Standard` is data, not a parser or runtime. Its
[`CanonicalData.lean`](../Solcore/Standard/CanonicalData.lean) module embeds the
six canonical standard-library source files as exact UTF-8 byte arrays and
pins each logical path, byte count, and SHA-256 digest. Consumers can construct
a reproducible source workspace from those bytes; changing them is a standard
library revision, not an Oracle or runtime change. This neutral data module
does not import `Syntax`, `Core`, `ContractRuntime`, or `Oracle`.

The intended execution-side dependency direction is:

```text
Core → ContractRuntime → Oracle v5
```

The source-library route consumes `Standard` data through the canonical
`Syntax`/workspace/frontend path and may lower supported programs to Core. The
Oracle route begins at versioned Core JSON and has no dependency on `Standard`,
`Syntax`, or the historical `Surface` parsers.

## Proof boundary

Executable functions are accompanied by independent typing/evaluation
judgments and local correspondence proofs. The amount of proof is not uniform
across the three source backends:

- The declarative resolved-source layer covers all retained static forms and
  successful big-step evaluation. Its whole-language subject-reduction theorem
  composes the value, heap, primitive, coercion, pattern, place, expression,
  statement, loop, and body-call proofs, including generic body instantiation.
  It applies to successful derivations in instantiated runtime contexts whose
  rigid and lexical flexible binders are closed while residual inference
  admission remains open; it is not a progress, determinism, or
  fault-completeness result.
- Direct Core has deep value and final-store preservation under deeply typed
  inputs and an initially typed store.
- The checked finite call graph has a whole-evaluator deep preservation
  theorem for normal completion under the same kind of explicit premises.
  The public compiler graph route carries that conclusion.
- The typed-source runtime has recursive value/heap relations and local
  allocation/update preservation lemmas. An evaluator-wide deep preservation
  theorem is still open; static checked-IR body typing, environment-to-cell
  typing, and projected updates remain dependencies.

None of these normal-completion or successful-evaluation theorems asserts
termination or excludes every runtime fault. The
[deep-preservation decision](adr/0376-deep-runtime-typing-foundations.md) and
[resolved-source semantics decision](adr/0378-declarative-resolved-source-semantics.md)
record the precise current premises and open boundaries. The status document,
not an older ADR, is the revision-local account of supported behavior.

## Version and dependency policy

Core v1/v2, Surface v1, the historical Multi frontend, and older Oracle
versions retain their published meanings. Core v3/Oracle v5 is the current
checked-contract boundary. Internal source work is additive: it does not
silently reinterpret a frozen wire, profile, or observation.

Dependencies should follow the semantic direction: syntax and workspace
identities feed resolution and source checking; a supported specialization may
lower into Core; `ContractRuntime` executes admitted Core in a contract world;
the Oracle adapts the versioned wire protocol to that runtime independently of
source syntax. `Standard` supplies pinned canonical source bytes, while
historical `Surface` code remains outside the current path.
Importing a parser AST into the Core semantic kernel, or treating a compiler
backend as the Oracle, would erase those boundaries.

For concrete modules and a short reading route, see the [project map](PROJECT_MAP.md).
Historical feature-by-feature rationale lives in [`docs/adr`](adr), not in
this architectural overview. The previous long-form architecture narrative is
[preserved as historical notes](archive/ARCHITECTURE_HISTORY.md), with one
relative link adjusted for its new location. Its revision-relative statements
do not override this overview or Current status.
