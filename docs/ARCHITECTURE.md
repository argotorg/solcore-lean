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
independent of the frozen `Solcore.Surface` parsers.

`Solcore.Resolved` already exists. It supplies stable identities and a
syntax-independent **local-expression** foundation with lookup, typing,
evaluation, and Core correspondence. It is not a complete resolved-language
replacement for the canonical source AST. The whole-program path in
`Solcore.Frontend` catalogs declarations, resolves imports and names, builds
signatures and type environments, and retains occurrence-addressed typed
bodies. `Solcore.TypeSystem` supplies source-level types, substitution,
unification, rank-1 schemes, and inference machinery. These types are not
silently identified with monomorphic Core types.

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

### Contract runtime and observation

`Solcore.Semantics` models the explicit contract world and its transitions;
`Solcore.Oracle.V5` decodes requests, checks and admits Core contracts, runs
scenarios, and encodes observations. A Core-local cell store is distinct from
contract accounts, storage, balances, and logs. Oracle v5 specifies checked
Core execution, including commit/rollback behavior, but makes no claim that
the source compiler has a public JSON interface or that its typed heap is
contract storage. See the [Oracle v5 wire catalog](ORACLE_V5_WIRE.md) for
the exact public protocol.

## Proof boundary

Executable functions are accompanied by independent typing/evaluation
judgments and local correspondence proofs. The amount of proof is not uniform
across the three source backends:

- Direct Core has deep value and final-store preservation under deeply typed
  inputs and an initially typed store.
- The checked finite call graph has a whole-evaluator deep preservation
  theorem for normal completion under the same kind of explicit premises.
  The public compiler graph route carries that conclusion.
- The typed-source runtime has recursive value/heap relations and local
  allocation/update preservation lemmas. An evaluator-wide deep preservation
  theorem is still open; static checked-IR body typing, environment-to-cell
  typing, and projected updates remain dependencies.

None of these normal-completion theorems asserts termination or excludes every
runtime fault. The [deep-preservation decision](adr/0376-deep-runtime-typing-foundations.md)
records the precise current premises and open boundary. The status document,
not an older ADR, is the revision-local account of supported behavior.

## Version and dependency policy

Core v1/v2, Surface v1, the historical Multi frontend, and older Oracle
versions retain their published meanings. Core v3/Oracle v5 is the current
checked-contract boundary. Internal source work is additive: it does not
silently reinterpret a frozen wire, profile, or observation.

Dependencies should follow the semantic direction: syntax and workspace
identities feed resolution and source checking; a supported specialization may
lower into Core; the Oracle consumes Core independently of source syntax.
Importing a parser AST into the Core semantic kernel, or treating a compiler
backend as the Oracle, would erase those boundaries.

For concrete modules and a short reading route, see the [project map](PROJECT_MAP.md).
Historical feature-by-feature rationale lives in [`docs/adr`](adr), not in
this architectural overview. The previous long-form architecture narrative is
[preserved as historical notes](archive/ARCHITECTURE_HISTORY.md), with one
relative link adjusted for its new location. Its revision-relative statements
do not override this overview or Current status.
