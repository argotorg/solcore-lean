# Architecture

`solcore-lean` separates source processing, independent language judgments,
the executable Semantic Core, and checked-contract execution. Each layer has a
direct Lean API and owns its data, executable functions, and proofs.

For revision-specific coverage, see [Current status](CURRENT_STATUS.md).

## Layer map

```text
source bytes
    |
    v
Syntax --------> Workspace
                    |
                    v
Resolved / TypeSystem / Frontend.Current
          |                    |
          |                    +--> direct Core backend
          |                    +--> finite call-graph backend
          |                    +--> typed-source backend
          v
SourceSemantics

Core <-------- Synthesis
  |
  v
ContractRuntime <-------- Abi
```

The arrows show intended data flow, not authority. In particular,
`SourceSemantics` states source-language rules independently of success of an
executable frontend pass.

## Canonical syntax

`Solcore.Syntax` owns lexical tokens, source positions, comments, diagnostics,
recovery nodes, declarations, types, expressions, patterns, statements,
inline Yul syntax, and the parser. It retains source spelling and enough
structure for diagnostics and later phases.

The parser's ordinary-result and exactness theorems live with the relevant
grammar components. A diagnostic-free parse is only a syntactic admission: it
does not prove workspace consistency, name resolution, typing, or execution
safety. [ADR-0153](adr/0153-canonical-syntax-boundary.md) fixes this ownership
boundary.

## Workspace, resolved identities, and types

`Solcore.Workspace` validates logical paths, libraries, modules, and imports.
`Solcore.Resolved` supplies stable identities and a local-expression semantic
foundation with lookup, typing, evaluation, renaming, and Core correspondence.
It is intentionally narrower than the whole source language.

`Solcore.TypeSystem` owns source types, substitutions, schemes, unification,
and inference support. Source types are not definitionally identified with
Core types.

## Executable frontend

`Solcore.Frontend.Current` is the umbrella for the current whole-program
pipeline. Its modules cover program identity and loading, module resolution,
signatures, type resolution and inference, implementation-method selection,
staging, specialization, source-to-Core elaboration, linking, and execution.

The caller supplies a raw workspace and an explicit ground root. The compiler
can select among three deliberately distinct backends:

| Backend | Role | Runtime carrier |
| --- | --- | --- |
| Direct Core | Lower the supported specialized body to checked Core | Core values and local store |
| Finite call graph | Preserve finite definitions, recursion, closures, and indirect calls | Graph values and Core store |
| Typed source | Execute supported typed forms outside the preceding paths | Source values and heap |

Backend selection does not make these representations interchangeable. A
compiled entry records its selected backend and the reasons earlier choices
were unavailable.

`Solcore.Frontend` remains a convenience umbrella: current whole-program code
should prefer `Solcore.Frontend.Current`, while focused clients can import the
specific module that owns their result.

## Declarative source semantics

`Solcore.SourceSemantics` is the proof-facing resolved-source specification.
It reuses occurrence-addressed records as data but does not define validity as
successful execution of frontend functions.

Its main parts are:

- context, well-formedness, instantiation, substitution, and graph closure;
- traits, requirements, coercions, types, binders, calls, and ownership;
- expression, pattern, place, statement, control, and whole-program typing;
- staging classification and materialization; and
- fuel-free successful big-step evaluation, positive fault propagation,
  heaps, values, defaults, and primitives.

The dynamic layer includes subject-reduction results for successful runs under
their stated closure and typing premises. These results do not imply progress,
termination, determinism, or exhaustive fault classification.

## Semantic Core

`Solcore.Core` is the syntax-independent executable intermediate language. It
owns:

- Core types, values, expressions, programs, and local stores;
- declarative typing and evaluation;
- executable checking and evaluation with detailed failures;
- CEK-style and host-aware machines;
- exact-fuel and resumption results;
- primitive arithmetic, bitwise, comparison, conversion, and shift rules;
- renaming, local-fragment, correspondence, progress, and safety results; and
- the current Core Wire encoding.

Core admits only what its checker proves. Source names, inference variables,
trait evidence, and source heaps cross this boundary only through explicit
elaboration or linking.

## Checked-contract execution

`Solcore.ContractRuntime` interprets admitted Core programs in an explicit
contract world. It owns accounts, balances, persistent storage, code
selection, transaction and frame state, host requests, nested calls, contract
creation, checkpoints, commit/rollback, logs, fuel, and observations.

This layer is distinct from both Core's local evaluator and the source dynamic
semantics. The distinction keeps local cells separate from world-state storage
and makes transaction effects explicit in types and judgments.

`Solcore.Abi` supplies Keccak-256 and the currently modeled static-word ABI
operations used at contract boundaries. ABI admissibility, decoding, and
encoding remain explicit prerequisites rather than implicit properties of a
source type.

## Reproducible Core synthesis

`Solcore.Synthesis.Core` generates a bounded pure Core fragment from an
explicit seed. Generated programs carry checker evidence. Its shrinker returns
only candidates that preserve the fragment invariants and are strictly
smaller according to the library's measure.

Synthesis targets Core directly. It is test-input infrastructure and does not
parse or compile source programs.

## Proof and trust boundary

Lean's kernel checks declarations and proofs. Executable functions are paired
with independent judgments and correspondence or safety theorems where the
current status records them. Tests exercise examples and regressions but do
not replace those statements.

Normal-completion preservation theorems do not assert termination and do not
exclude every runtime fault. Likewise, parser exactness does not imply source
type correctness, and Core safety does not establish correctness of every
source-to-Core lowering.

The repository kernel-policy check rejects configured escape hatches in the
semantic roots. Axiom reports for critical theorems should be read literally;
the accepted Lean foundations are documented by the check rather than hidden
behind an informal “trust zero” label.

## Dependency and change policy

- Put source grammar and AST changes in `Solcore.Syntax`.
- Put executable whole-program source processing in `Solcore.Frontend`.
- Put normative source judgments in `Solcore.SourceSemantics`.
- Put syntax-independent executable IR behavior in `Solcore.Core`.
- Put accounts, frames, transactions, and world effects in
  `Solcore.ContractRuntime`.
- Put hashing and supported call-data encoding in `Solcore.Abi`.
- Put seeded Core generators and shrinkers in `Solcore.Synthesis`.

Changes that cross layers must use an explicit adapter and state which layer
owns each failure. New executable coverage is not complete until its static,
dynamic, resource, diagnostic, and preservation obligations are either proved
or recorded as open.
