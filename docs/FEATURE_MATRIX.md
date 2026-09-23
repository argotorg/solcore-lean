# Feature matrix

This matrix summarizes the current Lean implementation. “Complete” means the
named boundary is implemented and has the locally required executable and
proof obligations. It does not imply end-to-end compiler or EVM conformance.
“Partial” names a usable but deliberately restricted boundary. “Planned” means
the repository makes no present implementation claim.

## Canonical syntax

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Source identities and spans | Complete | `Solcore.Syntax.Identifier` and syntax records retain file identity and locations |
| Lexing | Complete | `Solcore.Syntax.Lexer` produces tokens, comments, and lexical diagnostics |
| Complete-file parsing | Complete | `Solcore.Syntax.Parser` exposes the public parse result |
| Diagnostics and recovery | Complete | Malformed input remains an ordinary diagnostic-bearing result with recovery nodes |
| Declarative grammar | Complete for the implemented AST | `Solcore.Syntax.DeclarativeGrammar` and component grammar modules |
| Parser soundness/exactness | Complete at the exported boundaries | Component and public-file property modules under `Solcore.Syntax.Parser` and `Solcore.Syntax` |
| AST validity | Complete for retained declaration collections and Core terms | `Solcore.Syntax.CollectionValidity`, `CallableDeclarationValidity`, `ContractDeclarationValidity`, and `CoreTermValidity` |

Parsing does not by itself establish module resolution or source typing.

## Workspace and frontend

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Library/module path validation | Complete | `Solcore.Workspace` |
| Program loading and module catalog | Complete for the current workspace model | `Solcore.Frontend.ProgramLoading` and `ProgramEnvironment` |
| Imports, exports, aliases, and hiding | Complete for the current grammar | `ProgramImports`, `ProgramInterfaces`, and `ProgramModuleResolution` |
| Stable declaration identity | Complete | `ProgramIdentity` |
| Source type algebra, substitution, and unification | Complete for current types | `Solcore.TypeSystem` |
| Signature and type-name resolution | Complete for modeled declarations | `ProgramSignatures` and `ProgramTypeResolution` |
| Trait and implementation-method resolution | Partial | Executable bounded search with explicit inconclusive outcomes; unrestricted coherence is not claimed |
| Expression and body inference | Partial | Broad current expression/statement coverage; unsupported forms fail explicitly |
| Staging and specialization | Partial | Implemented for supported typed IR and roots; not every nominal/effectful value is materializable |
| Direct source-to-Core elaboration | Partial | Supported specialized bodies only |
| Finite call-graph linking/execution | Partial | Finite checked definitions, recursion, closures, and indirect calls in the admitted fragment |
| Typed-source execution | Partial | Supported typed terms and heap operations; not a universal fallback for all syntax |
| Whole-program compiler | Partial | Explicit workspace and root, deterministic backend selection, no automatic entry discovery |

## Declarative source semantics

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Context and well-formedness judgments | Complete for modeled records | `Solcore.SourceSemantics.Context` and `WellFormed` |
| Generic instantiation and substitution | Complete for modeled source terms | `Instantiation`, `Substitution`, correspondence and preservation modules |
| Traits, requirements, and coercions | Complete as declarative relations | `Traits`, `Requirements`, and `Coercions` |
| Expression and statement typing | Complete for retained resolved forms | `Typing`, `Static`, `Control`, and program judgments |
| Staging classification | Complete for modeled occurrences/programs | `Solcore.SourceSemantics.Staging` |
| Successful big-step evaluation | Complete for retained dynamic forms | `Solcore.SourceSemantics.Dynamic` |
| Positive fault relations | Partial | Modeled failures and propagation; exhaustive or unique fault classification is not claimed |
| Subject reduction | Complete under stated premises | Dynamic preservation and whole-language preservation modules |
| Progress, determinism, termination | Planned | No general theorem is claimed |
| Executable/declarative whole-frontend correspondence | Planned | Local correspondences exist; one universal theorem is not claimed |

## Semantic Core

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Unit, Boolean, Word, product, sum, and function values | Complete | `Solcore.Core.Data` and `Syntax` |
| Bindings, conditionals, cells, data, and matching | Complete | Core syntax, typing, evaluation, checker, and machine modules |
| Declarative typing and evaluation | Complete | `Typing` and `Eval` |
| Executable checker | Complete | `Check`, including detailed failures |
| Fuel-bounded evaluator | Complete | `Eval`, exact-fuel and resumption properties |
| Local CEK-style machine | Complete for Core execution | `Machine` and safety sections |
| Host operations and host machine | Complete for the frozen host context | `Host`, `HostMachine`, `HostRunner`, progress and safety modules |
| Word primitive algebra | Complete for current operators | Dedicated arithmetic, division, shift, conversion, bitwise, and comparison modules |
| Renaming and local fragments | Complete | `Renaming` and `LocalFragment` |
| Core Wire v1 | Retained | Closed base encoding in `Solcore.Core.Wire` |
| Core Wire v2 | Retained | Closed encoding in `Solcore.Core.Wire.V2` |
| Core Wire v3 | Complete/current | Strict current encoding in `Solcore.Core.Wire.V3`; see [catalog](CORE_WIRE_V3.md) |

## Checked-contract runtime

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Accounts and world state | Complete for current model | `Account`, `WorldState`, and property modules |
| Balances, nonces, code, and sparse storage | Complete for current model | Dedicated world-state and transfer modules |
| Checked Core program admission | Complete | Checked-program and checked-contract wrappers |
| Top-level transaction execution | Complete for modeled outcomes | `TopLevelExecution` and `BalancedTopLevelExecution` |
| Frame checkpoints and commit/rollback | Complete | Frame checkpoint, resolution, journal, and continuation modules |
| Storage host handling | Complete for current host operations | Host storage input, context, handler, and driver modules |
| Ordered Word logs | Complete | Checked log and transaction journal modules |
| Nested calls | Partial | One-level nested transition and execution model |
| Contract creation | Partial | Checked templates, preflight, initializer, address policy, and installation; not an EVM creation model |
| Typed observations and deltas | Complete for current state model | Outcome, log, storage delta, and world-state delta modules |
| Unbounded call stack | Planned | No claim |
| EVM gas, fees, blocks, or bytecode equivalence | Planned | Outside the current model |

## ABI and synthesis

| Feature | Status | Evidence and boundary |
| --- | --- | --- |
| Keccak-256 | Complete for the implemented function | `Solcore.Abi.Keccak256` |
| Static Word ABI | Complete for current call boundary | `Solcore.Abi.StaticWord` |
| General dynamic ABI | Planned | No claim |
| Seeded pure Core v3 generation | Complete for the admitted Word/Boolean fragment | `Solcore.Synthesis.CoreV3.Generator` |
| Checker-sealed output | Complete | Generated results retain successful checking evidence |
| Scope-preserving strict shrinking | Complete for the generated fragment | `Solcore.Synthesis.CoreV3.Shrink` |
| Function/data/cell/host-effect generation | Planned | Outside the current fragment |

## External evidence

| Comparison | Status | Valid claim |
| --- | --- | --- |
| Canonical syntax corpus against pinned implementations | Partial evidence | Can identify lexical, parse, AST, or diagnostic differences on aligned inputs |
| Source checking and elaboration | Unverified across implementations | Internal Lean execution does not establish cross-compiler agreement |
| Core execution | Lean-only boundary | External compilers do not consume the retained Core encodings |
| Contract execution | Lean-only boundary | No normalized end-to-end adapter to compiler-generated EVM exists |

See [Compatibility evidence](COMPATIBILITY_MATRIX.md) for baseline and
classification rules.

## Compatibility rule

Retained wire encodings are closed. Extending internal Core does not authorize
adding constructors to an older encoding. Any adapter between source,
frontend, Core, contract runtime, ABI, or synthesis layers must be explicit
and must preserve the failure information owned by the source layer.
