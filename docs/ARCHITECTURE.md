# Architecture

Solcore separates source representation, typed expression meaning, contract
execution, and observation. Each boundary has its own inputs and guarantees.
For examples and an explanation of what the theorems establish, read the
[semantics and guarantees guide](../manual/README.md). This document records
stable responsibilities; [Current status](CURRENT_STATUS.md) records the
revision-local implementation boundary.

## Layers

```text
source text
  -> canonical Syntax lexer and parser
  -> resolution and source checking
  -> specialization and supported elaboration
  -> Semantic Core
  -> explicit contract runtime
  -> canonical observation
```

The arrows describe separate transformations. Their existence does not imply
a general end-to-end source preservation theorem. The canonical parser, proven
local Resolved fragment, and newer executable whole-program frontend have
different supported boundaries. Oracle v5 begins at Core, not source text.

### Source syntax

`Solcore.Syntax` owns canonical spelling, tokens, comments, grouping, recovery
nodes, and UTF-8 source spans. ADR-0153 selects its syntax baseline. It is
independent of the frozen Surface v1 and Multi frontend representations.

The public parser retains ordinary malformed-source diagnostics in its output.
An output carrier is not evidence that a source file is diagnostic-free.
`ParseOutput.isDiagnosticFree` checks lexical and parse diagnostic lists; name
resolution and source typing are later obligations. Parser proof families
separately address provenance, progress, totality, grammar correspondence, and
specific AST/endpoint exactness boundaries.

### Identity, checking, and elaboration

Workspace, module, declaration, and local identities distinguish semantic
ownership from spelling and source location. Resolution selects identities;
source checking selects types, declarations, overloads, and evidence.
Specialization plans concrete declaration instances before restricted linking.

The local Resolved language has independent typing and evaluation relations.
Successful lowering connects named environments to positional Core, with
bidirectional typing and evaluation correspondence for that fragment. The
larger frontend retains independently checked output equations and restricted
acyclic linking. Those carriers must not be described as a general source
semantics preservation theorem.

Core and runtime semantics do not depend on source spelling. A source operator
can select an ordinary function; it does not automatically inherit the meaning
of a similarly named derived Core builder.

### Semantic Core

`Solcore.Core` owns the value and type algebras, declarative typing and
evaluation, executable checking, the CEK-style expression machine, and their
correspondence and safety results. Variables are positions in environments.
Closures retain captured environments. Continuation frames retain pending
work; their stack is not an EVM operand stack.

Evaluation threads an explicit local cell store. Binary expressions and pairs
evaluate left then right; conditionals evaluate only the selected branch.
Closures share captured cell references rather than copying the store.
Cell payloads are first-order unit, Boolean, Word, products, and sums. Function,
cell, and named-data payloads are excluded by the current cell predicate.
These restrictions matter to the pure Core termination argument.

Named data uses a program-owned immutable definition table. Constructor
identities record their owner and index. Definitions may be recursive while
runtime values remain finite. Core matches are normalized, exhaustive,
constructor-ordered branch lists; the selected payload becomes position zero.
Source guards, wildcard patterns, and branch rearrangement need a separate
frontend interpretation.

Derived expressions compose existing Core forms. Their expansions must retain
typing, operand order, exactly-once effects, and the appropriate final store.
A derived operator need not add a machine instruction or wire constructor.
Primitive value laws and expression-level effect laws are separate results.

Fuel counts abstract machine transitions. Exhaustion retains an actual state
and is inconclusive; resumption continues that state. Correspondence,
termination, sufficient-fuel, and exact-threshold results have distinct
premises. Model fuel is not EVM gas.

### Host requests and contract execution

Host-aware Core execution adds typed request emission and typed resumption for
storage, environment queries, input data, calls, creation, and logs. Its
progress result includes emitting a request. A raw machine fault is distinct
from an explicitly modeled failed call, revert, or trap.

`Solcore.Semantics` owns the runtime world and invocation. Accounts have
balances, nonces, optional checked code, and sparse Word storage. A missing
slot in a present account reads as zero. Account absence remains explicit;
world operations do not invent missing accounts. This persistent storage is
distinct from Core-local cells and from physical EVM memory.

Frames retain checkpoint and working state. Return selects working state;
revert selects the checkpoint. Generic frame helpers leave trap disposition
open, while root execution selects rollback on trap. State and rollback-scoped
effect journals resolve together. Trace components may retain attempted work
without treating it as a committed contract effect.

The published runtime supports checked depth-one nested Word calls, value
transfer, checked creation, and ordered Word logs. Root balance-preflight
rejection leaves the initial world and commits no effects. Exhaustion retains
resumable state instead of inventing a terminal world. Registries, creation
policy, immutable environment, and invocation data are explicit inputs.

Contract entry admission is separate from Core well-typedness. The static Word
ABI profile uses a four-byte selector, one 32-byte argument, and one 32-byte
result. Broader ABI values, general recursive calls, and EVM equivalence require
separate boundaries.

### Observation

Oracle v5 publishes terminal outcome and data, requested initial and committed
state endpoints, committed Word logs, and successfully created addresses.
Order and duplicates matter where the observation is a sequence.

Canonical scalar encodings and public wire contracts define exact text and
byte representations. Internal Lean types do not add public fields. Bytecode
layout, optimizer traces, generated names, and wall-clock behavior are not
standard semantic observations. Gas and fork-sensitive behavior need a separate
fork-pinned specification.

## Proof pattern

A theorem must be read at the boundary it actually states:

| Question | Relevant guarantee |
| --- | --- |
| Does executable checking recognize the rules? | Soundness and completeness against declarative typing |
| Does the machine implement evaluation? | Dynamic correspondence, including final stores |
| Can equal inputs produce different answers? | Determinism |
| Are typed executions safe? | Progress, preservation, and fault exclusion with matching runtime inputs |
| Does a computation finish? | Termination or sufficient fuel under the stated fragment assumptions |
| Can execution resume faithfully? | Equality with a larger run from the actual exhaustion checkpoint |
| Does a transformation preserve meaning? | An explicit typing/evaluation relation between its source and target |
| Which effects survive? | Checkpoint/working selection and observation laws |
| Does an older interface retain its meaning? | Closed projections, codec contracts, and compatibility checks |

The [guide's guarantee map](../manual/Guide/Guarantees.lean) explains these
families and their limits. Feature-by-feature inventories belong in Current
status and the feature matrix rather than this architecture document.

## Version boundaries

Core Wire v1, v2, and v3, Surface v1, and Oracle v1-v5 are closed published
boundaries. Internal additions do not expand them. Unsupported internal
constructors fail projection into an older algebra; publishing a new public
meaning requires an additive version and its format, profile, capabilities,
resource contract, and conformance material.

The [Core v3 catalog](CORE_WIRE_V3.md) and [Oracle v5 catalog](ORACLE_V5_WIRE.md)
are exact references. The [charter](SPEC_CHARTER.md) establishes their authority.

## Dependency policy

The semantic library uses Lean without external documentation dependencies.
The separate `manual/` Lake package pins Verso and imports the library through
a local path dependency. Native rich source docstrings can check Lean references
without adding Verso to the library's dependency graph.

Tests and executable frontends may depend on semantic layers. Semantic meaning
must not depend on a particular source parser, CLI, wire encoder, or manual.

## Repository map

| Location | Responsibility |
| --- | --- |
| `Solcore/Syntax` | Canonical source representation, lexer, parser, and parser proofs |
| `Solcore/Workspace`, `Solcore/Resolved` | Ownership, identities, scopes, and local semantic lowering |
| `Solcore/TypeSystem`, `Solcore/Frontend` | Source types, checking, evidence, specialization, and elaboration |
| `Solcore/Core` | Expressions, typing, evaluation, machines, safety, and closed Core wires |
| `Solcore/Semantics` | Runtime state, effects, calls, creation, and observations |
| `Solcore/Oracle` | Versioned query and response boundaries |
| `Solcore/Synthesis` | Checked generation, replay packaging, and shrinking |
| `Solcore/Surface` | Frozen historical source interfaces |
| `Solcore/Test`, `Tests` | Lean tests and command-line golden fixtures |
| `manual` | Checked reader guide and theorem explanations |
| `docs/adr` | Accepted decisions and historical rationale |
