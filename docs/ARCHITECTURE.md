# Architecture

solcore-lean separates source representation from language meaning. This lets
the syntax evolve without forcing the executable semantics to be rewritten.

## Layers

    source text
      -> versioned Surface parser
      -> Surface-to-Resolved adapter
      -> resolved and typed semantic input
      -> Semantic Core
      -> contract runtime
      -> canonical observation

Only some of these arrows exist today. The architecture treats each arrow as a
separate executable transformation with its own declarative relation and proof
boundary.

### Surface

Surface owns concrete spelling, tokens, comments, grouping, and source spans.
The published Surface v1 parser is stable. The larger Multi parser is an
internal reference for a frozen grammar.

Surface data is not semantic identity. A source span cannot stand in for a
declaration, scope, variable, function, or module identity.

### Resolved input

Resolved input will replace source spellings with structured identities and
will make scope ownership and module selection explicit. Its contract should
depend on abstract declarations and occurrences, not on a particular parser
implementation.

No executable Resolved language exists yet. During the semantics-first phase,
Core and runtime work must not depend on the unfinished Multi AST.

### Semantic Core

Semantic Core is the executable language definition. It owns:

- value and type algebras;
- declarative typing;
- big-step dynamic semantics;
- a deterministic CEK-style machine;
- executable inference, checking, and evaluation;
- correspondence between relations and executors; and
- progress, preservation, and fault-exclusion results.

The existing Core v2 fragment is closed and published. New features extend the
internal Core additively. Old wire languages remain projections and must
reject new constructors.

Core vNext includes local mutation through explicit typed cells. Cell
references are ordinary internal values, while the local store is a separate
component of evaluation and machine state. Closures capture references in
their lexical environments; they do not copy the store. This makes sharing
explicit and keeps the semantics independent of host-language mutation.

The completed initial cell slice stores only first-order data: unit, boolean,
word, and products or sums made recursively from those types. Function-valued
and cell-valued contents wait for the recursion-and-divergence decision because
higher-order cells can encode nontermination.

The completed named-data slice gives each internal Core program an immutable
definition table. A data type is identified by its position in that table; a
constructor is identified by its owning type and position within that type.
These are local semantic identities, not source names. Definitions may be
recursive or mutually recursive, while runtime values remain finite.

Named-data matching is a normalized Core operation. Its branch list is
exhaustive and follows constructor-table order, and the selected constructor's
single payload becomes de Bruijn index zero. An explicit result type also
supports elimination of an empty data type. Source wildcards, nested patterns,
guards, arm ordering, names, and field shapes belong to a later resolved
adapter, not this execution layer.

The completed boolean/word conversion slice is deliberately smaller than an
algebra extension. `boolToWord` expands to a conditional selecting word zero or
one, and `wordToBool` expands to a nonzero test built from existing primitives.
The operand occurs once in either expansion. Because there is no new expression
tag, the existing evaluator, CEK machine, safety results, and wire projections
remain the architectural boundary; the slice adds named builders, focused
theorems, and tests rather than parallel semantics. Dedicated typing, inference,
evaluation, store-threading, and weakening results, plus effect, exact-fuel, and
wire regressions, are complete.

This conversion layer is not an ABI layer. Total nonzero truthiness and strict
ABI zero-or-one admissibility are separate rules. ABI byte layout, validation,
decoding, and rejection remain in the future contract boundary.

The completed `wordIsZero` slice follows the same derived-expression boundary.
It has type `word -> word`, returning word one for zero and word zero for every
nonzero input, and expands to existing equality and `boolToWord` expressions.
It is distinct from `wordToBool` truthiness and from ABI decoding. No new Core,
CEK, wire, or Oracle tag is added: wire v1 rejects the required primitive form,
while wire v2 projects the ordinary existing expansion.
Dedicated typing, inference, evaluation, store-threading, expansion, and
weakening theorems, plus effect, exact-fuel, type-error, boundary, and wire
regressions, complete this proof boundary.

The completed short-circuit boolean slice is another derived-expression boundary.
`boolAnd(x, y)` expands to `ifE x y false`, while `boolOr(x, y)` expands to
`ifE x true y`. The left operand runs once and first; the right operand runs
only in the selected branch. This store, fault, and fuel behavior follows the
existing conditional semantics and adds no Core, CEK, wire, or Oracle tag.
Eager ordinary reference calls are comparison evidence, not authority over the
selected-branch-only decision fixed by ADR-0011 and ADR-0026.
Named expansion, typing, inference, and all four store-threaded branch theorems
are complete. Tests cover truth, operand types, skipped and selected faults,
allocation and writes, left-to-right store threading, exact fuel, weakening,
and exact wire v1 and v2 projection.

The completed `wordIsNonzero` slice composes the existing conversions as
`boolToWord(wordToBool(x))`. It maps zero to word zero and every nonzero word to
word one, evaluates `x` exactly once, and preserves its final store. It is a
word-valued predicate rather than boolean truthiness or strict ABI decoding,
and introduces no new semantic or wire tag.
Its canonical expansion, typing, inference, general and zero/nonzero
store-threaded evaluation, and weakening interfaces are complete. Value,
type/fault, 9/10 fuel, exactly-once allocation/write, distinction, and exact
v1/v2 wire tests pass with the repository audits.

### Contract runtime

The future runtime will make all external state explicit: storage, balances,
call frames, transaction inputs, logs, created contracts, and rollback state.
That world state is distinct from the Core-local cell store. The local store
uses transient locations for one Core execution; it does not define contract
storage keys, persistence, transaction boundaries, or rollback. Neither layer
may obtain meaning from compiler output or hidden host state.

### Observation

Observations are canonical, versioned semantic results. Contract observations
will record normative state effects rather than bytecode layout, optimizer
traces, generated names, or wall-clock behavior. Gas belongs to a separate
fork-pinned profile.

## Proof pattern

Each semantic feature follows the same vertical structure:

| Concern | Required artifact |
| --- | --- |
| Intended meaning | Independent typing and evaluation judgments |
| Execution | Total checker and explicitly state-threaded evaluator |
| Static correspondence | Checker soundness and completeness |
| Dynamic correspondence | Machine and big-step agreement |
| Safety | Progress, preservation, and typed result properties |
| Local state | Explicit store threading, typed allocation/update, and final-store agreement |
| Named definitions | Whole-table validity, stable constructor ownership, and recursive finite-value reasoning |
| Derived expressions | Expansion typing, exact result semantics, exactly-once use, and unchanged version boundaries |
| Resource behavior | Explicit fuel or a proved finite bound |
| Compatibility | Old wires reject new syntax; derived forms preserve existing projection behavior |
| Regression protection | Positive, negative, order, boundary, and version tests |

An executable function is not used as its own specification.

## Version boundaries

| Boundary | Role | Change policy |
| --- | --- | --- |
| Semantic Core v1 / Oracle v2 | Frozen historical Core | No reinterpretation |
| Semantic Core v2 / Oracle v3 | Current published Core | No reinterpretation |
| Surface v1 / Oracle v4 | Current published parser | No reinterpretation |
| Internal Multi frontend | Frozen grammar reference | No active grammar proof expansion |
| Core vNext | Active internal semantics | Additive and unpublished |

A future publication receives a new schema, profile, capability report, limits,
golden corpus, and Oracle version. Internal progress never changes an existing
profile.

## Dependency policy

Work is ordered by exposure to syntax churn:

1. Core values, typing, evaluation, and machine proofs.
2. Explicit contract state and observations.
3. Resolved static semantics over abstract identities.
4. Surface adapters and source diagnostics.
5. Concrete parser updates and grammar-specific proofs.

The first two groups can proceed while the concrete language syntax is under
revision. The final two resume only after a syntax version is deliberately
stabilized.

## Repository map

| Location | Responsibility |
| --- | --- |
| Solcore/Core | Semantic Core, its local value store, and current Core proofs |
| Solcore/Semantics | Future cross-feature and runtime semantics |
| Solcore/Surface | Published Surface v1 |
| Solcore/Surface/Multi | Frozen internal Multi frontend |
| Solcore/Workspace | Pure workspace identity and validation |
| Solcore/Oracle | Versioned external protocols |
| schema, profiles, Tests/golden | Published compatibility artifacts |
| docs/adr | Durable semantic and architectural decisions |
