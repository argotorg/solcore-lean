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

The completed word-comparison-flags slice derives `wordEqFlag` and `wordGtFlag` by
converting the existing boolean equality and unsigned greater-than results to
canonical word one or zero. Operands retain left-to-right, exactly-once store
and fault behavior. Existing boolean comparisons remain unchanged, and no Core
or wire tag is added.
Named expansion, typing, inference, general and four case-specific
store-threaded evaluation, and weakening results are complete. Value, boundary,
type, fault-order, two-operand effect, exact-fuel, boolean-preservation, and
exact wire regressions pass with the repository audits.

The completed renaming foundation provides binder-aware `Expr.rename`,
context-respecting preservation of expression and branch typing, structural
relations for values, environments, and stores, and `Evaluates.rename` for all
evaluation forms. Renamed closures retain related bodies and captured
environments rather than requiring false raw equality. `CellPayload` exactness
recovers equal ground values and typed stores, and the word head-insertion
corollary preserves the exact word and final store. Static and dynamic tests
cover binders, closures, application, cells, named data, and effects. This
changes no Core execution or wire behavior.

The completed ADR-0030 slice retains the ADR-0011 definitions of `wordNe`,
`wordLt`, `wordLe`, and `wordGe`. All four provide named expansion, typing,
inference, renaming, weakening, store-threaded evaluation, and two truth-case
results. `wordNe` and `wordLe` evaluations need no typing assumptions;
`wordLt` and `wordGe` use typed store-threading. The nested-let
shape of `wordLt` and `wordGe`, including weakening the right operand under the
left binding, is part of the semantic boundary: it preserves left-to-right,
exactly-once effects and fault order. A syntax-level operand swap is not an
equivalent implementation for arbitrary expressions. This work adds proofs and
tests only; it does not add a Core form or change a wire or Oracle contract.
Tests cover values, types, exact fuel, faults, effects, Wire v1 rejection, and
exact Wire v2 projection and round trips.

The completed ADR-0031 slice applies `boolToWord` to the existing boolean
`wordNe`, `wordLt`, `wordLe`, and `wordGe` builders. These derived flags return
canonical word zero or one. They inherit left-to-right exactly-once evaluation,
fault order, effects, final stores, and fuel from the established expansions;
in particular, the nested-let less-than forms are not replaced by operand
swaps. Four general and eight case evaluations accompany expansion, typing,
inference, renaming, and weakening results. Tests cover values, types, exact
fuel, faults, effects, Wire v1 rejection, and exact Wire v2 projection and
round trips. A faulting right expression in the less-than forms is weakened
under the internal binding, so its variable index is lifted while the completed
left store is retained. No Core form, wire tag, or published behavior changes.
The next feature is selected by a separate ADR.

The completed ADR-0032 slice fills a static API gap left by the order of earlier
work. `boolToWord`, `wordToBool`, `wordIsZero`, `wordIsNonzero`, `boolAnd`,
`boolOr`, `wordEqFlag`, and `wordGtFlag` gain arbitrary renaming laws in their
owning modules. `rename_boolToWord` moves from the later derived-comparison-flag
module to `Conversions`. The non-insertion `swap01` golden exchanges free
variables zero and one; corresponding-environment evaluations cover conversion,
short-circuit, and comparison-flag witnesses. Existing weakening, evaluation,
store, fault, fuel, and wire behavior remain unchanged. The next feature is
selected by a separate ADR.

The completed ADR-0033 slice keeps boolean negation and word complement as direct
`.unary` expressions. Named typing, inference, store-threaded evaluation cases,
arbitrary renaming, and weakening theorems make the existing primitives easier
to use without adding aliases. Zero, maximum, and universal involution theorems
characterize word complement. Boundary and effect tests cover both boolean
values, exact 2/3 and 14/15 fuel, raw faults, final stores, Wire v1 rejection,
and exact Wire v2 projection and round trips. Generic Safety and machine
correspondence remain unchanged, as do semantics, tags, and bytes. The next
feature is selected by a separate ADR.

The completed ADR-0034 slice adds focused reasoning interfaces for direct unsigned
word division and modulo. The raw binary form keeps numerator on the left and
divisor on the right. A zero divisor produces zero only after both operands
evaluate exactly once in order, so effects, faults, and final stores remain
visible. Four Word, two apply, and six evaluation theorems cover normal and zero
divisors. Tests include `0 / 0`, types, raw and ordered faults, two effectful
operands, exact 4/5 and 28/29 fuel, Wire v1 rejection, and exact Wire v2
projection and round trips. Generic typing, renaming, weakening, Safety, machine
correspondence, tags, and bytes do not change. The next feature is selected by
a separate ADR.

The active ADR-0035 slice completes focused interfaces for the existing raw
logical shifts. Core keeps the value on the left and the shift amount on the
right, evaluates both exactly once in that order, and returns zero for amounts
of 256 or more. Fourteen named value, application, and store-threaded evaluation
theorems are required without aliases, new tags, or duplicate generic proofs.
Arithmetic shift, source spelling, opcode lowering, and gas remain outside the
slice. Parser-specific proof work remains paused under the semantics-first plan.

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
