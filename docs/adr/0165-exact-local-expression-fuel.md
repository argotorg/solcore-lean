# ADR-0165: Exact Core fuel for canonical local expressions

- Status: Accepted
- Decision date: 2026-09-08
- Scope: proof-only cost semantics for the current monomorphic expression fragment

## Decision

Give successful canonical local-expression evaluation an independent natural
cost index counting Core transitions. Preserve all current source values,
initial and final stores, first-match lookups, literal meanings, and selected
branches. The cost relation is not defined by executable run success or by an
existential Core path: its leaf premises are the existing independent lookup
and literal relations, and its recursive premises are cost-indexed source
evaluations.

Identifiers and Word literals cost one transition. Grouping costs exactly its
child's cost. Boolean negation and Word complement add two to their operand's
cost. Binary Word bitwise operators cost left plus right plus three. A
conditional costs its condition plus its selected branch plus two.

For `&&`, a true left operand costs left plus right plus two; a false left
operand costs left plus three, including the generated false constant. For
`||`, a true left operand costs left plus three, including the generated true
constant; a false left operand costs left plus right plus two. A selected
short-circuit right operand can still return an arbitrary value at the raw
evaluation boundary. Unselected branches receive no evaluation, resolution,
typing, or cost premise. Both Word bitwise operands remain strictly evaluated
left to right.

## Proof interface

Prove erasure to the existing source evaluation, existence of a cost for every
existing evaluation, positivity, and joint uniqueness of result, final store,
and cost. These are raw source theorems without a whole-resolution or typing
premise. In particular, uniqueness must cover skipped unresolved branches and
cannot rely solely on a Core translation that those expressions lack.

Given a cost derivation, whole-expression resolution, and lowering against
the runtime environment's identity order, prove a Core path of exactly that
length. Generalize the continuation for compositional unary, binary, and
selected-conditional paths. No runtime typing premise is required for this
bridge once the successful source derivation is supplied.

Prove only the needed generic machine facts: two paths from one starting
state to terminal `State.final` states have the same length and endpoint; a
known terminal path completes exactly when fuel is at least its length; and
smaller fuel exhausts with a retained state. Do not claim length uniqueness for
arbitrary nonterminal endpoints. Detecting a final state consumes no extra
transition, so there is no extra final `+1` in the cost formulas.

Connect these facts to checked frontend execution and `LocalInputs.run?`.
Checking success, or independent whole source typing, remains essential:
raw evaluation may skip a branch that prevents checking. Typed aligned inputs
supply existence of a cost and a typed value; the supplied cost derivation
then fixes the exact same result and store at every sufficient fuel. Failed
checking remains `none`, whereas insufficient fuel after checking remains a
present exhausted result. This unit does not strengthen unused-name insertion
to equality of suspended machine states or introduce a cost-invariance API.

## Measurement and validation boundaries

This is a count of successful Core transitions, not gas, CPU or wall-clock
time, parsing/decoding/lookup complexity, or work performed by failing runs.
Span changes, grouping, and long numeric spellings do not imply any claim
about the time spent traversing frontend syntax. No execution algorithm,
parser, type rule, evaluation order, wire format, Oracle endpoint, capability,
or golden bytes change.

Consumers cover all cost formulas, exact completion and exhaustion thresholds,
nonempty stores, selected and skipped branches, raw untypable or unresolved
examples, and terminal path boundaries. Audit every public proof against
standard kernel axioms; run focused and aggregate builds, full tests, kernel
and metadata checks. Keep each new proof file below 300 lines.
