# ADR-0180: Compiled-function observation invariance

- Status: Accepted
- Decision date: 2026-09-08
- Scope: exact execution and cost across independently compiled declarations

## Decision

Prove that independently compiled restricted declarations with the same
ordered parameter type context and exact Core expression have the same runtime
observations for every common actual typed argument list, fuel, and initial
store. The two declarations may use different type-name tables, declaration
owners, parameter/function spellings, source ranges, or grouping.

The compiled return types agree by existing Core typing uniqueness; derive
that equality rather than requiring it as a redundant premise. Context equality
concerns ordered Core types, not parameter names, generated identities, or
whole static input records. Exact Core equality concerns the actual elaborated
tree, not equality of eventual values or algebraic equivalence.

The runtime equality is unconditional on argument acceptance. Both declarations
reject the same arity/type-order mismatches; matching supplied arguments retain
their actual values and yield identical full stateful results, including every
zero-fuel and suspended state. Reuse execution factorization from ADR-0179.

## Independent cost correspondence

Transport independent `RuntimeFunctionEvaluatesWithCost` evidence in both
directions, preserving the same actual arguments, initial and final stores,
result type, value, and exact cost. Use the all-fuel execution equality together
with the existing characterization of completed execution and both exact cost
thresholds. No new termination, typing, allocation, or type-inhabitation premise
is necessary, and no new runner or evaluation relation is introduced.

Publish a small proof interface: return-type equality, full runtime equality,
and independent cost equivalence under the two compilation witnesses, ordered
context equality, and exact Core equality. Independent compilation remains
mandatory; hand-built records alone do not establish source correspondence.

## Boundaries and validation

Use independent declarations and fully parsed pairs with renamed parameters,
type aliases, distinct owners, and different ranges/grouping. Check actual
compiled context/Core equality before comparing all supplied arguments and
complete machine results. Include a composite arithmetic comparison and its
conditional cost where useful, not only one literal example.

Counterexamples must distinguish necessary premises. Unused parameters with
different arity or ordered types can leave Core and result unchanged but change
argument acceptance. Returning a Word and adding zero to it have the same
eventual value yet different Core trees, costs, and suspended states. Equal
argument type lists do not allow replacing actual values on one side.

Register every public theorem, keep new files below 300 lines, and run focused
and aggregate builds, full tests, standard-axiom, kernel, metadata, forbidden
proof-token, and whitespace checks. Commit small exact-path units and preserve
unrelated diagnostic work without extending it.
