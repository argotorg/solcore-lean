# ADR-0169: Single-return canonical body semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: a restricted canonical body adapter over existing local expressions

## Decision

Interpret exactly a canonical `Syntax.Block` containing one return statement.
A bare `return;` denotes Unit and elaborates to `Core.Expr.unit`. An expression
return delegates to the existing monomorphic local-expression elaborator,
retaining its exact checked Core and type. The block and return wrappers add
no Core operation. No separate Resolved body language is needed for this
shape-preserving adapter.

Empty bodies, multiple statements, declarations, nested blocks, expression-tail
forms, and a return followed by another statement are outside this adapter.
Do not silently drop preceding, following, or unreachable syntax. `none` means
unmapped or unsupported by this restricted checker, not generally invalid
source syntax. Existing expression restrictions and whole-child checking remain
unchanged, including an unresolved or ill-typed branch that execution would skip.

## Independent meaning and execution

Define independent body typing, value/store evaluation, and cost evaluation
judgments. Each has a bare-return rule and an expression-return rule that uses
the corresponding existing independent source judgment. Their premises must
not contain successful body checking or execution.

Bare return has type Unit, yields the Unit value, preserves the store, and
costs one transition. Expression return retains the expression's value, both
stores, and exact cost. These are compiled Core-transition counts, not a
general cost for source returns, function calls, or return-control handling.
Prove raw evaluation and cost determinism, store preservation, cost erasure,
existence, and positivity without adding whole typing or resolution premises.

Prove body typing iff checked elaboration exists at that type, exact checked
Core typing, and checked source/Core evaluation correspondence under runtime
identity-order alignment. Typed aligned inputs supply a result of the checked
type, sufficient execution fuel, and fault exclusion. Use existing typed
`LocalInputs` projections for a checked body runner. At fixed fuel, completion
is equivalent to whole body typing plus the independent matching cost at most
that fuel; present exhaustion corresponds to a greater cost. Do not equate
suspended states across different environments.

The resulting type is inferred for this body alone. Checking it against a
function signature, interpreting generic/where constraints and modifiers,
function invocation, escaping from nested control flow, and unwinding caller
continuations remain separate. The adapter does not implement general early
returns, mutable locals, loops, or source function definitions.

## Validation

Use independent rule consumers and actual fully parsed canonical bodies.
Cover bare return at fuel zero/one, expression cost preservation, parsed
parameters feeding returned expressions, nonempty stores, and returning typed
closures or unallocated cell references without executing/dereferencing them.
Keep raw skipped-branch evaluation distinct from checked failure, and test
parseable unsupported body shapes as well as malformed or partial source text.

Audit all public declarations against the permitted standard kernel axioms;
run focused and aggregate builds, full tests, and kernel-policy and whitespace
checks. Keep new proof files below 300 lines. No existing parser, expression
semantics, Core machine, or wire-format behavior changes.
