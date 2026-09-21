# ADR-0355: Direct staged-integer source calls

## Status

Implemented as a provisional executable extension of the ADR-0349–0354 closed
staging boundary.  The accepted profile consists of canonical whole-program
direct calls whose fully specialized inputs and single result are exact bare
`integer`, whose signature has no predicates, whose call and arguments have no
output coercions, and whose specialization path is acyclic.

## Context

ADR-0354 can erase declaration-local integer lets, but a checked source call
still crosses into another `TypedSource`.  Evaluating such a call requires more
than substituting its arguments into the caller's closed-expression evaluator:
local identities and requirement identities are function-local, the callee must
come from the validated specialization plan, and recursive expansion must share
the linker's existing cycle and depth controls.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` also carries separate
staging flags which the current Lean checked carrier does not yet reproduce.  A
source `Param` retains `paramComptime`, a signature retains `sigRetComptime`, and
those bits propagate to `MastParam.mastParamComptime` and
`MastFunDef.mastFunRetComptime`.  The reference rejects a definitely runtime
actual for an explicitly comptime parameter and classifies a call as comptime
only when its result is marked comptime and all actuals are comptime.

Lean's raw syntax retains the optional `comptime` span on a function parameter,
but `ProgramSignatures.resolveFunctionParameters` currently matches the marker
without retaining it in `ProgramFunctionSignature`, `TypedBinder`,
`CheckedFunction`, or specialization.  Lean does resolve a written
`comptime<T>` result structurally as `Ty.comptime T`, but it has no separate
canonical counterpart of the reference's `sigRetComptime` flag.  This ADR
therefore does **not** claim the reference's marker semantics.  It introduces a
deliberately provisional type-directed rule for bare `integer`: an unmarked,
fully specialized integer parameter and bare-integer result are staged only
while evaluating an otherwise accepted staged-integer call.

## Decision

### Keep whole-program identity and planning authoritative

Source Core exposes a source-typed `StagedIntegerCallPlan`.  A plan declares the
exact argument types and caller-local call requirements, then receives already
validated `Int` values in source order.  It returns only an `Int`; it cannot
return callee requirement identities or traverse caller expression edges by
itself.

The direct linker is the only current producer of this plan.  Before argument
evaluation it requires the complete specialization plan to reconstruct
canonically, resolves the declaration instantiation again, requires the exact
occurrence-addressed call edge, and checks that the edge names the same
specialization.  The call must be direct and predicate-free.  The callee
reference must retain its exact declaration instantiation and function type;
the call result, arguments, and callee inputs must each have exact bare
`integer` type and coercion-free metadata.  Indirect calls and any predicate or
output-coercion path remain outside this profile.

The worklist continues to retain every written direct-call occurrence,
including calls in an unselected conditional branch.  Folding a closed
conditional therefore neither removes an edge nor lowers the finite
specialization budget required to validate the program.

### Evaluate arguments and bind the callee locally

Source Core evaluates arguments left to right under the caller's current
staged environment.  Each argument must itself be a closed staged integer.
Argument requirements are concatenated in source order, followed by the call
node's own requirements.  In this predicate-free profile the latter list is
empty, but keeping it explicit prevents a policy from silently claiming or
reordering caller obligations.

Only the resulting `List Int` crosses the function boundary.  The callee
evaluator validates its owner, exact arity and function type, and requires every
input binder to be declaration-owned, unique, monomorphic, and exactly
`integer`.  It pairs values positionally with those stable local identities and
evaluates the callee's tail-normal integer body.  Integer lets remain strict;
tail returns, terminal blocks, and terminal statement conditionals are
supported.  Local lookup remains identity-based and a same-spelled nested
binder may shadow an input without aliasing it.

Requirement IDs are never transferred between ledgers.  Caller argument and
call-node requirements remain in the caller's consumed stream.  The callee
reconciles its literals, lets, nested calls, and both conditional branches
against its own `solvedRequirements` table before returning the bare `Int`.
This remains correct even when caller and callee use numerically identical
function-local `RequirementId` values.

### Share termination controls and retain eager validation

The linker's runtime-body builder and staged-function evaluator are mutually
fuel-recursive.  Both use the same canonical `SpecializationKey` visiting stack
and the same decreasing link-depth fuel.  Entering staging from ordinary
runtime lowering, or entering another staged integer function, therefore cannot
reset call-cycle detection.  Direct and mutual recursion reject explicitly.
The source-local node-table fuel still bounds malformed expression and statement
graphs within each callee.

Expression and statement conditionals keep the ADR-0353 eager policy: guard,
then branch, and else branch are all evaluated and their requirements are
concatenated in that order before selecting a value.  Consequently a recursive
call in a syntactically unselected branch still rejects.  This slice is an
acyclic closed evaluator, not a selected-branch recursive interpreter.

The staged result must still reach a supported consumer such as
`wordFromInteger` or an integer comparison.  Selecting an integer-returning
function itself as a runtime program root continues to fail because Semantic
Core has no runtime `integer` type or input representation.

Public standalone expression and function evaluators retain the closed-call
boundary.  Only the whole-program linker supplies the plan-aware policy, so an
isolated `TypedSource` cannot invent declaration resolution or reset global
termination state.

## Deferred boundaries

- Canonical retention and enforcement of the parameter `comptime` marker and a
  separate reference-style result flag, alongside Lean's existing structural
  `Ty.comptime T`, remain required before this provisional bare-integer rule can
  be generalized.
- General `comptime<T>`, staged Word/Bool parameters and locals, multiple return
  values, predicate-bearing calls, output or argument coercions, indirect calls,
  and calls depending on runtime values remain unsupported.
- Recursive staged execution, memoization, selected-branch recursion, and
  programs such as compile-time Fibonacci remain deferred.  The current eager
  branch policy and specialization-key cycle check intentionally reject them.
- An integer value may not survive into Semantic Core, and an integer function
  remains invalid as a runtime entry even when its body can be evaluated by a
  staged caller.
- Shared-DAG total-work controls, graph-wide ownership/reachability proofs, and
  broad staging, specialization, and lowering metatheory remain later
  hardening work.

## Verification

Whole-program regressions cover one- and multi-argument integer helpers,
repeated calls, nested calls, signed arithmetic before the outer Word modulo,
and eager calls in both conditional branches.  Worklist checks retain FIFO
specialization order, every occurrence-addressed edge, and exact budget
exhaustion.  Requirement regressions deliberately reuse the same numeric IDs in
caller and callee and confirm that each ledger reconciles independently.

Adversarial tests mutate call type, requirements, coercions, policy arity,
argument type, callee function/input type, binder owner, quantification,
identity, reference spelling, plan edges, and signature predicates.  Separate
self-, mutual-, and unselected-branch recursion cases confirm shared visiting
and depth control.  The standalone evaluator still rejects an ordinary call,
an integer runtime root still rejects before Core, and the complete test suite
retains all pre-existing runtime and staging behavior.
