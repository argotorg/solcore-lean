# ADR-0368: Bundled indirect application and finite runtime call-graph linking

## Status

Accepted for the restricted structural whole-program source profile.  The
specialization worklist discovers first-class declaration references, the
graph linker lowers direct calls, lambdas, and coercion-free indirect calls to
one checked finite runtime table, and the public single-seed runner uses that
table when authoritative Core inlining cannot represent the program.  This
completes roadmap phase 6, runtime call-graph generalization.

## Context

ADR-0366 and ADR-0367 provide a checked runtime target, but a source program
still needs a complete finite set of specialized definitions and an exact
translation from typed occurrences.  The existing worklist followed only
syntactically direct calls and rejected every indirect call.  A declaration
used as a value could therefore name a function absent from the specialization
plan, while recursively inlining direct calls continued to reject runtime
cycles.

The existing direct linker also remains substantially more capable for its
acyclic domain: it owns evidence-aware operator and coercion execution,
comptime staging, and independently checked Semantic Core output.  Runtime
graph support must extend that path without silently replacing its diagnostics
or weakening those checks.

## Decision

### Discover calls and first-class references separately

The specialization plan now retains `ReferenceEdge` alongside `CallEdge`.
Every standalone source-declaration reference is resolved through the same
canonical request boundary, added to the FIFO specialization frontier, and
recorded at its exact caller occurrence.  A reference that is merely the
callee child of a direct call is excluded from this second edge set because the
call edge already represents it.

Indirect-call metadata is validated by the worklist, but the indirect call
itself adds no guessed static target.  Its callee expression supplies the
runtime value; any referenced named functions inside that expression are
discovered by their own reference occurrences.  Repeated canonical keys still
close finitely, and type-growing recursion still exposes the existing distinct-
specialization budget frontier.

### Lower the complete plan once

`SourceRuntimeLinking.link` first revalidates the complete canonical plan
against the checked program.  Seed keys, specialization order, direct call
edges, first-class reference edges, and every known caller/callee key must
match reconstruction; a caller cannot inject or omit a reference edge before
graph lowering.

The linker then lowers every specialization to one
`SourceRuntime.Definition`, checks the entire table, and reconstructs entries
in seed order.  Direct calls become application of a named global.  Declaration
references become checked global values.  Lambdas retain stable parameter
identities and lexical bodies.  Indirect calls lower the callee and each source
argument separately, verify their typed-IR before/after bundle metadata, and
use the ADR-0367 application convention.

The current graph profile accepts only Unit, Bool, Word, product, and function
types; tail-normal initialized lets, returns, blocks, two-branch conditionals,
lambdas, direct and indirect calls, and requirement-free builtin operations.
Checked builtin `Int<Word>` literal obligations are the sole requirement-bearing
exception.  A runtime definition with unresolved assumptions or other evidence
requirements rejects.  Parameter, local, or result `comptime` markers reject,
as do polymorphic locals, unsupported nominal forms, and general coercion
paths.  In particular, indirect argument-bundle coercions and result coercions
remain deferred rather than being approximated or erased.

### Preserve the established linker as authority

`SourceProgramExecution.prepare` first invokes the established direct Core
linker.  When it succeeds, behavior is unchanged.  Only when it rejects does
the pipeline try the additive graph linker.  If the graph linker also rejects,
the public error remains the original evidence-aware direct-linker diagnostic;
the narrower fallback does not replace it with a less capable error.

A successful graph entry keeps the existing `LinkedEntry` shape for clients:
it contains a type-correct closed first-order inspection value and separately
attaches the authoritative checked runtime table.  Execution detects that
table and dispatches by the entry's specialization key.  Because no closed
inspection value exists for a function result, function-valued public results
are rejected at this bridge.  `PreparedEntry.usesRuntimeCallGraph` exposes
which execution mode was selected without exposing or reinterpreting the
table's internal runtime errors.

The established compatibility return type is `Core.StatefulRunResult`, so
graph-only runtime details remain intentionally opaque at that boundary.
`LinkedEntry.run?`, `PreparedEntry.run?`, and `SourceProgramExecution.run`
derive solely from the exact execution result: a successful projectable value
is returned exactly, out-of-fuel retains the exact store in an inert Core
state, and a graph runtime fault becomes the existing Core fault carrier with
the exact store but without exposing `SourceRuntime.RuntimeError`.  The inert
state is not a resumable graph continuation; graph fuel is a depth budget.

New callers can retain the backend distinction.  `ExecutionResult` is either
`.core Core.StatefulRunResult` or `.runtime SourceRuntime.RunResult`, and
`LinkedEntry.runExact?`, `PreparedEntry.runExact?`, and
`SourceProgramExecution.runExact` preserve the precise graph completion,
store-only exhaustion, or `RuntimeError`.  `usesRuntimeCallGraph` still exposes
the selected mode without requiring an execution.

## Phase boundary

Roadmap phase 6 now includes:

- finite direct and mutual runtime recursion without cyclic body inlining;
- canonical discovery of named functions used as first-class values;
- full reconstruction validation of specialization, call, and reference edges;
- lexical source closures and higher-order local/parameter/result passing
  inside the graph;
- checked bundled indirect application, including multiple source arguments;
- public fallback execution under `Limits.executionFuel`; and
- exact backend-tagged completion, fault, and fuel exhaustion with store
  retention, plus the legacy opaque Core projection.

Still deferred are:

- evidence-bearing or comptime runtime definitions beyond the builtin Word-
  literal obligation;
- indirect argument and result coercions in the graph path;
- nominal data, constructors/members, assignment, mappings/proxies, indexing,
  loops and broader control flow;
- function-valued public results and a graph result encoding in a published
  Oracle or wire protocol;
- automatic entry discovery, multi-root public execution, and a source Oracle;
- total-work accounting, runtime memoization, and type-growing polymorphic
  recursion beyond the specialization budget; and
- broad type-safety, linking-correctness, fuel, closure, and source/runtime
  correspondence proofs.

## Verification target

End-to-end source checks execute runtime countdown and factorial, finite mutual
`even`/`odd` recursion, a lexically capturing closure passed through another
function, a capturing closure returned from an internal helper, a two-argument
lambda, erased product/multi-parameter and Unit/zero-parameter application, and
conditional selection of named increment or decrement functions.  A tampered
specialization body and a missing canonical reference edge reject before graph
lowering.  `runExact` distinguishes a normal graph completion, store-only graph
fuel exhaustion, and an embedded Core-closure fault with its exact
`RuntimeError` and store; a small legacy execution bound still projects to
public Core out-of-fuel without claiming a resumable graph checkpoint.  Existing
acyclic and staged programs use the `.core` exact carrier and continue to take
the established direct Core path.
