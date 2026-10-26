# Core runtime unification and semantic preservation

Updated: 2026-10-27.

## Status and scope

The first goal is complete: native source execution uses Core, and the separate
typed-source runtime evaluator has been removed. The second goal is incomplete:
there is no general theorem connecting every successfully compiled native
source body to its independent meaning through the complete public execution
pipeline.

The [M0–M6 differential-testing milestones](semantic-differential-testing.md)
are complete for their documented bounded profiles. Those comparisons exercise
the pinned Rust dialect against original generated Core and imported Hull;
they do not finish the native source compiler's preservation theorem. The
[next implementation roadmap](next-implementation-roadmap.md) sets the order
for further testing and proof work.

This document replaces the migration progress, API and audit appendices.
Their dated checkpoints are available in Git history. The current API and
proof definitions below take precedence over those historical descriptions.

## Original goals

1. Preserve existing runtime behavior while replacing direct typed-source
   execution with compilation to Core and execution by the Core machine.
2. Prove that the actual source-to-Core transformation preserves observable
   meaning, including values, failures, heap effects and retained callable
   environments, through the public API.

The first goal concerns runtime execution. Unifying the native frontend's
comptime evaluator is a separate task. Connecting native source contract
members, persistent storage and external calls to `ContractRuntime` is also
separate; current native ABI discovery is limited to static Word roots. The
Rust Hull import path already has broader contract execution support and its
own [proof boundary](hull-meaning-preservation.md).

The proof target is a successful selected compilation: the requested roots,
their discovered dependencies and the callable instances actually compiled.
Checker acceptance alone does not guarantee that every declaration in the
workspace is executable. An unrelated unsupported declaration need not block
an executable selected entry. Do not replace this boundary with a requirement
that the entire workspace compiles, or with checker acceptance alone.

## Public runtime API

Import [SourceCompiler](../../Solcore/Frontend/SourceCompiler.lean). It exports
the same artifacts, values, sessions and checkpoints as
[SourceCoreExecution](../../Solcore/Frontend/SourceCoreExecution.lean); it is
not another evaluator.

| Operation | Public entry points |
| --- | --- |
| Check and compile selected roots | `compile`, `compileChecked`; `compileEntry` selects the entry point. |
| Open and initialize | `Compiled.open`, `Artifact.bootstrap`, `Bootstrap.resume`. |
| Execute a named root | `Session.start`, `Session.run`. |
| Retain and invoke functions | `Session.named`, `Session.builtin`, `Session.invokePacked`. |
| Resume suspended execution | `Checkpoint.resume`. |
| Observe and restore local state | `Session.snapshot`, `Checkpoint.snapshot`, `Session.restoreSnapshot`. |
| Discover a static Word ABI | `compileStaticWord`, `StaticWordProgram.rootForSelector?`. |

Use the session returned by a completed call for subsequent calls. Public
handles carry artifact/session authority; they are not raw Core references or
serializable source closures. Snapshot and handle restrictions are enforced by
the API. [Execution tests](../../Solcore/Test/SourceCoreExecution.lean) and
[snapshot tests](../../Solcore/Test/SourceCoreExecutionSnapshots.lean) provide
current executable usage examples.

`RunOptions` separates input validation, Core execution and output validation
budgets. Initialization can also suspend. The public outcomes distinguish
successful completion, language failure, an out-of-fuel checkpoint and an
output export error. Exhausted fuel is a resumable resource outcome, not proof
of source termination or a successful result. Core fuel and EVM gas are not the
same quantity.

Runtime support includes closures, recursive functions, mapping values,
mutable locals, compound values and function handles nested in data. Source
mapping values here are local language data; they are not an assertion that
native contract storage is connected to the account-world runtime.

## Established proof connections

Core typing and finite execution safety are established separately from
source-to-Core meaning preservation. Independent Source semantics provides
the source-side executions; running translated Core is not its definition.

The checker connection now derives validity of every ordinary-function and
implementation-method body in the selected compilation cache, including
later-discovered dependencies. It follows the actual inference calls,
initializer lifetimes, retained bindings and final substitution:

- [SourceCompiledActualInitializerBarriers.compile_cached_bodies](../../Solcore/SourceSemantics/SourceCompiledActualInitializerBarriers.lean)
  derives cached-body validity from successful compilation and its artifact.
- [SelectedCompilationRawPublicReceipt.of_compile](../../Solcore/SourceSemantics/CoreLowering/SelectedCompilationRawPublicReceipt.lean)
  retains the actual public compilation and prepared recipe.
- [Receipt.checker_bodies, checker_profiled and checker_initial_row](../../Solcore/SourceSemantics/CoreLowering/SelectedCompilationCheckerPublicProfile.lean)
  connect that receipt to body validity and the existing profiled public
  session. Initializer barriers and body typing are derived here rather than
  supplied independently. `StaticProfile` remains an explicit premise for
  the latter public connections.

Existing [profiled public sessions](../../Solcore/SourceSemantics/CoreLowering/SelectedCompilationProfiledPublicSession.lean)
connect supported source bodies to actual initialization, calls, resumptions
and retained histories. The broader proof library covers individual expression,
statement, loop, assignment, mapping and callable connections. Their exact
premises matter: a connected restricted profile does not imply coverage of
all compiler-accepted syntax.

The general accepted-body route starts from the actual compiler receipt of one
body invocation, `ActualBodyInvocation.Index`: a named cache row or a
materialized contextual closure. In
[CellAwareInvocationAcceptedFlow](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedFlow.lean),
`correct` closes the mixed-cell statement flows by induction over the actual
accepted compiler tree (`AcceptedNamedBodyFlow.Tree`), not over a Source
recognizer. Each branch uses the compiler's own read, child lowering, fuel,
scope and allocation receipt; fixed-control checker typing supplies the Source
facts. `body_preserves` and `body_reflects` compose it with the actual footer and
relate `index.body` to independent Source execution in both directions,
including failures, control transfers and the reached heap.

These theorems keep explicit premises. `Expressions` supplies meaning for
exactly the expressions the compiler accepted, at every compiler fuel; the
expression closure below discharges it only for a first subset of named-row
bodies. `Covered` admits returns, final values, discards,
`break`/`continue`, blocks, conditionals, `while` and `for` loops, monomorphic
initialized or uninitialized declarations, and bare and projected assignments
and bit-not updates when the compiler view is the original Source (as for named
rows). Write heads come from the tree's assignment receipts, the compiler's own
key and right-hand lowerings and the body's actual assignment policy
(`ActualBodyInvocation.Index.assignment_policy` and `bitNot_policy`). `for`
headers are closed by two further inductions over the compiler's header items
([CellAwareInvocationAcceptedForItems](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedForItems.lean));
their declarations are authenticated by the original compilation receipt.
Matches are closed under the same Source view
([CellAwareInvocationAcceptedMatches](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedMatches.lean)):
the tree's match receipt supplies the certificate, the scrutinee lowering and
the finite branch requests; each arm is the compiler's own request at its
original pattern context with the match's control, typed natively through the
match certificate; and the hidden scrutinee and pattern binders are non-inputs
by the body's runtime local-identity ownership. The checker run of the original
compilation receipt supplies the well-formed signature catalog. The tree does
not record a match receipt's compilation context, so `Covered` requires it to be
admitted (`Admitted`: the checked catalog's initial values, the body's own
allocator and definitions extended by the indexed layouts);
`AcceptedNamedBodyFlow.Tree.refine` builds its match receipts at its
policy-success context but does not state it. Generalized declarations are
closed through `CellAwareInvocationGeneralizedAcceptedAllocation` when their
initializer is a direct lambda without requirements or coercions and the
`CellAwareInvocationAcceptedInputs.Generalized` inputs hold: the captured-scope
descriptor attachment, the residual entry of a contextual invocation (trivial
for named rows) and the body's diagnostic issuer. For this the closure carries
the compiler's statement sites (`ActualBodyInvocation.Index.Site`) and also
concludes that every native typing of the emitted code has a Word failure
component
([CellAwareInvocationAcceptedNative](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedNative.lean));
that fixes the initializer's native type at its language result.
`Covered` excludes writes and matches under contextual metadata views, and it
requires a function-mode fallthrough to have Unit result and a final bare value
to have the declared result type. The
closure threads the Source context's signatures through declarations. The
caller also supplies Core typing of the compiled body, fixed-control checker
typing and the result projection; for an actual prepared named header,
[CellAwareInvocationAcceptedNamedHeaders.static_inputs](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedNamedHeaders.lean)
derives all three from checker certification and the cached body's Core typing.
The invocation's physical entry state, the original compilation receipt, and
the write inputs (`CellAwareInvocationAcceptedInputs.Writes`: fault
interpretation of the body's assignment diagnostic words, reached place
diagnostics and function identity views) remain inputs of these theorems. The
public connection below constructs the physical entry state for named rows
whose accepted expressions lie in the first expression subset.

The first expression closure is
[CellAwareInvocationAcceptedExpressions](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedExpressions.lean).
`Closed` states the covered subset as a predicate on the actual accepted
expression receipts: every expression the compiler accepts for the body, at any
fuel and scope, is a site of the subset (`InSubset`). For a named row these
sites are `Subset` of
[CellAwareInvocationAcceptedExpressionTrees](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedExpressionTrees.lean):
literals, ordinary local reads, groups, pairs, primitive unary and binary
operators and conditionals. Each such site has no coercions, has no
requirements except at an integer literal, is not a generalized initializer and
reads no generalized binder, so the compiler's special callback declines it. A
contextual closure admits no site. Because the compiler accepts only
expressions it finds in its view, `closed_of_nodes` derives `Closed` from the
body's expression nodes alone. `of_subset` extracts a receipt tree from the
compiler's own acceptance at its root fuel
(`GeneralizedLocalInitializerCompilation.named_contextual`), at the reached
scope and Source context, using the scope declarations of the physical entry.
[CellAwareInvocationAcceptedExpressionBounds](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedExpressionBounds.lean)
closes that tree by structural recursion over the existing invocation-family
heads for read-product leaves, groups, pairs, operators and conditionals. No
expression or body execution law is an input. `expressions` turns `Closed` into
`Expressions` at every budget, and the module's `body_preserves` and
`body_reflects` compose it with the statement closure: for such bodies they
are the whole-body theorems above without the `Expressions` premise. In its
place they take `Closed`, `Reads` (the fault interpretation of the body's
uninitialized-read diagnostic words) and selected-body typing of the staged
registry (`SelectedBodies`); the registry extension comes from `Writes`. All
other premises of the body theorems are unchanged. Direct calls do not fit this
structural recursion, because their staged trace runs the callee body; they
need the shared size induction across bodies. Indirect, builtin and method
calls, indices, longer tuples, constructors, builtin references, generalized
reads, lambdas and coercions are also outside the subset.

The public connection of this subset starts at
[CellAwareInvocationAcceptedNamedInvocation](../../Solcore/SourceSemantics/CoreLowering/CellAwareInvocationAcceptedNamedInvocation.lean).
Its `reads` derives `Reads` for a named row from the retained diagnostic issuer
and the public fault receiver, as `CellAwareNamedReadDiagnostics.uninitialized`
does for the older named family. `preserves_selected` and `reflects_selected`
run the actual named parameter entry (`CellAwareNamedEntry.prepare_selected`).
From it they build the physical entry state of the row's own accepted-body
index: the parameters are monomorphic, so
`CellAwareInvocationPhysical.Physical.of_monomorphic` and
`CellAwareScopeAuthority.At.of_monomorphic` apply. They then apply the
subset's `body_preserves` or `body_reflects` and restore the saved physical
caller. The caller's heap is represented with the profiled instance model of
the older family. `cell_of_profiled` embeds each of its cells in the accepted
instance model with the trivial attachment, and the results are stated in that
model. At an actual prepared header,
[CellAwarePublicAcceptedNamedRoot](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicAcceptedNamedRoot.lean)
derives the static inputs (`CellAwareInvocationAcceptedNamedHeaders.static_inputs`)
and the issuer from the public diagnostic receipt. Its
`checkpoint_has_sufficient_fuel_selected` and `checkpoint_reflects_selected`
relate a staged Source trace of the body to the native completion of the actual
public start in both directions, through the unchanged public root.
[CellAwarePublicAcceptedNamedForward](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicAcceptedNamedForward.lean)
`first_value_selected` takes a staged trace that returns a value to a
successful public resumption (`SourceCoreExecution.Checkpoint.ResumeAt`). The
resumption carries the exported value and the physical history of the returned
session.

These public theorems keep as explicit premises `Closed`, the accepted body
receipt and its `Covered`, `Writes`, and the original compilation receipt.
They also keep the root, start and caller-state receipts that the older public
root takes. The trivial attachment does not satisfy `Generalized`, so
generalized declarations are not connected. The theorems take a staged Source
trace. Unlike the older imperative family, which lifts an original Source trace
with its profiled body tree, they do not lift original traces. The reached
heap and history are in the accepted instance model, and no continuation
theorem consumes them, so later public calls do not yet chain from them. No
concrete program instantiates these theorems yet.

## Remaining work for the second goal

`StaticProfile` deliberately recognizes a strict subset. Successful compilation
cannot imply it for every accepted program. Complete the general body proof
from actual named and contextual compiler receipts, rather than widening a
recognizer until it appears universal or assuming a body-execution law.

On the accepted-body route above, the next connected steps are:

- Close the remaining compiler branches in `Covered`: writes and matches under
  contextual metadata views. Record the match compilation context in the
  refined tree so that `Admitted` follows from the body policy, derive the
  lambda shape of generalized initializers from the compiler's initializer
  receipt, and derive the `Generalized` issuer at actual headers from the public
  diagnostic receipt (as `CellAwareNamedDiagnosticIssuer.of_prepared` does).
  Statements after an always-returning prefix in a non-Unit
  function, which the existing flows cannot express, need a separate argument;
  the header certificate's `BodyCompletes` fact is the available Source input.
- Extend the expression closure beyond its first subset over the same actual
  accepted expression compiler: direct calls through the shared size induction
  across bodies, then indirect and builtin calls, methods, indices, tuples,
  constructors, generalized reads, closures and coercions. Expressions of
  contextual closures need the relation between the compiler view and the
  Source that their writes and matches also need.
- Strengthen the named-row public connection. Derive `Writes` at actual
  headers from the issued assignment recipes and the public receiver, as the
  older family does with `CallableIndexedOwnedIssuedAssignmentRecipes.operands`
  and `CellAwareNamedAssignmentDiagnostics.ready`. Lift original Source traces
  of accepted bodies to staged traces, and carry the accepted instance model
  through public histories so that later calls chain. Then instantiate the
  public theorems on a concrete program, and issue program support from the
  receipt without `StaticProfile`.

The final connection must:

- Preserve independently instantiated Source metadata, generalized local
  closures, captured environments and the actual reached heap.
- Assemble expression, statement and loop simulations for complete accepted
  bodies, including calls, control transfers and failure paths.
- Compose specialization, evidence handling, staging and lowering without
  substituting a previously transformed program for the original Source
  meaning.
- Derive initialization, argument, heap and callable-history conditions from
  the actual public compiler, bootstrap and call receipts, and carry them
  through repeated resumptions and later calls.
- Relate completed values, language failures and export behavior under the
  stated validation budgets. State finite-execution and termination premises
  explicitly; fuel exhaustion must not disguise a missing preservation case.

End each extension in a consumer of the real public API. Isolated helper
lemmas, declaration counts and runtime test counts do not establish completion
of this goal. The final theorem and its remaining premises, rather than a
percentage estimate, determine the boundary.

## Validation

For implementation or proof changes, run focused checks followed by the
required repository build, tests and semantic-kernel policy check. Audit the
public theorem's assumptions and test its real execution path. Keep unresolved
upstream questions in the ignored `questions.md`; retain confirmed regressions
and public limitations in tracked tests and documentation. Delete disposable
validation files after recording their results.
