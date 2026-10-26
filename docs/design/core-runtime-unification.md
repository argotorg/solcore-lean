# Core runtime unification and semantic preservation

Updated: 2026-10-26.

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
exactly the expressions the compiler accepted, at every compiler fuel; no
expression closure exists yet. `Covered` admits returns, final values, discards,
`break`/`continue`, blocks, conditionals, `while` loops, monomorphic initialized
or uninitialized declarations, and bare assignments and bit-not updates when the
compiler view is the original Source (as for named rows). Their flow heads come
from the tree's assignment receipts and the body's actual assignment policy
(`ActualBodyInvocation.Index.assignment_policy` and `bitNot_policy`). `Covered`
excludes projected writes, matches, `for` loops and generalized declarations,
and it requires a function-mode fallthrough to have Unit result and a final bare
value to have the declared result type. The caller also supplies native typing
of the flow, checker typing of the body, the invocation's physical entry state,
and the fault interpretation of the body's assignment diagnostic words. These
theorems are not yet used by the public session.

## Remaining work for the second goal

`StaticProfile` deliberately recognizes a strict subset. Successful compilation
cannot imply it for every accepted program. Complete the general body proof
from actual named and contextual compiler receipts, rather than widening a
recognizer until it appears universal or assuming a body-execution law.

On the accepted-body route above, the next connected steps are:

- Close the remaining compiler branches in `Covered`: projected writes, bare
  writes under contextual metadata views, matches, `for` loops and generalized
  declarations. Statements after an always-returning prefix in a non-Unit
  function, which the existing flows cannot express, need a separate argument.
- Discharge `Expressions` by an expression closure over the actual accepted
  expression compiler, with calls, closures, methods and coercions supplied by
  the shared size induction.
- Construct the invocation's physical entry state from the actual named
  parameter entry and connect `body_preserves`/`body_reflects` to the public
  body ports, then issue program support from the receipt without
  `StaticProfile`.

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
