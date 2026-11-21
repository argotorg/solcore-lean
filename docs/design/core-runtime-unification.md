# Core runtime unification and semantic preservation

Updated: 2026-11-18.

## Status and scope

- **The first goal is complete.** Native source execution uses Core, and the separate typed-source
  runtime evaluator has been removed.
- **The second goal is incomplete.** No general theorem connects every successfully compiled
  native source body to its independent meaning through the complete public execution pipeline.
- **Differential testing.** The M0–M6 milestones are complete for their documented bounded
  profiles ([differential testing](../guide/differential-testing.md)). Those comparisons exercise
  the pinned Rust dialect against original generated Core and imported Hull; they do not finish
  the native source compiler's preservation theorem.

The [next implementation roadmap](next-implementation-roadmap.md) sets the order of further testing
and proof work. This note replaced the migration progress, API and audit appendices, whose dated
checkpoints are in git history; the API and proof definitions below take precedence over them.

## Original goals

1. Preserve existing runtime behavior while replacing direct typed-source execution with
   compilation to Core and execution by the Core machine.
2. Prove that the actual source-to-Core transformation preserves observable meaning, including
   values, failures, heap effects and retained callable environments, through the public API.

**Separate tasks.** The first goal concerns runtime execution: unifying the native frontend's
comptime evaluator is a separate task. Connecting native source contract members, persistent
storage and external calls to `ContractRuntime` is also separate; current native ABI discovery is
limited to static Word roots. The Rust Hull import path already has broader contract execution
support and its own [proof boundary](hull-meaning-preservation.md).

**The proof target** is a successful selected compilation: the requested roots, their discovered
dependencies and the callable instances actually compiled. Checker acceptance alone does not
guarantee that every declaration in the workspace is executable, and an unrelated unsupported
declaration need not block an executable selected entry. Do not replace this boundary with a
requirement that the entire workspace compiles, or with checker acceptance alone.

## Public runtime API

Import [SourceCompiler](../../Solcore/Frontend/SourceCompiler.lean). It exports the same artifacts,
values, sessions and checkpoints as
[SourceCoreExecution](../../Solcore/Frontend/SourceCoreExecution.lean); it is not another evaluator.

| Operation | Public entry points |
| --- | --- |
| Check and compile selected roots | `compile`, `compileChecked`; `compileEntry` selects the entry point. |
| Open and initialize | `Compiled.open`, `Artifact.bootstrap`, `Bootstrap.resume`. |
| Execute a named root | `Session.start`, `Session.run`. |
| Retain and invoke functions | `Session.named`, `Session.builtin`, `Session.invokePacked`. |
| Resume suspended execution | `Checkpoint.resume`. |
| Observe and restore local state | `Session.snapshot`, `Checkpoint.snapshot`, `Session.restoreSnapshot`. |
| Discover a static Word ABI | `compileStaticWord`, `StaticWordProgram.rootForSelector?`. |

- **Sessions and handles.** Use the session returned by a completed call for later calls. Public
  handles carry artifact and session authority; they are not raw Core references or serializable
  source closures. The API enforces the snapshot and handle restrictions. The
  [execution tests](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean)
  and [snapshot tests](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Snapshots.lean)
  show current usage.
- **Budgets and outcomes.** `RunOptions` separates the budgets of input validation, Core execution
  and output validation. Initialization can also suspend. The public outcomes distinguish
  successful completion, language failure, an out-of-fuel checkpoint and an output export error.
  Exhausted fuel is a resumable resource outcome, not proof of source termination or of a
  successful result. Core fuel and EVM gas are not the same quantity.
- **What runs.** Runtime support includes closures, recursive functions, mapping values, mutable
  locals, compound values and function handles nested in data. Closures capture by value: a closure
  copies its captured locals when it is created and again at each call
  ([closure captures](../guide/source-semantics.md#closures-capture-by-value)). Source mapping
  values here are local language data; they are not an assertion that native contract storage is
  connected to the account-world runtime.

## Established proof connections

Core typing and finite execution safety are established separately from source-to-Core meaning
preservation. The independent Source semantics provides the source-side executions; running
translated Core is not its definition. core-lowering's
[module table](../guide/core-lowering.md#front) says what each module of `CoreLowering/` holds.

### The checker connection

The checker connection derives the validity of every ordinary-function and implementation-method
body in the selected compilation cache, later-discovered dependencies included. It follows the
actual inference calls, initializer lifetimes, retained bindings and final substitution.

- `SourceCompiledActualInitializerBarriers.compile_cached_bodies`
  ([CompiledBodies](../../Solcore/SourceSemantics/CompiledBodies.lean)) derives cached-body validity
  from successful compilation and its artifact.
- `SelectedCompilationRawPublicReceipt.of_compile`
  ([PublicSessions](../../Solcore/SourceSemantics/CoreLowering/PublicSessions.lean)) retains the
  actual public compilation and prepared recipe.
- `Receipt.checker_bodies`, `checker_profiled` and `checker_initial_row` connect that receipt to
  body validity and the existing profiled public session. Initializer barriers and body typing are
  derived here rather than supplied independently. `StaticProfile` remains an explicit premise of
  the connections to the profiled public session.

### Profiled public sessions

The profiled public sessions in `PublicSessions` connect supported source bodies to actual
initialization, calls, resumptions and retained histories. The broader proof library covers
individual expression, statement, loop, assignment, mapping and callable connections. Their exact
premises matter: a connected restricted profile does not imply coverage of all compiler-accepted
syntax.

### Accepted bodies: the statement closure

The general accepted-body route starts from the actual compiler receipt of one body invocation,
`ActualBodyInvocation.Index`: a named cache row or a materialized contextual closure. In
`CellAwareInvocationAcceptedFlow`
([AcceptedStatements](../../Solcore/SourceSemantics/CoreLowering/AcceptedStatements.lean)),
`correct` closes the mixed-cell statement flows by induction over the actual accepted compiler tree
(`AcceptedNamedBodyFlow.Tree`), not over a Source recognizer. Each branch uses the compiler's own
receipts, and fixed-control checker typing supplies the Source facts. `body_preserves` and
`body_reflects` compose it with the actual footer and relate `index.body` to independent Source
execution in both directions, including failures, control transfers and the reached heap.

These theorems keep explicit premises:

- **`Expressions`** supplies meaning for exactly the expressions the compiler accepted, at every
  compiler fuel. The expression closure below discharges it for named-row bodies of a first subset
  with direct calls and the builtin conversions at any expression position.
- **`Covered`** admits returns, final values, discards, `break`/`continue`, blocks, conditionals,
  `while` and `for` loops, monomorphic initialized or uninitialized declarations, and bare and
  projected assignments and bit-not updates when the compiler view is the original Source, as for
  named rows. It excludes writes and matches under contextual metadata views, and it requires a
  function-mode fallthrough to have Unit result and a final bare value to have the declared result
  type.
  - Write heads come from the tree's assignment receipts, the compiler's own key and right-hand
    lowerings and the body's actual assignment policy
    (`ActualBodyInvocation.Index.assignment_policy` and `bitNot_policy`).
  - `for` headers are closed over the compiler's header items
    (`CellAwareInvocationAcceptedForItems`), with their declarations authenticated by the original
    compilation receipt.
  - Matches are closed under the same Source view (`CellAwareInvocationAcceptedMatches`). The tree
    does not record a match receipt's compilation context, so `Covered` requires it to be admitted
    (`Admitted`: the checked catalog's initial values, the body's own allocator and definitions
    extended by the indexed layouts). `AcceptedNamedBodyFlow.Tree.refine` builds its match receipts
    at its policy-success context but does not state it.
  - Generalized declarations are closed through `CellAwareInvocationGeneralizedAcceptedAllocation`
    when their initializer is a direct lambda without requirements or coercions and the
    `CellAwareInvocationAcceptedInputs.Generalized` inputs hold: the captured-scope descriptor
    attachment, the residual entry of a contextual invocation (trivial for named rows) and the
    body's diagnostic issuer. For this the closure carries the compiler's statement sites
    (`ActualBodyInvocation.Index.Site`), and it also concludes that every native typing of the
    emitted code has a Word failure component (`CellAwareInvocationAcceptedNative`), which fixes
    the initializer's native type at its language result.
- **Typing.** The caller supplies Core typing of the compiled body, fixed-control checker typing and
  the result projection. For an actual prepared named header,
  `CellAwareInvocationAcceptedNamedHeaders.static_inputs`, in `AcceptedExpressions`, derives all
  three from checker certification and the cached body's Core typing.
- **Other inputs:** the invocation's physical entry state, the original compilation receipt and the
  write inputs (`CellAwareInvocationAcceptedInputs.Writes`). The write inputs are the fault
  interpretation of the body's assignment diagnostic words at its typed assignment occurrences,
  reached place diagnostics and function identity views. The public connection below constructs
  the physical entry state and the write inputs for named rows whose accepted expressions lie in
  the first expression subset.

### The first expression subset

The first expression closure is `CellAwareInvocationAcceptedExpressions`
([AcceptedExpressions](../../Solcore/SourceSemantics/CoreLowering/AcceptedExpressions.lean)).

- **The subset.** `Closed` states it as a predicate on the actual accepted expression receipts:
  every expression the compiler accepts for the body, at any fuel and scope, is a site of the
  subset (`InSubset`). For a named row these sites are `Subset` of
  `CellAwareInvocationAcceptedExpressionTrees`: literals, ordinary local reads, groups, pairs,
  primitive unary and binary operators and conditionals. Each such site has no coercions, has no
  requirements except at an integer literal, is not a generalized initializer and reads no
  generalized binder. A contextual closure admits no site.
- **Its closure.** `closed_of_nodes` derives `Closed` from the body's expression nodes alone, since
  the compiler accepts only expressions it finds in its view. `of_subset` extracts a receipt tree
  from the compiler's own acceptance, and `CellAwareInvocationAcceptedExpressionBounds` closes it by
  structural recursion over the existing invocation-family heads. No expression or body execution
  law is an input.
- **The body theorems.** `expressions` turns `Closed` into `Expressions` at every budget. The
  module's `body_preserves` and `body_reflects` are then the whole-body theorems above without the
  `Expressions` premise. In its place they take `Closed`, `Reads` (the fault interpretation of the
  body's uninitialized-read diagnostic words) and selected-body typing of the staged registry
  (`SelectedBodies`); the registry extension comes from `Writes`. Their other premises are
  unchanged.
- **Outside the subset.** Direct calls do not fit this structural recursion, because their staged
  trace runs the callee body; they need the shared size induction across bodies, below. Indirect,
  builtin and method calls, indices, longer tuples, constructors, builtin references, generalized
  reads, lambdas and coercions are also outside the subset.

### Direct calls

Direct calls are in [AcceptedCalls](../../Solcore/SourceSemantics/CoreLowering/AcceptedCalls.lean).

- **The head.** `CellAwareInvocationAcceptedDirectCalls` works at a site with the actual compiler
  receipt, call authority and evidence (the plain-heap family's `Receipt`, `Port` and
  `EvidenceAt`). Its `preserves` and `reflects` close the argument vector, read the issued global
  cell and restore the caller carrier; argument faults stop before the read.
- **Its input.** Applying the selected closure is an explicit input below the grade of the call.
  `PreservesBelow` and `ReflectsBelow` of the callee header state that applying its issued closure
  from a reached caller pool enters the callee, runs it and restores the same pool over accepted
  cells, with the Source application at its own grade. The pool comes with its physical capture
  and cache, stable rows and argument rows.
- **The protocol.** The caller carrier must retain every ordinary global slot (`Globals`), and
  every reached caller the physical cache. The physical canonical protocol does both, with the cell
  producer of `CellAwareInvocationAcceptedGlobalSlots`. The accepted flow and the derived write
  inputs are generic in the protocol, so accepted bodies can run on it. The head also uses
  `ProgramWellFormed`, which the public named support does not carry.
- **Named application.** `CellAwareInvocationAcceptedNamedApplication` derives the head's input
  from the callee's own accepted body. From the receipts of the public named root, its `preserves`
  and `reflects` prove `PreservesAt` and `ReflectsAt` of a named row's header. The only expression
  input is the meaning of the body's accepted expressions below the grade on the slot-retaining
  protocol, for every owner key with physical locations. For reflection the callee's registry
  scope is a row receipt, as at the public root.
- **The entry.** `CellAwareInvocationAcceptedNamedEntry` is `CellAwareNamedEntry.prepare_selected`
  over any instance model of the caller's cells. It also returns the parameter spine, and it
  inverts a sized native completion into a strictly smaller body completion through a sized prefix
  agreement (`SizedAgreement`).
- **Closed callees.** `expressions_closed` discharges the expression input when every accepted
  expression of the callee lies in the closed subset, so `preserves_closed` and `reflects_closed`
  give the input for such a callee at every grade without the induction.

### Direct calls at expression roots

- **The extended subset.** `CellAwareInvocationAcceptedCallTrees` adds direct calls to the first
  subset (`CallSubset`) when four conditions hold:
  - the call's arguments are first-subset sites;
  - its node has no coercions or requirements;
  - its declaration is monomorphic and the calling row has no evidence assumptions (`DirectSite`,
    whose policy lemmas are in `CellAwareInvocationAcceptedDirectSites`);
  - the family admits its instantiation.
- **The receipt tree.** The tree (`CallTree`) keeps the compiler's direct-call receipt, the
  authority (`Port`) of the selected header and the subset receipt trees of the arguments, and
  `of_call_subset` extracts it from the compiler's acceptance. On a compiled row,
  `CellAwareInvocationAcceptedCallSubsetCheck.nodes?` checks the extended roots and `closedCalls`
  gives `ClosedCalls`. The call authority of the body's receipts is an input (`Ports`).
- **The closure.** `CellAwareInvocationAcceptedCallBounds` closes the tree: subset roots use the
  existing bounds, and calls use the direct-call head. `CellAwareInvocationAcceptedCallExpressions`
  turns `ClosedCalls` into `Expressions` on the slot-retaining protocol, given the application of
  every admitted callee below the budget.
- **Families.** `CellAwareInvocationAcceptedCallFamily` closes a family. If every catalog header
  with an admitted instantiation has the receipts of such a row (`Row`), one strong induction on
  the grade gives `Expressions` for every family body, and its `preserves` and `reflects` give the
  application of every admitted header at every grade.
  `CellAwareInvocationAcceptedNestedTrees.Nested` closes the subset's forms and direct calls under
  one another, so a call may also be an operand, a branch, a pair element or another call's
  argument; the family takes rows whose accepted expressions are nested sites (`ClosedNested`).
  The builtin conversions are nested sites too, with the dirty-integer revert's token law as an
  instance argument (`CellAwareInvocationAcceptedConversionFaults.DirtyToken`).
- **Authority.** `CellAwareInvocationAcceptedCallAuthority` derives `Ports` from a complete
  inventory: a call receipt's global slot names an indexed function, and the inventory's header for
  that index gives the `Port`.
- **The public root.** `CellAwareInvocationAcceptedCallEntry` is the body-trace counterpart of the
  row lemma in both directions (`preserves_selected`, `reflects_selected`), packaged as the root's
  `NamedResultAt` with the restored caller's post-admission. In
  [AcceptedPublicRoots](../../Solcore/SourceSemantics/CoreLowering/AcceptedPublicRoots.lean),
  `CellAwarePublicAcceptedCallRoot` relates a call-containing row to the unchanged public root in
  both directions (`checkpoint_has_sufficient_fuel_selected`, `checkpoint_reflects_selected`), and
  `CellAwarePublicAcceptedCallForward.first_value_selected` takes a returning trace to a successful
  public resumption. The body runs on the slot-retaining protocol from the root's physical cache
  and capture. Its expression meaning is an input, which `expressions_of_family` gives at every
  grade from the row's extended roots, its call authority and a family of callee rows.

### The public connection of the subset

`CellAwareInvocationAcceptedNamedInvocation`, in `AcceptedExpressions`, connects the first subset at
a named row.

- **Diagnostics.** Its `reads` derives `Reads` from the retained diagnostic issuer and the public
  fault receiver, and its `writes` derives `Writes` from the issued compilation, its prepared
  assignment table and the public receiver, as the older named family's diagnostics do. The
  registry extension is the receiver's own.
- **Where `Writes` asks.** `Writes` asks for the operand and unary words only at the typed
  assignment occurrences of the Source, as for the reached place diagnostics. An input over every
  site would have no instance with the actual fault relation: a site without a table entry yields
  the zero word for both kinds of fault, and the receiving table cannot decode one word as both.
- **The row.** `preserves_selected` and `reflects_selected` run the actual named parameter entry
  (`CellAwareNamedEntry.prepare_selected`), build from it the physical entry state of the row's own
  accepted-body index, whose parameters are monomorphic, apply the subset's body theorems and
  restore the saved physical caller. The caller's heap is the older family's profiled instance
  model, which `cell_of_profiled` embeds in the accepted instance model with the trivial
  attachment, and the results are stated in that model.
- **The public root.** At an actual prepared header, `CellAwarePublicAcceptedNamedRoot`, in
  `AcceptedPublicRoots`, derives the static inputs, the issuer, the issued tables and the prepared
  assignment table from the public diagnostic receipt. Its
  `checkpoint_has_sufficient_fuel_selected` and `checkpoint_reflects_selected` relate a staged
  Source trace of the body to the native completion of the actual public start in both directions,
  through the unchanged public root. `CellAwarePublicAcceptedNamedForward.first_value_selected`
  takes a staged trace that returns a value to a successful public resumption
  (`SourceCoreExecution.Checkpoint.ResumeAt`), which carries the exported value and the physical
  history of the returned session.

These public theorems keep as explicit premises `Closed`, the accepted body receipt and its
`Covered`, the original compilation receipt, the root, start and caller-state receipts that the
older public root takes, and a staged Source trace. The trivial attachment does not satisfy
`Generalized`, so generalized declarations are not connected. The reached heap and history are in
the accepted instance model, and no continuation theorem consumes them, so later public calls do not
yet chain from them.

### Premises at an actual program

Each premise of the public theorems above, and the staged trace, can be produced at an actual
program.

- **The subset check.** `CellAwareInvocationAcceptedSubsetCheck`, in `AcceptedExpressions`: its
  `nodes?` reads a row's Source nodes and the prepared local inventory and returns a proof that
  every expression node is a `Subset` site. A site depends on its row only through the row's key,
  so `transport` moves the proof to every row with that key, and `closed` turns it into `Closed`.
- **The body shape.** `Shape`, in `CellAwareInvocationAcceptedBodyShape`
  ([AcceptedShapes](../../Solcore/SourceSemantics/CoreLowering/AcceptedShapes.lean)), recognizes on
  the Source statement lists of value and unit returns, monomorphic declarations, bare assignments
  that the compiler refines (`Assignable`), bare in-place `~` that it refines
  (`BitNotAssignable`), expression statements, blocks and conditionals, with every expression in
  a given predicate. A list that may end without returning is a branch or block
  body, or belongs to a Unit function. `covered` shows that every refined accepted tree of such a
  list is covered; a refined tree keeps the unrefined assignment branch only for writes that are not
  `ValueAssignable`, and the unrefined `~=` branch only for those that are not `UnaryAssignable`.
  `shape?` checks a shape with subset-site expressions on an actually compiled row.
- **The receipts.** `CellAwarePublicAcceptedNamedRoot.refined_body` refines the actual body receipt
  at a prepared header with the header's own assignment, bit-not and match policies.
  `CellAwarePublicAcceptedNamedRoot.compilation_receipts` derives the original compilation receipt
  from the checked program, its public compilation and the issued recipe.
- **Lifting**, also in `AcceptedShapes`. `CellAwareInvocationAcceptedSourceLifting.expression_value`
  stages every value execution of a subset expression, by structural induction on `Subset` with no
  typing or state input. `CellAwareInvocationAcceptedStatementLifting.statements` stages every
  ordinary execution of a shaped list whose expressions are subset sites, in both compiler modes,
  by structural induction on `Shape`. Every control outcome is carried unchanged, with the context,
  environment and heap of the original execution, and `body` gives the sized staged trace of a
  function body.
- **Lifting with calls.** `CellAwareInvocationAcceptedCallLifting`
  ([AcceptedCallLifting](../../Solcore/SourceSemantics/CoreLowering/AcceptedCallLifting.lean))
  lifts original executions of bodies whose expressions are extended roots (`CallSubset`), over
  sized derivations (`CellAwareInvocationAcceptedSizedLifting.statements`). At a direct call the
  callee body's derivation is smaller than the call's, so `bodies` lifts every admitted callee's
  body by one strong induction on the size, and `body` gives the sized staged trace of a
  call-containing function body. The admitted callees' static receipts are a premise (`Callees`).
- Fault executions are not lifted.

### Instances

- **One named row.** The tick test in
  [Generalized/Export](../../Solcore/Test/SourceSemantics/CoreLowering/Generalized/Export.lean),
  merged there from `Solcore.Test.SourceCoreGeneralizedExportAcceptedTick`, compiles the existing
  three-function GeneralizedExport program at runtime and takes its `tick` row, whose body returns
  its Bool parameter. Its `accepted_tick` meets every premise of `first_value_selected`,
  `checkpoint_has_sufficient_fuel_selected` and `checkpoint_reflects_selected` at the row's first
  public call, with the existing start receipts.
  The premises come from the runtime subset and shape checks, the refined body receipt and its
  coverage, the compilation receipts and the trace of the row's independent Source execution
  lifted through the shape. Program support comes from
  `SelectedCompilationNamedSupport.Support.of_program`, with the well-formedness that the existing
  typing observation derives; no `StaticProfile` enters. The runtime harness checks the subset and
  the shape, builds this kernel-checked plan for both inputs and resumes the actual call. The
  instance exercises one ordinary local read under a returning first statement; the theorems it
  uses are general over the subset and the shape.
- **One call.** The test
  [Accepted/OneCall](../../Solcore/Test/SourceSemantics/CoreLowering/Accepted/OneCall.lean) compiles
  a five-function program at runtime: `identity` returns its `Word` parameter, `relay` returns
  `identity(value)`, `twice` returns `identity(identity(value))`, `narrow` returns `uint8(value)`
  and `roundTrip` returns `Typedef.rep(uint8(value))`. Its `accepted_call` meets every premise of
  `CellAwarePublicAcceptedCallForward.first_value_selected`,
  `CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected` and
  `checkpoint_reflects_selected` at `relay`'s first public call, at `twice`'s, where the inner
  call's result is the outer call's argument, and at `narrow`'s and `roundTrip`'s at a canonical
  word. At a dirty word, `accepted_reflection` meets the reflection's premises at both, and the
  call fails with the dirty-integer reason. The fixture
  [Accepted/Fixture](../../Solcore/Test/SourceSemantics/CoreLowering/Accepted/Fixture.lean) builds
  the family rows and the callees' receipts from runtime checks of every cache row and a complete
  inventory (`WholeInventory.family_row`, `WholeInventory.callees`), and the staged trace is lifted
  from `relay`'s original execution. A call's callee is an expression node of its own: the check
  admits it as a declaration reference with no plan reference edge, which the named compiler cannot
  lower on its own (`CellAwareInvocationAcceptedCallSubsetCheck.reference_rejected`).

## Remaining work for the second goal

`StaticProfile` deliberately recognizes a strict subset. Successful compilation cannot imply it for
every accepted program. Complete the general body proof from actual named and contextual compiler
receipts, rather than widening a recognizer until it appears universal or assuming a body-execution
law.

On the accepted-body route above, the next connected steps are:

- **Close the remaining compiler branches in `Covered`:** writes and matches under contextual
  metadata views.
  - Record the match compilation context in the refined tree, so that `Admitted` follows from the
    body policy.
  - Derive the lambda shape of generalized initializers from the compiler's initializer receipt.
  - Derive the `Generalized` issuer at actual headers from the public diagnostic receipt, as
    `CellAwareNamedDiagnosticIssuer.of_prepared` does.
  - Statements after an always-returning prefix in a non-Unit function, which the existing flows
    cannot express, need a separate argument; the header certificate's `BodyCompletes` fact is the
    available Source input.
- **Extend the expression closure beyond its first subset**, over the same actual accepted
  expression compiler.
  - Direct calls and the builtin conversions at any expression position are closed over
    families of rows, with call authority from a complete inventory. They are connected at the
    public root in both directions, original traces of call-containing bodies are lifted, and a
    program with a call, a nested call, a conversion and `Typedef.rep` of a conversion
    instantiates both directions.
  - Next come indirect calls, the other builtin calls, methods, indices, tuples, constructors,
    generalized reads, closures and coercions.
  - Expressions of contextual closures need the relation between the compiler view and the Source
    that their writes and matches also need.
- **Strengthen the named-row public connection.**
  - Instantiate the theorems at a body with declarations, assignments, conditionals, operators and
    pairs. This needs a fixture with the older root's receipts and an independent Source trace of
    that body, or a proof-producing Source evaluator for the closed subset.
  - Extend the shape, its coverage and the lifting to fault outcomes, projected writes, tail
    values and loops.
  - Carry the accepted instance model through public histories, so that later calls chain.
  - Issue program support from the compiler receipt for every accepted program, rather than from an
    observation of its typings.

The final connection must:

- Preserve independently instantiated Source metadata, generalized local closures, captured
  environments and the actual reached heap.
- Assemble expression, statement and loop simulations for complete accepted bodies, including
  calls, control transfers and failure paths.
- Compose specialization, evidence handling, staging and lowering without substituting a previously
  transformed program for the original Source meaning.
- Derive initialization, argument, heap and callable-history conditions from the actual public
  compiler, bootstrap and call receipts, and carry them through repeated resumptions and later
  calls.
- Relate completed values, language failures and export behavior under the stated validation
  budgets. State finite-execution and termination premises explicitly; fuel exhaustion must not
  disguise a missing preservation case.

End each extension in a consumer of the real public API. Isolated helper lemmas, declaration counts
and runtime test counts do not establish completion of this goal. The final theorem and its
remaining premises, rather than a percentage estimate, determine the boundary.

## Validation

For implementation or proof changes, run focused checks, then the required repository build, tests
and semantic-kernel policy check. Audit the public theorem's assumptions and test its real execution
path. Keep unresolved upstream questions in the ignored `questions.md`, and keep confirmed
regressions and public limitations in tracked tests and documentation. Delete disposable validation
files after recording their results.
