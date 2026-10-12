import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalLambdaBodyBounds

/-! Empty ordinary closure bodies run their actual compiled unit footer.
The original parameter allocation and saved caller restoration supply the
same reached pool, heap and post as every other application branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Empty EmptySupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Empty code stages)
  (support : EmptySupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include packet in
private theorem footer_evaluates (actual : Environment) (initial : Store) (ξ : Renaming) :
    Evaluates actual initial (code.receipt.body.rename ξ) (.inRight .word .unit) initial := by
  rw [packet.emitted, packet.nativeUnit]
  have renamed : (CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
      code.compilation.internalReason code.compilation.internalReason).rename ξ =
      CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        code.compilation.internalReason code.compilation.internalReason := by
    simp [CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
      Expr.rename, Renaming.lift]
  rw [renamed]
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal _ code.compilation.internalReason (LocalLoop.fallthrough_evaluates .unit actual initial))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: actual) initial
        (.inRight .word .unit) (.inRight .word .unit) initial from .inRight .unit))

private theorem empty_trace {program : Program} {stages : Staging.Recursive.Registry}
    {size : Nat} {child : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {ids : List StatementId}
    {outcome : Staging.Recursive.BodyOutcome} (empty : ids = [])
    (trace : Staging.Recursive.Size.Statements program stages size child context environment heap
      ids finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = heap := by
  subst ids
  cases trace
  exact ⟨rfl, rfl, rfl⟩

private theorem empty_outcome {type : TypeSystem.Ty} {environment : Dynamic.Environment}
    {outcome : Staging.Recursive.Outcome}
    (matched : Staging.Recursive.BodyResult type (.fallthrough environment) outcome) :
    outcome = .value .unit := by
  cases matched
  rfl

private theorem unit_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {type : TypeSystem.Ty} (same : type = .unit) : Dynamic.ValueHasType context heap .unit type := by
  subst type
  exact .unit

private theorem unit_result (sourceType : TypeSystem.Ty) (nativeType : Ty)
    (raw : sourceType = .unit) (native : nativeType = .unit) (m : LocationMap) (w : StoreTyping) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      m w sourceType nativeType callFaults (.value .unit) (.inRight .word .unit) := by
  subst sourceType
  subst nativeType
  exact .value .unit

include packet stable beforeTyped argumentsTyped in
private theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (bodySize : Nat) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  obtain ⟨rfl, rfl, rfl⟩ := empty_trace packet.empty trace
  obtain rfl := empty_outcome matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  refine ⟨_, entry.entry.store, entry.entry.mapping, entry.entry.world,
    footer_evaluates (captured := captured) (code := code) (packet := packet) _ _ _, ?_, entry.entry.heaps,
    .refl _, .refl _, .refl _ _, .refl _, reached, .refl _, ?_⟩
  · exact unit_result (profile := profile) _ _ packet.unit packet.nativeUnit _ _
  · change CallableIndexedOwnedSourceAdmission.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context function.resultType (.value .unit) reached
    refine ⟨admitted.rows, ?_⟩
    intro value same
    cases same
    exact ⟨unit_typed packet.unit, admitted.heap⟩

include packet stable beforeTyped argumentsTyped in
private theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (nativeSize : Nat) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have evaluated := footer_evaluates (captured := captured) (code := code) (packet := packet) entry.actual entry.store entry.embedding
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping beforeTyped rawArguments entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  refine ⟨Staging.Recursive.Size.stepSize [], inputs.context, .fallthrough entry.environment,
    .value .unit, entry.heap, entry.mapping, entry.world, ?_, ?_, ?_, entry.heaps,
    .refl _, .refl _, .refl _ _, .refl _, reached, .refl _, ?_⟩
  · simpa only [packet.empty] using
      (Staging.Recursive.Size.Statements.nil (program := Program.ofChecked compiled.sourceProgram)
        (registry := stages) (scope := packet.child) (context := inputs.context)
        (environment := entry.environment) (heap := entry.heap))
  · rw [packet.unit]
    exact .unit
  · exact unit_result (profile := profile) _ _ packet.unit packet.nativeUnit _ _
  · change CallableIndexedOwnedSourceAdmission.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context function.resultType (.value .unit) reached
    refine ⟨rows, ?_⟩
    intro result same
    cases same
    exact ⟨unit_typed packet.unit, heapTyped⟩

include packet stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The real Source call allocates its parameters before the empty body and
restores the actual saved caller after its unit result. -/
theorem application_preserves
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable size
    (fun entry reached childSize _strict =>
      source_body_at (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached childSize)
    trace (Nat.le_refl size)

include packet stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native completion determines the unchanged body store and unit result;
reflection reconstructs the original empty Source body with its own grade. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid size
    (fun entry reached childSize _strict =>
      native_body_at (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid childSize)
    completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
