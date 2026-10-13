import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaBodyBounds

/-! The actual retained closure application constructs its terminal body
ports from the same compiler receipt and strict expression hypotheses.
Parameter installation and caller restoration use their original producers;
semantic and stage failures keep their exact Source scope and reached state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (callerPrefix : Nat)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {expression : ExpressionId}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
  (terminal : Receipt policy fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression function.body code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ lowered,
    policy.lowerExpression terminal.childFuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression reasonAt = .ok lowered →
    certificate
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression lowered)


variable (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
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
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- The strict body port is manufactured at the genuine parameter entry.
The Source application and both native prefixes run once. -/
theorem application_preserves (budget : Nat)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length spine reached childSize strict =>
      SelectedCompilationPhysicalTerminalLambdaBodyBounds.source_body_at
        captured code history inputs functions owner caller callerPrefix capturedSlots physical stable beforeTyped argumentsTyped terminal certifies
        entry added length spine reached budget childSize (Nat.le_of_lt strict) children)
    trace within

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- Reflection selects the authentic strict native body child and constructs
its independently graded Source body from the expression hypothesis. -/
theorem application_reflects (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) (valid : Dynamic.ClosureFrame program function)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies program stages sourceSize invocation callContext before
        (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable child selected valid budget
    (fun entry reached childSize strict =>
      SelectedCompilationPhysicalTerminalLambdaBodyBounds.native_body_at
        captured code history inputs functions owner caller callerPrefix capturedSlots physical stable beforeTyped argumentsTyped terminal certifies
        entry reached child selected valid budget childSize (Nat.le_of_lt strict) children)
    completed within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
