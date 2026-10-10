import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds

/-! A supported terminal body uses its literal compiler receipt and the
actual parameter entry. The selected registry supplies its original Source
scope, and the retained Code supplies the compiler metadata view. Original
body typing and parameter admission are constructed before the used strict
expression hypothesis is invoked. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalLambdaBodyBounds
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

include stable beforeTyped argumentsTyped terminal certifies in
/-- The actual Source closure rule supplies its selected scope and frame.
The same compiler body and parameter pool satisfy the Source body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (budget bodySize : Nat) (within : bodySize ≤ budget)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled) (program := program)
          (headers := headers) (keys := keys)) inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled) (program := program)
          (headers := headers) (keys := keys)))
    (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
    (environments := entry.entry.environments) (heaps := entry.entry.heaps)
    (locals := entry.entry.locals) (agrees := entry.entry.lookups)
    (typed := entry.entry.actualTyped) (initial := reached) (admitted := admitted)
    unique budget (children child selected) trace matched within

include stable beforeTyped argumentsTyped terminal certifies in
/-- Native completion uses the same retained parameter prefix and original
registry scope. Its independently graded Source body is constructed from the
strict expression reflection at that actual entry. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function)
    (budget nativeSize : Nat) (within : nativeSize ≤ budget)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled) (program := program)
          (headers := headers) (keys := keys)) inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached child nativeSize := by
  intro value bodyStore completed
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
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
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled) (program := program)
          (headers := headers) (keys := keys)) inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, meaning,
      heaps, maps, worlds, frame, metadata, returned⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled) (program := program)
          (headers := headers) (keys := keys)))
      (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
      (environments := entry.environments) (heaps := entry.heaps)
      (locals := entry.locals) (agrees := entry.lookups) (typed := entry.actualTyped)
      (initial := reached) (admitted := admitted) unique budget children completed within
  exact ⟨sourceSize, inputs.context,
    CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, meaning,
    heaps, maps, worlds, frame, metadata, returned⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalLambdaBodyBounds
