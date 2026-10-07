import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs

/-! The actual selected lambda entry carries its genuine compiler layout.
Only that exact dependent index enters the joint family; no arbitrary static
lambda origin is assigned compiled layouts. Strict child results return the
same original reached pool and independently measured Source trace. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointLambdaReadyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (layouts : body.origin.layouts = compiled.indexed.layouts)

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- Each authentic actual Source parameter entry constructs its index and
uses only the strict shared-family child in that index's exact protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (CallableIndexedOwnedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached child strict outcome after trace
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_source_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry added length spine reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry added length spine reached
  have ready := below (.lambda index layouts) child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include layouts wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- The original measured prefix constructs the same static index directly;
reflection preserves the independently reconstructed Source body grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (CallableIndexedOwnedJointReadyFamilyInputs.protocol index)
          (readiness (CallableIndexedOwnedJointReadyFamilyInputs.bridge index))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (CallableIndexedOwnedJointReadyFamilyInputs.inputs wellFormed index).facts
          functions (Program.ofChecked compiled.sourceProgram) (CallableIndexedOwnedJointReadyFamilyInputs.origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict value finalStore completed
  let index := CallableIndexedOwnedLambdaReadyFamilyReceipts.of_native_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry reached
  have ready := below (.lambda index layouts) child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointLambdaReadyContinuations
