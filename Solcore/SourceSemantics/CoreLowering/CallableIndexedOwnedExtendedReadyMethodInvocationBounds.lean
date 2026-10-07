import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations

/-! Genuine method selections and original parameter receipts select their
strict body child from the extended joint family. Actual invocation preserves
the reached body pool through the saved-frame write. Source and native sizes
remain independent; the existing measured method cores are reused. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {headerCertificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {headerSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments profile.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (observed : CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 0 [] installed.canonical)

variable (syntaxTree : GenericImperativeMatch.Syntax principal.sourceFunction.source expressionSyntax profile.context
    (.statements true principal.sourceFunction.body) principal.sourceFunction.resultType)

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
theorem source_continuation (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget) :
    CallableIndexedOwnedMethodInvocationBounds.SourceContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  exact CallableIndexedOwnedMethodReadyFamilyReceipts.source_continuation
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree budget (fun index => below (.existing (.method index)))

include wellFormed beforeTyped argumentsTyped stable observed syntaxTree in
theorem native_continuation (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget) :
    CallableIndexedOwnedMethodInvocationBounds.NativeContinuationWithHistory
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) (owner := owner) (caller := caller)
      principal.cached.compilation profile functions escaped extend runtimeOf installed budget := by
  exact CallableIndexedOwnedMethodReadyFamilyReceipts.native_continuation
    principal profile functions escaped extend runtimeOf installed owner caller wellFormed
    beforeTyped argumentsTyped stable observed syntaxTree budget (fun index => below (.existing (.method index)))

variable (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world principal.named.inputs arguments payloads)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

include escaped extend runtimeOf wellFormed beforeTyped argumentsTyped stable observed syntaxTree represented sameFrame heaps in
theorem invocation_preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size principal.sourceBody principal.dictionary before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_preserves_bounded_at_with_history
    principal.cached.compilation profile functions escaped extend runtimeOf installed represented owner caller sameFrame heaps budget
    (source_continuation principal profile functions escaped extend runtimeOf installed owner caller
      wellFormed beforeTyped argumentsTyped stable observed syntaxTree budget below)
    trace within

include escaped extend runtimeOf wellFormed beforeTyped argumentsTyped stable observed syntaxTree represented sameFrame heaps in
theorem invocation_reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := headerCertificates) (expressionSyntax := headerSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (principal.cached.compilation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize principal.sourceBody principal.dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_reflects_bounded_at_with_history
    principal.cached.compilation profile functions escaped extend runtimeOf installed represented owner caller sameFrame heaps budget
    (native_continuation principal profile functions escaped extend runtimeOf installed owner caller
      wellFormed beforeTyped argumentsTyped stable observed syntaxTree budget below)
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
