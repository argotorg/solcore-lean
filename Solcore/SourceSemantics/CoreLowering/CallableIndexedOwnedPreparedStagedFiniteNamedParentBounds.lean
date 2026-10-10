import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix

/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
The finite named invocation producer constructs the terminal body internally.
Authentic Header, diagnostic, receiver and finite compiler/runtime inputs remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {stages : Staging.Recursive.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header argumentMap argumentWorld)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
    (owner := owner) header capture identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt namedPrepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed namedPrepared.named).owner)
  (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression)
  (sameLedger : header.context.solvedRequirements = header.solved)
  (runtimeLedger : RuntimeRequirementLedgerValid header.context)
  (headerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context header.function.source)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
  calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt nativeType in
private theorem arguments_at {argumentsSize : Nat}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap) :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.accepted_rows sourceAt compiler wellFormed
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments sourceAt wellFormed
      runtime covers locals calleeHeapTyped typing calleeTyped bundle physicalArity argumentsTrace
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := completion.result.context.registry) (payloads := values) functions owner (bridge.pool reached) header capture
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal namedPrepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger headerRuntime in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (headerCovers : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      child.evidence.Covers header.context)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.application_preserves
      (prepared := namedPrepared) (aligned := aligned) (diagnostic := diagnostic) (receiver := receiver)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger) (runtime := headerRuntime)
      functions owner (bridge.pool reached) header capture sourceAt terminal sameLayouts member wellFormed
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget headerCovers called within
  change Evaluates [CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.carrier
    (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues values]
    argumentsStore CallableIndexedLambdaCalls.applyPayload value finalStore at application
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal namedPrepared aligned diagnostic receiver ordinary syntaxTree sameLedger runtimeLedger headerRuntime
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (headerCovers : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      child.evidence.Covers header.context)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedFiniteNamedInvocationBounds.application_reflects
      (prepared := namedPrepared) (aligned := aligned) (diagnostic := diagnostic) (receiver := receiver)
      (ordinary := ordinary) (syntaxTree := syntaxTree) (sameLedger := sameLedger)
      (runtimeLedger := runtimeLedger) (runtime := headerRuntime)
      functions owner (bridge.pool reached) header capture sourceAt terminal stagePrepared descriptor
      sameLayouts member wellFormed admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget headerCovers application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedParentBounds
