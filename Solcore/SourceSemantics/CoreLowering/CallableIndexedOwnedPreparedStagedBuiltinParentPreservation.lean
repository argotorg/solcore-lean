import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix

/-! The original builtin application supplies its accepted native suffix and
whole indirect parent at the actual argument endpoint. The strict callee and argument producers supply their
literal traces and reached caller admission. The builtin primitive has no body
child and leaves this whole heap and store unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {faults : RecursiveStageMeaning.FaultRep}
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
  {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel))
    finalMap finalWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
  (frame : AdministrativePreserved mapping store finalMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)
  {function : Dynamic.BuiltinFunction} {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {row : SourceCoreStageCodebook.Decision}
  (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
    sidecar prepared.site callee ids originalMetadata originalNode function carrier row)
  (count : row.entry.parameterCount = ids.length)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
  (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
    headers keys bodyRegistry registry semanticFaults profile finalMap finalWorld
    (.function parameter result) (.builtin function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functionModel)) finalMap finalWorld
    sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

include bridge compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  observations builtinAt count actualFunctionType calleeTyped calleeRelated represented bundle originalResult in
omit positive in
/-- The real primitive supplies the accepted native application once. The
literal callee and ordered argument computations are the strict child outputs;
their original binds complete at the same reached caller state. -/
theorem preserves_parent
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.builtin function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.builtin function) sources outcome after)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value,
      Evaluates actual store (lowered.expression.rename ξ) value argumentsStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      after = argumentsHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧
      Dynamic.HeapMetadataExtend before argumentsHeap ∧
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached := by
  have rows := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.at_arguments compiler
    actualFunctionType builtinAt count calleeTyped calleeRelated represented bundle originalResult
  obtain ⟨sourceResult, sameOutcome, sameHeap, _sourceGrade, primitive⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations rows.represented called
  subst outcome
  obtain ⟨_nativeSize, nativeValue, appliedNative, resultRep, _heap, _grade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions observations
      (faults := faults) (store := argumentsStore) rows.builtin rows.represented called
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (store := argumentsStore) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    shape builtinAt.selected builtinAt.selected.found count appliedNative.sound
  have gate := builtinAt.first_gate
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) nativeValue argumentsStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType gate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have resultAt : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults (.value sourceResult) nativeValue := by
    rw [rows.original_result, loweredType, rows.native_result]
    exact resultRep
  obtain ⟨sameReached, same, _reflexive, primitivePost⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.argument_post bridge reached admitted primitive
  cases same
  have callerPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type (.value sourceResult) reached := by
    rw [rows.original_result]
    exact primitivePost
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace (.builtin function)
    argumentsTrace sourceParent.arity called, nativeValue, whole, resultAt, sameHeap,
    heaps, maps, worlds, frame, heapMetadata, related, callerPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinParentPreservation
