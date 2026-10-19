import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentPrefix

/-! The reached second gate uses the original selected row and receiving
word. Its genuine count branch preserves the same mixed argument heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds (NamedOrigin source_at_boundary rejected_suffix)
universe u

section WholeParent
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (sourceParent : SourceParent compiler)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "publicFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include caller occurrence sourceParent preparedStages receiver in
omit positive in
/-- The actual selected count decides the branch internally. Successful
arguments already carry their real independent grades and reached admission.
The mismatch constructs Source arity, its literal receiver lookup and the same
whole-parent fault post. The equal-count alternative retains only that actual
row fact for the separate application producer. -/
theorem classify_application_prefix {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    («prefix» : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ∃ originalNode originalMetadata row,
      Selected sidecar prepared.site callee ids originalMetadata originalNode row ∧
      (row.entry.parameterCount = ids.length ∨
        ∃ sourceSize after token finalMap finalWorld,
          Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
            invocation context environment before id
            (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) after ∧
          value = .inLeft lowered.type (.word token) ∧
          CellAwareScopeIndirectCalleeFaultBounds.ResultAt
            (registry := completion.result.context.registry) (faults := publicFaults) (context := context)
            (actual := actual) (ξ := ξ) bridge functions compiler initial
            (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)) after token finalStore finalMap finalWorld) := by
  obtain ⟨rawParameter, rawResult, _calleeType, _bundle, _originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    child, accepted, arguments, _representedValues, _representedCallee, strong, _callView, boundary,
    finalHeaps, maps, worlds, frame, metadataExtension, effect, ⟨reached, related, admitted⟩,
    suffixSize, suffix, _strict⟩ := «prefix»
  have namedOrigins : NamedOrigin compiled sourceValue := by
    intro global same
    obtain ⟨function, native, bindings, parameter, result, closure, _rest⟩ := strong sourceValue rfl
    rw [closure] at same
    cases same
  obtain ⟨raw, tag, row, shape, selected, found, sourceFault⟩ :=
    source_at_boundary caller occurrence compiler.argumentCoercions sourceParent.arity
      child accepted arguments boundary namedOrigins
  refine ⟨originalNode, originalMetadata, row, selected, ?_⟩
  by_cases same : row.entry.parameterCount = ids.length
  · exact .inl same
  · have lowerType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    obtain ⟨sameValue, sameStore⟩ := rejected_suffix shape selected found same suffix
    cases sameStore
    obtain ⟨diagnostic, decoded, error⟩ :=
      CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
        compiler prepared preparedStages selected receiver same
    have represented : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type
        (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
        (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
        (.inLeft lowered.type (.word (prepared.site.reasonAt row.caller row.call row.entry.id
          .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) :=
      .fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
    refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
      argumentsHeap, prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length),
      finalMap, finalWorld, sourceFault same, ?_, ?_⟩
    · simpa only [lowerType] using sameValue
    · refine ⟨?_, CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented,
        finalHeaps, maps, worlds, frame, metadataExtension, effect, reached, related, ?_⟩
      · simpa only [sameValue, lowerType] using completed.sound
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩
end WholeParent
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds
