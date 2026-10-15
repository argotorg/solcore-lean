import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults

/-! The physical second decision follows the actual successful ordered argument
prefix. A count mismatch invokes the existing semantic application-arity rule;
the first guard's scoped stage failure is unchanged and handled separately.
The original Selected row determines the word, while genuine receiving issuance
interprets it at the same reached argument state. This construction is separate
from the integrated NEW12 group. NamedOrigin is only authentic Header/SourceAt provenance, not a
count equality, application result, body trace or completed meaning law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

/-- The genuine global branch retains the same original BodyInstance. -/
def NamedOrigin (compiled : SourceCoreUnifiedCompilation.Compiled)
    (sourceValue : Dynamic.Value) : Prop :=
  ∀ function, sourceValue = .global function →
    ∃ (header : Header compiled (Program.ofChecked compiled.sourceProgram))
      (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment), NamedSourceAt header rawD function

section SourceBoundary
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before calleeHeap argumentsHeap : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId}
  {metadata originalMetadata : IndirectCallResolution} {originalNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {sourceValue : Dynamic.Value} {carrier : Value} {sources : List Dynamic.Value}
  {calleeSize argumentsSize : Nat}

/-- Real closure, global and builtin bindings supply each physical parameter
list. The conditional conclusion is constructed from the actual two Source
prefixes; no trace is retained in a static compiler certificate. -/
theorem source_at_boundary
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (occurrence : Staging.Recursive.Occurrence invocation call (.call callee ids (.indirect metadata)))
    (uncoerced : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      calleeSize invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids sourceValue)
    (arguments : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages
      argumentsSize invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (boundary : BoundaryAt sidecar site callee ids originalMetadata originalNode sourceValue carrier)
    (named : NamedOrigin compiled sourceValue) :
    ∃ raw tag row, carrier = .pair raw (.word tag) ∧
      Selected sidecar site callee ids originalMetadata originalNode row ∧ site.rowAt? tag = some row ∧
      ∀ (_different : row.entry.parameterCount ≠ ids.length),
        Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
          invocation context environment before call
          (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) argumentsHeap := by
  cases boundary with
  | user dispatch selected =>
    cases (CallableLedger.frame sidecar).userCallable dispatch.bound with
    | closure function =>
      have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      intro different
      have mismatch : function.parameters.length ≠ ids.length := by
        simpa only [physical] using different
      simpa only [physical] using
        CallableIndexedOwnedPreparedSecondCallGateRejection.closure_source
          occurrence uncoerced sourceArity arguments child accepted mismatch
    | global function =>
      obtain ⟨header, rawD, sourceAt⟩ := named function rfl
      have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt caller dispatch selected
      refine ⟨dispatch.function, dispatch.contract, dispatch.row, dispatch.shape, selected, dispatch.found, ?_⟩
      intro different
      have mismatch : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using different
      simpa only [physical] using
        CallableIndexedOwnedPreparedSecondCallGateRejection.named_source
          occurrence uncoerced sourceArity arguments sourceAt child accepted mismatch
  | builtin receipt =>
    rename_i function row
    obtain ⟨raw, shape⟩ := receipt.shape
    refine ⟨raw, _, _, shape, receipt.selected, receipt.selected.found, ?_⟩
    intro different
    have physical := receipt.parameter_count
    have mismatch : function.id.parameterTypes.length ≠ ids.length := by simpa only [physical] using different
    simpa only [physical] using
      CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_source
        occurrence uncoerced sourceArity arguments child mismatch
end SourceBoundary

section NativeSuffix
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {row : SourceCoreStageCodebook.Decision}
  {raw carrier packed : Value} {tag unknown : Word} {actual : Environment}
  {argumentsStore finalStore : Store} {result : Ty} {size : Nat} {value : Value}

/-- Pure second dispatch fixes its original word and retains the argument
store. There is no application evaluation in this rejection branch. -/
theorem rejected_suffix
    (shape : carrier = .pair raw (.word tag))
    (selected : Selected sidecar site callee ids metadata node row)
    (found : site.rowAt? tag = some row)
    (different : row.entry.parameterCount ≠ ids.length)
    (completed : EvaluationSize size (packed :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind result (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore) :
    value = .inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication
      (.argumentArityMismatch row.entry.parameterCount ids.length))) ∧ finalStore = argumentsStore := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) argumentsStore
      (.second (.var 2)) (.word tag) argumentsStore := by
    rw [shape]
    exact .second (.var rfl)
  have gate := CallableContract.dispatch_evaluates site.gates .beforeApplication unknown tag read
  rw [CallableIndexedOwnedPreparedSecondCallGateRejection.rejected_gate selected found different unknown,
    CallableContract.resultValue] at gate
  exact evaluation_deterministic completed.sound (LanguageResult.bind_failure result gate)
end NativeSuffix

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
    («prefix» : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore)
    (namedOrigins : ∀ {sourceValue carrier finalMap finalWorld},
      GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
        sourceValue carrier compiler.calleeCode.type → NamedOrigin compiled sourceValue) :
    ∃ originalNode originalMetadata row,
      Selected sidecar prepared.site callee ids originalMetadata originalNode row ∧
      (row.entry.parameterCount = ids.length ∨
        ∃ sourceSize after token finalMap finalWorld,
          Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
            invocation context environment before id
            (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) after ∧
          value = .inLeft lowered.type (.word token) ∧
          CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
            (registry := completion.result.context.registry) (faults := publicFaults) (context := context)
            (actual := actual) (ξ := ξ) bridge functions compiler initial
            (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)) after token finalStore finalMap finalWorld) := by
  obtain ⟨rawParameter, rawResult, _calleeType, _bundle, _originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    child, accepted, arguments, _representedValues, representedCallee, _callView, boundary,
    finalHeaps, maps, worlds, frame, metadataExtension, ⟨reached, related, admitted⟩,
    suffixSize, suffix, _strict⟩ := «prefix»
  obtain ⟨raw, tag, row, shape, selected, found, sourceFault⟩ :=
    source_at_boundary caller occurrence compiler.argumentCoercions sourceParent.arity
      child accepted arguments boundary (namedOrigins representedCallee)
  refine ⟨originalNode, originalMetadata, row, selected, ?_⟩
  by_cases same : row.entry.parameterCount = ids.length
  · exact .inl same
  · have lowerType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    obtain ⟨sameValue, sameStore⟩ := rejected_suffix shape selected found same suffix
    cases sameStore
    obtain ⟨represented, keptHeaps, keptState, sameState, keptRelated⟩ :=
      CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
        compiler prepared preparedStages selected receiver initial functions reached related finalHeaps
        (sourceResult := compiler.original.type) (resultCore := lowered.type) same
    cases sameState
    refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
      argumentsHeap, prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length),
      finalMap, finalWorld, sourceFault same, ?_, ?_⟩
    · simpa only [lowerType] using sameValue
    · refine ⟨?_, CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented,
        keptHeaps, maps, worlds, frame, metadataExtension, reached, keptRelated, ?_⟩
      · simpa only [sameValue, lowerType] using completed.sound
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩
end WholeParent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds
