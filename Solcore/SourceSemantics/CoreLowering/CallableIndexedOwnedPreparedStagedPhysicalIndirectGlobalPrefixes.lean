import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The uncompleted named branch retains the actual global value, all three
Source prefixes and application suffix, and every native prefix witness. -/
def GlobalAppliedPrefix (calleeSize argumentsSize applicationSize : Nat)
    (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    sourceValue = .global function ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functions)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources

/-- This remaining branch retains the actual global value and complete
original user prefix. It supplies no named application or body meaning. -/
def GlobalApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ function : Dynamic.GlobalFunction,
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
    ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
        argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
      CallableIndexedOwnedPreparedStagedIndirectNativePrefix.CalleePost
        (registry := completion.result.context.registry) (context := context) (actual := actual)
        (ξ := ξ) (calleeNode := calleeNode) bridge functions compiler initial
        (.global function) calleeHeap carrier calleeStore calleeMap calleeWorld ∧
      Dynamic.ValueHasType context calleeHeap (.global function) calleeNode.type ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
        invocation context environment before callee (.value (.global function)) calleeHeap ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function) ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
        invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
      DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
      GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
        (.global function) carrier compiler.calleeCode.type ∧
      CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.CallView originalNode compiler.original originalMetadata metadata ∧
      CallableIndexedOwnedContextualCalleeStageReceipts.BoundaryAt
        sidecar prepared.site callee ids originalMetadata originalNode (.global function) carrier ∧
      GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
        argumentsStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

/-- The remaining named branch carries the same original parent size and a
strict actual Source application child, alongside all original prefix receipts. -/
def GlobalAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after


end CallableIndexedOwnedPreparedStagedPhysicalIndirectGlobalPrefixes
