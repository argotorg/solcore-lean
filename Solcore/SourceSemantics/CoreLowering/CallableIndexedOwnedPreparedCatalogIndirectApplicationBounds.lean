import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds

/-! The actual argument post selects one positive retained application packet.
This adapter builds the original indirect parent's application ports from the
concrete dispatcher and strict body children. The packet factory has no trace,
grade, outcome or execution law input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {canonical : Environment}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Value} {calleeNative : Value}
  {sourceTypes : List TypeSystem.Ty} {sourceResultType : TypeSystem.Ty} {resultCore : Ty}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- An honest contextual packet factory at the admitted argument state. It
retains only the positive closure/global/builtin constructor and raw result
alignment. Each producer must use the same actual carrier and argument list. -/
def ArgumentPackets : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      Receipt (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := middleMap) (world := middleWorld) (before := middle)
        (arguments := arguments) (payloads := payloads)
        functions function invocation calleeNative actualSourceResult resultCore

private theorem result_at_raw_type {finalMap : LocationMap} {finalWorld : StoreTyping}
    {actualSourceResult : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (same : SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult)
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld actualSourceResult resultCore faults outcome value) :
    FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value := by
  cases related with
  | value payload => exact .value (.compatible same payload)
  | fault matched => exact .fault matched

variable (packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (context := context) (invocation := invocation) (canonical := canonical)
    (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
    (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
    (sourceResultType := sourceResultType) (resultCore := resultCore) bridge functions compiler)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include packets wellFormed observations in
/-- The actual dispatcher constructs the application part of the original
parent from one selected packet and strict F. The argument trace is only a
runtime proof input; it is not retained by the packet factory. -/
theorem preserves (budget : Nat)
    (closures : ClosurePreservesBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedPreservesBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : CallableIndexedOwnedPreparedIndirectValueSourceSuffix.Suffix (Program.ofChecked compiled.sourceProgram)
      context evidence invocation source environment calleeHeap ids function argumentsSize callSize outcome after) :
    CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationPreserves
      (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (environment := environment)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore)
      (sourceResultType := sourceResultType) budget suffix := by
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
    rawArguments packing bundle argumentsSize callSize outcome after _argumentsTrace called _calledSuffix within
  obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
    calleeTyped extension represented heaps rawArguments packing bundle
  obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, returned, returnedRelated⟩ :=
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.preserves functions bridge argumentState
      heaps admitted.rows wellFormed receipt budget closures named observations called within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result_at_raw_type functions rawResult related,
    finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩

include packets wellFormed observations in
/-- Native reflection constructs its own Source suffix grade and retains the
same reached caller witness. No preservation proof is used in this direction. -/
theorem reflects (budget : Nat)
    (closures : ClosureReflectsBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedReflectsBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget) :
    CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationReflects
      (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (invocation := invocation)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore)
      (sourceResultType := sourceResultType) budget := by
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
    rawArguments packing bundle size value finalStore completed within
  obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
    calleeTyped extension represented heaps rawArguments packing bundle
  obtain ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, returned, returnedRelated⟩ :=
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.reflects functions bridge argumentState
      heaps admitted.rows wellFormed receipt budget closures named observations completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result_at_raw_type functions rawResult related,
    finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
