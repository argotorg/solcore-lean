import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Original Header-supported lambda formation remains authentic under the
additive method-lambda model. Only the proved forward inclusion transfers
its representation. The actual nested packet, Source occurrence and captured
history stay original; formation copies the captured cells, and the packet and
admission are transported to the formed pool and store. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)} {rank : Nat}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

include complete globals slots prefixZero packet related agrees nativeTyped in
/-- Genuine nested packet facets select the original formation producer.
Forward inclusion adds the model alternative without weakening Source authority. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        (CallableIndexedNamedGeneration.source caller.named) environment heap id (.closure (formed head captured))
        finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)
        finalMap finalWorld head.code.sourceNode.type (.closure (formed head captured)) value lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld finalHeap
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap := by
  obtain ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, copy, native, represented,
      finalHeaps, maps, worlds, frame, metadata, _transition⟩ :=
    CallableIndexedOwnedLambdaViewHeads.formation_in head profile complete globals slots initial owner prefixZero
      packet.observed packet.carried packet.bundle related agrees nativeTyped
      (CallableIndexedOwnedMethodLambdaValues.includes_original keys registry faults profile) heaps
  exact ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, copy, native, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

/-- Full expression leaf effects accompany the same authentic nested packet,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
        context head.code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (typed : ExpressionHasType source context id head.code.sourceNode.type)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)) context ⟨initial, packet⟩)

include slots related agrees nativeTyped complete globals prefixZero wellFormed runtime covers locals typed sameSource unique heaps admitted in
/-- Original lambda inversion selects the actual Source closure and same heap;
proved formation and genuine Source preservation supply its admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment heap id outcome after) :
    ∃ result finalStore, ResultAt (actual := actual) (ξ := ξ) head profile owner initial packet outcome after result finalStore := by
  let code := actualCode head environment
  rw [sameSource] at unique trace
  cases trace.sound with
  | value evaluated =>
    rename_i sourceValue
    have original : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        (formed head environment).context (formed head environment).evidence (formed head environment).source
        (formed head environment).captured heap code.id sourceValue after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using evaluated
    obtain ⟨sourceCaptured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) (program := Program.ofChecked compiled.sourceProgram) code unique head.coercions original
    obtain ⟨value, formedCaptured, finalHeap, finalStore, finalMap, finalWorld, sourceTrace, formedCopy, native,
        represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      formation head profile complete globals slots owner prefixZero initial packet related agrees nativeTyped heaps
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
    have sourceTrace' : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source
        environment heap id (.closure (formed head sourceCaptured)) after := by simpa only [sameSource] using sourceTrace
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      ⟨initial, packet⟩ maps worlds frame metadata
    have post := after_expression
      (bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
        (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller))
      (context := context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace') frame
    exact ⟨.inRight .word value, finalStore, native, finalMap, finalWorld, .value represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩
  | fault failed =>
    rename_i reason
    have original : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
        (formed head environment).context (formed head environment).evidence (formed head environment).source
        (formed head environment).captured heap code.id reason after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using failed
    exact False.elim (excludes_fault_of_code (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) (program := Program.ofChecked compiled.sourceProgram) code unique head.coercions original)

include slots related agrees nativeTyped complete globals prefixZero wellFormed runtime covers locals typed sameSource unique heaps admitted in
/-- Determinism identifies the actual native completion. The constructed
Source formation keeps its independently measured grade and same post packet. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap id outcome after ∧
      ResultAt (actual := actual) (ξ := ξ) head profile owner initial packet outcome after result finalStore := by
  obtain ⟨value, formedCaptured, finalHeap, formedStore, _finalMap, _finalWorld, sourceTrace, _copy, native,
      _represented, _finalHeaps, _maps, _worlds, _frame, _metadata⟩ :=
    formation head profile complete globals slots owner prefixZero initial packet related agrees nativeTyped heaps
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence source
      environment heap id (.value (.closure (formed head formedCaptured))) finalHeap := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  obtain ⟨actualResult, actualStore, resultAt⟩ := preserves_at head profile complete globals slots owner prefixZero
    initial packet related agrees nativeTyped wellFormed runtime covers locals typed sameSource unique heaps admitted sized
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic resultAt.1 native
  exact ⟨sourceSize, _, finalHeap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
