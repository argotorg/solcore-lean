import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation

/-! Method formation keeps the caller's function model throughout its heap
and result receipts. Forward inclusion transfers only the authentic newly
formed closure; the real principal packet and Source post stay unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaFormationReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile).Includes functions)

include packet inclusion in
/-- The original actual formation supplies the closure. Only its function
representation is transferred forward to the caller's model. -/
theorem formation
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) := by
  obtain ⟨sourceTrace, native, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation captured code support owner initial packet
      profile stored ordinary coercions
  exact ⟨sourceTrace, native, inclusion represented, determined⟩

/-- The output retains all ordinary leaf effects and the exact packet state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, mapping, world, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
    PostAdmission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include inclusion sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨sourceTrace, native, represented, _determined⟩ :=
      formation captured code support owner initial packet profile functions inclusion heaps.runtime_hasTypes ordinary coercions
    have valueRep : ValueRep compiled.compatible.checked registry
        functions mapping world
        code.sourceNode.type (.closure function)
        (value code captured.embedding (history_at captured code support owner initial packet).native actual) code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    have post := after_expression
      (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
    exact ⟨_, store, native, .value valueRep, heaps, .refl _, .refl _, .refl _ _, .refl _,
      ⟨initial, packet⟩, Relates.refl initial, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include inclusion sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support owner initial packet profile functions inclusion heaps.runtime_hasTypes ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support owner initial packet profile functions inclusion
    wellFormed runtime covers locals typed sourceType ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, heap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormationWithFunctions
