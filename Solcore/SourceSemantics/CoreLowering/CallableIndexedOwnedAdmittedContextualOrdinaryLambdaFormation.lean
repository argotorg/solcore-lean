import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries

/-! The actual formation retains its contextual provenance. Original finite
formation and admitted endpoints provide the same traces and reached packet;
only the represented output closure gains its authentic static receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual canonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

variable (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)


include packet prefixContext observed inclusion provenance in
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
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl rfl profile stored ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).runtime_hasType
    (registry := registry) represented
  have retained : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .contextual_ordinary_lambda owner captured code (history_at captured code support owner initial packet)
      support (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed provenance
  exact ⟨sourceTrace, native, inclusion retained, determined⟩

/-- The original full reached result is retained verbatim, together with
its exact contextual packet and the actual formed Source/native value. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore ∧
  CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support ∧
  outcome = .value (.closure function) ∧ after = heap ∧
  result = .inRight .word (value code captured.embedding
    (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual) ∧
  finalStore = store

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
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)


include prefixContext observed inclusion sourceType ordinary coercions heaps provenance in
private theorem strengthen_result {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Value} {finalStore : Store}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after)
    (original : CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt captured code support owner initial packet functions outcome after result finalStore) :
    ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨_sourceTrace, _native, represented, determined⟩ :=
      formation captured code support owner initial packet profile prefixContext observed provenance functions inclusion heaps.runtime_hasTypes ordinary coercions
    obtain ⟨rfl, rfl⟩ := determined result finalStore original.1
    have payload : ValueRep compiled.compatible.checked registry functions mapping world code.sourceNode.type
        (.closure function) (value code captured.embedding (history_at captured code support owner initial packet).native actual)
        code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    exact ⟨⟨original.1, .value payload, original.2.2⟩, provenance, rfl, rfl, rfl, rfl⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed inclusion sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- Original admitted preservation fixes the actual state and post. The
contextual representation strengthens only its freshly formed value. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨result, finalStore, original⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.preserves_at captured code support owner initial packet profile prefixContext observed functions inclusion
      wellFormed runtime covers locals typed sourceType ordinary coercions heaps admitted trace
  exact ⟨result, finalStore, strengthen_result captured code support owner initial packet profile prefixContext observed provenance functions inclusion
    sourceType ordinary coercions heaps trace original⟩

include prefixContext observed inclusion sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed provenance in
/-- The original native reflection supplies its independent Source grade and
reached packet. No native type is inverted to obtain contextual provenance. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, original⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reflects_at captured code support owner initial packet profile prefixContext observed functions inclusion
      wellFormed runtime covers locals typed sourceType ordinary coercions heaps admitted completed
  exact ⟨sourceSize, outcome, after, trace, strengthen_result captured code support owner initial packet profile prefixContext observed provenance functions inclusion
    sourceType ordinary coercions heaps trace original⟩

end CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation
