import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues

/-! Actual method-principal packets supply the complete formation history and
captured bundle. Source authority stays in the genuine same-Code support;
native environment tags establish only the corresponding bundle observation.
The original formation producers leave the actual pool and store unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport

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

/-- The packet's own physical row retains the full authentic compiler seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.principal.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

/-- The original method Source seed is retained by construction. -/
theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include packet in
/-- The genuine captured environment identifies its existing leading bundle. -/
theorem leading : captured.administrative[0]? = some support.principal.named.signature.parameterType := by
  have bundle := packet.bundle
  rw [captured.represented.runtime_hasTypes.type_tags] at bundle
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using bundle

include support in
/-- Same-Code method compilation fixes the original physical frame slot. -/
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

include packet in
/-- Real Source and native formation, native typing and deterministic output
follow the original producers at this exact packet and pool. -/
theorem formation
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    CallableIndexedOwnedMethodLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) := by
  exact CallableIndexedOwnedMethodLambdaValues.method_lambda_of_formation initial owner captured code
    (history_at captured code support owner initial packet) support
    (source_origin captured code support owner initial packet) packet.observed
    (reference_index captured code support) rfl rfl profile stored ordinary coercions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFormationReceipts
