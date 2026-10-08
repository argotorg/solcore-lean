import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

/-! An ordinary lambda certificate contains only its authentic ranked static
receipt. The generic admitted leaf constructs captures, code and history from
the actual input environment and nested packet through the original producer.
The additive model is used throughout the input heap and returned payload. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

/-- Static formation support fixes the genuine Header and original Source
occurrence. Captures and runtime authority are supplied at the actual input. -/
def Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ rank, Nonempty
    (LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)

def bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)

def model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)

variable
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)

include complete globals slots prefixZero wellFormed runtime covers sameSource unique in
/-- The original finite formation proof is selected by the static certificate
and consumes exactly the caller packet and represented environment it receives. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (headers := headers) (bridge (headers := headers) caller owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) context evidence source
      (Certificate (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨rank, ⟨head⟩⟩ := certified
  have sourceFound : source.lookupExpression? id = some head.code.sourceNode := by
    simpa only [sameSource, CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨result, finalStore, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.preserves_at head profile complete globals slots owner prefixZero
      initial.val initial.property environments agrees nativeTyped wellFormed runtime covers locals typed
      sameSource unique heaps admitted trace
  exact ⟨result, finalStore, mapping, world, native, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

include complete globals slots prefixZero wellFormed runtime covers sameSource unique in
/-- Native completion is reflected by the same authentic formation producer;
the original Source formation is independently sized at the unchanged pool. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (headers := headers) (bridge (headers := headers) caller owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) context evidence source
      (Certificate (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨rank, ⟨head⟩⟩ := certified
  have sourceFound : source.lookupExpression? id = some head.code.sourceNode := by
    simpa only [sameSource, CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨sourceSize, outcome, after, trace, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.reflects_at head profile complete globals slots owner prefixZero
      initial.val initial.property environments agrees nativeTyped wellFormed runtime covers locals typed
      sameSource unique heaps admitted completed
  exact ⟨sourceSize, outcome, after, mapping, world, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
