import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier

/-! Observe the same finite named invocation's represented result. Successful
Word payloads have identical Source and native words; language failures retain
their genuine diagnostic relation. This proof does not execute or export a
value, and does not turn native completion into public export success. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence

/-- Observable payload or language failure, with the same original fault map. -/
inductive Observation (faults : FunctionCalls.FaultRep) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | word (value : Word) : Observation faults (.value (.word value))
      (.inRight .word (.word value))
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      (related : faults reason token) : Observation faults (.fault reason)
      (.inLeft .word (.word token))

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : CallableIndexedNamedGeneration.Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

include inventory in
/-- The authenticated Header's output is the actual retained Word signature. -/
theorem output_word (bootstrap : BootstrapEvidence fixture caller) : caller.output = .word := by
  have same := caller.resultType
  rw [bootstrap.named] at same
  exact same.symm.trans inventory.resultType

/-- The receiving function model supplies the observation theorem. The
returned heap, pool and cumulative effects remain in the original ResultAt. -/
theorem observe (bootstrap : BootstrapEvidence fixture caller)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : GeneralHeap.LocationMap}
    {finalWorld : StoreTyping}
    (result : SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld) : Observation faults outcome value := by
  have represented := result.1
  have output := output_word fixture inventory bootstrap
  rw [output] at represented
  cases represented with
  | value payload =>
    have observations : CompatibleEquality.FunctionObservations fixture.packet.compiled.compatible.checked.catalog
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (CallableIndexedLambdaValues.Identity fixture.packet.compiled.indexed) :=
      CallableIndexedOwnedChosenOrdinaryLambdaValues.observations root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture) registry faults inventory.contracts
    obtain ⟨word, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
    cases sourceEq
    cases nativeEq
    exact .word word
  | fault related => exact .fault related

theorem Observation.word_iff {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {native : Core.Value} (observed : Observation faults outcome native)
    (word : Word) : outcome = .value (.word word) ↔ native = .inRight .word (.word word) := by
  cases observed with
  | word actual => simp only [Dynamic.ExpressionOutcome.value.injEq, Dynamic.Value.word.injEq,
      Core.Value.inRight.injEq, Core.Value.word.injEq, true_and]
  | fault related => simp

theorem Observation.fault_iff {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {native : Core.Value} (observed : Observation faults outcome native) :
    (∃ reason, outcome = .fault reason) ↔ (∃ token, native = .inLeft .word (.word token)) := by
  cases observed with
  | word actual => simp
  | fault related => simp

end Tests.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
