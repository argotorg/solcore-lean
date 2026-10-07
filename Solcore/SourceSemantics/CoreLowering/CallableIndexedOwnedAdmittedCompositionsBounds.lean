import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! Genuine parent typing supplies only its actual ordered operand row. The
shared readiness composition proof passes each child's exact successful state
to the next child or selected branch. Its returned witness is retained when
original Source preservation supplies the parent's full post admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}

/-- Only actual operand slots receive Source typing and child admission. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate) faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _⟩ :=
    RecursiveNamedExpressionCompositionsBounds.Stateful.WithReady.Head.preserves_at functions program evidence
      callerProtocol (Admission bridge context) budget size bounded unique tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.PreservesAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.preserves_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- The real reflected Source trace keeps its independent grade and certifies
post admission at the exact reached native witness. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate) faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _⟩ :=
    RecursiveNamedExpressionCompositionsBounds.Stateful.WithReady.Head.reflects_at functions program evidence
      callerProtocol (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.ReflectsAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.reflects_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      environments heaps locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
