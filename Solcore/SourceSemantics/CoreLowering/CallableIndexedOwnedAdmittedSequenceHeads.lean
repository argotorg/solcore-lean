import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Tuple and contracted builtin heads use admitted children through one whole
ordered sequence at the actual caller input. The genuine parent Source typing
provides an independent operand row. Successful whole execution establishes
admission at the identical reached witness; faults retain stable rows. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment)
  {children : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)

include wellFormed runtime covers unique

namespace Tuple

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (CompatibleExpressionTuples.Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨originalTypes, typing⟩ := operand_types unique receipt.metadata.found parentTyped
  have argumentsTyped : ExpressionsHaveTypes source context ids originalTypes := by
    simpa only [receipt.form, actualOperandIds] using typing
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.preserves_bounded_with_sequence functions program evidence callerProtocol
      budget size within unique receipt initial
      (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted sequence unique argumentsTyped
        environments heaps locals agrees actualTyped (budget + 1) (fun n bound => meaning n (by omega))) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (CompatibleExpressionTuples.Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted evaluated
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨originalTypes, typing⟩ := operand_types unique receipt.metadata.found parentTyped
  have argumentsTyped : ExpressionsHaveTypes source context ids originalTypes := by
    simpa only [receipt.form, actualOperandIds] using typing
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.reflects_bounded_with_sequence functions program evidence callerProtocol
      budget size within receipt initial
      (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted sequence unique argumentsTyped
        environments heaps locals agrees actualTyped (budget + 1) (fun n bound => meaning n (by omega))) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩
end Tuple

namespace Builtin
open BuiltinCalls BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix)
variable {identities : Dynamic.Value → Word → Prop}
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include functionLeaves in
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (BuiltinCalls.Typed.Head values source children) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨originalTypes, typing⟩ := operand_types unique metadata.found parentTyped
    have argumentsTyped : ExpressionsHaveTypes source context arguments originalTypes := by
      simpa only [form, actualOperandIds] using typing
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related⟩ :=
      RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_bounded_with_sequence functions functionLeaves
        program evidence unique callerProtocol budget size within metadata form sourceType nativeTypes initial
        (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted sequence unique argumentsTyped
          environments heaps locals
          (agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit)
          (RecursiveNamedBuiltinHeadBounds.Stateful.prefixed_typed actualTyped function identity contract)
          (budget + 1) (fun n bound => meaning n (by omega))) trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related,
      after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include functionLeaves in
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (BuiltinCalls.Typed.Head values source children) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped initial admitted completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨originalTypes, typing⟩ := operand_types unique metadata.found parentTyped
    have argumentsTyped : ExpressionsHaveTypes source context arguments originalTypes := by
      simpa only [form, actualOperandIds] using typing
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related⟩ :=
      RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_bounded_with_sequence functions functionLeaves
        program evidence callerProtocol budget size within metadata form sourceType nativeTypes initial
        (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted sequence unique argumentsTyped
          environments heaps locals
          (agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit)
          (RecursiveNamedBuiltinHeadBounds.Stateful.prefixed_typed actualTyped function identity contract)
          (budget + 1) (fun n bound => meaning n (by omega))) completed
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related,
      after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩
end Builtin
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
