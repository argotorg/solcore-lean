import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites

/-! Genuine admission supplies lexical readiness at the actual reached state.
Allocation uses original Source receipts; restoration keeps that same heap and
native store. Expression adapters retain the full original child result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

def readiness : Readiness callerProtocol where
  Ready := fun context {_} state => Admission bridge context state
  FaultReady := fun {_} state => StableRows (bridge.pool state)
  ValueFacts := Dynamic.ValueHasType
  ready_fault := fun admitted => admitted.rows
  fault_after := fun first last rows frame =>
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) rows frame

/-- Binder facts transport the genuine Source heap context. Every restored
row is authenticated by its own real read in the retained native store. -/
theorem allocation_transfers (bindings : ProtectedStateTransition.Bindings callerProtocol)
    (source : TypedSource) :
    AllocationTransfers callerProtocol (readiness bridge) bindings source where
  absent := by
    intro initial reached first last context nextContext binder location admitted extended allocated frame
    exact CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge first last admitted
      extended (.none _) allocated frame
  initialized := by
    intro initial reached first last context nextContext binder location value admitted extended typed allocated frame
    exact CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge first last admitted
      extended (.some typed) allocated frame
  restore_ready := by
    intro index context nextContext binder type value extended state admitted
    exact ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr admitted.heap,
      StableRows.after_administrative (bridge.pool state) (bridge.pool (bindings.restore state))
        admitted.rows (.refl _ _)⟩
  restore_fault := by
    intro index binder type value state rows
    exact StableRows.after_administrative (bridge.pool state) (bridge.pool (bindings.restore state))
      rows (.refl _ _)

/-- The original successful post provides both raw value typing and admission
at its actual witness. Faults retain that witness's stable rows. -/
theorem expression_post {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {index : ProtectedStateTransition.Index}
    {state : callerProtocol.State index}
    (post : PostAdmission bridge context type outcome state) :
    ExpressionPost callerProtocol (readiness bridge) context type outcome state := by
  cases outcome with
  | fault _ => exact post.rows
  | value _ =>
    obtain ⟨typed, admitted⟩ := post.at_value
    exact ⟨admitted, typed⟩

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

theorem preserves_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model
      context evidence source certificate faults size) :
    ExpressionPreservesAt callerProtocol (readiness bridge) program evidence model
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) certificate
      (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees actualTyped initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, expression_post bridge post⟩

theorem reflects_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model
      context evidence source certificate faults size) :
    ExpressionReflectsAt callerProtocol (readiness bridge) program evidence model
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) certificate
      (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees actualTyped initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, expression_post bridge post⟩
end Expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
