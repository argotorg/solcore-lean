import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition

/-! Exact-sized bridges between the recursive expression contract and the
protected ordered sequence contract. Both wrappers retain the original source
derivation; conversion preserves the concrete reached-state witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.SequenceBridge
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
universe u v

theorem source_trace {program size context evidence source environment before id outcome after}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ProtectedDataExpressionSequence.ExpressionTraceAt program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

theorem call_trace {program size context evidence source environment before id outcome after}
    (trace : ProtectedDataExpressionSequence.ExpressionTraceAt program size context evidence source environment before id outcome after) :
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat}

theorem preserves_at
    (meaning : PreservesAt protocol model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt protocol size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  exact meaning certified found environments heaps locals agrees typed initial (call_trace trace)

theorem preserves_at_inv
    (meaning : ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt protocol size model program context evidence source certificate faults) :
    PreservesAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  exact meaning certified found environments heaps locals agrees typed initial (source_trace trace)

theorem reflects_at
    (meaning : ReflectsAt protocol model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt protocol size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, source_trace trace, rest⟩

theorem reflects_at_inv
    (meaning : ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt protocol size model program context evidence source certificate faults) :
    ReflectsAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, call_trace trace, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.SequenceBridge
