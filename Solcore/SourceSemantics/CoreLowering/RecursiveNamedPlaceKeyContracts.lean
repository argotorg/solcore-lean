import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts

/-! Measured ordered keys keep the actual projection derivation. Member steps
add source cost without evaluating an expression; index steps retain source
order and repetitions. Native bundle sizes are independent of these source
sizes. The adapters only restrict pointwise expression meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open DataPlaceKeyOrder

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}

/-- Removing member-only steps cannot increase the actual source size. -/
theorem projections_values {size : Nat} {projections : List PlaceProjection} {evaluated : List Dynamic.EvaluatedProjection}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) :
    ∃ values vectorSize, Values projections values evaluated ∧
      SourceExecutionSize.ExpressionsEvaluate program vectorSize context evidence source environment before (sourceKeys projections) values after ∧
      vectorSize ≤ size := by
  induction projections generalizing size before evaluated with
  | nil => cases trace; exact ⟨[], _, .nil, .nil, Nat.le_refl _⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | member tail =>
        obtain ⟨values, vectorSize, shaped, executed, bound⟩ := ih tail
        exact ⟨values, vectorSize, .member shaped, executed,
          Nat.le_trans bound (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp)))⟩
    | index key =>
      cases trace with
      | index head tail =>
        obtain ⟨values, vectorSize, shaped, executed, bound⟩ := ih tail
        refine ⟨_ :: values, _, .index shaped, .cons head executed, ?_⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *
        omega

theorem projections_fault {size : Nat} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) :
    ∃ vectorSize, SourceExecutionSize.ExpressionsFault program vectorSize context evidence source environment before (sourceKeys projections) reason after ∧
      vectorSize ≤ size := by
  induction projections generalizing size before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | memberTail failed =>
        obtain ⟨vectorSize, failed, bound⟩ := ih failed
        exact ⟨vectorSize, failed, Nat.le_trans bound
          (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp)))⟩
    | index key =>
      cases trace with
      | indexHead failed => exact ⟨_, .head failed, Nat.le_refl _⟩
      | indexTail head failed =>
        obtain ⟨vectorSize, failed, bound⟩ := ih failed
        refine ⟨_, .tail head failed, ?_⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *
        omega

/-- Reflection reconstructs a source size; it makes no comparison to Core cost. -/
theorem values_projections {size : Nat} {projections : List PlaceProjection} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before (sourceKeys projections) values after) :
    ∃ sourceSize evaluated, Values projections values evaluated ∧
      SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before projections evaluated after := by
  induction projections generalizing size before values with
  | nil => cases trace; exact ⟨_, [], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      obtain ⟨sourceSize, evaluated, shaped, executed⟩ := ih trace
      exact ⟨_, _, .member shaped, .member executed⟩
    | index key =>
      cases trace with
      | cons head tail =>
        obtain ⟨sourceSize, evaluated, shaped, executed⟩ := ih tail
        exact ⟨_, _, .index shaped, .index head executed⟩

theorem fault_projections {size : Nat} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionsFault program size context evidence source environment before (sourceKeys projections) reason after) :
    ∃ sourceSize, SourceExecutionSize.SourceProjectionsFault program sourceSize context evidence source environment before projections reason after := by
  induction projections generalizing size before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      obtain ⟨sourceSize, failed⟩ := ih trace
      exact ⟨_, .memberTail failed⟩
    | index key =>
      cases trace with
      | head failed => exact ⟨_, .indexHead failed⟩
      | tail head failed =>
        obtain ⟨sourceSize, failed⟩ := ih failed
        exact ⟨_, .indexTail head failed⟩

inductive OutcomeAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (projections : List PlaceProjection) : DataExpressionSequence.Outcome → Dynamic.Heap → Prop where
  | values {values evaluated after} (shaped : Values projections values evaluated)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) :
      OutcomeAt program size context evidence source environment before projections (.ok values) after
  | fault {reason after} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) :
      OutcomeAt program size context evidence source environment before projections (.error reason) after

theorem OutcomeAt.sound {size projections outcome}
    (trace : OutcomeAt program size context evidence source environment before projections outcome after) :
    OutcomeTrace program context evidence source environment before projections outcome after := by
  cases trace with
  | values shaped trace => exact .values shaped trace.sound
  | fault trace => exact .fault trace.sound

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {entry : ProtectedExpressionMeaning.Entry}

/-- The higher-level named contract supplies the same measured source child. -/
theorem preserves_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry) :
    ProtectedDataExpressionSequence.ExpressionPreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed installed trace
  apply meaning generated found environments heaps locals agrees typed installed
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

theorem reflects_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults entry) :
    ProtectedDataExpressionSequence.ExpressionReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning generated found environments heaps locals agrees typed installed evaluated
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, rest⟩
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
