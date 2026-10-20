import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState

/-! Expression leaves in ordinary materialized bodies retain their own actual
compiler certificate and original typing derivation. Numeric evidence is
recovered from the runtime context and its covering dictionary at that leaf. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState
open Staging.Recursive.Lifting (embed)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

def StaticCertificate (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (reasonAt : ExpressionId → Word) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ fuel solved node, source.lookupExpression? id = some node ∧
    ExpressionHasType source context id node.type ∧
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel (.initial checked)
      source context solved reasonAt scope id lowered

abbrev Certificate (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  StaticCertificate checked invocation.source reasonAt context scope id lowered

include extension uninitialized semantic selectedBodies in
theorem expression {context scope id lowered node}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (certificate : Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt) context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node) :
    ∃ size outcome after value finalStore,
      Staging.Recursive.Size.Expression program registry size invocation context entry.environment entry.heap id (embed outcome) after ∧
      Evaluates entry.actual entry.store (lowered.expression.rename entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model entry.mapping entry.world node.type lowered.type faults (embed outcome) value ∧
      GenericHeap.CellHeapRepresents cells entry.mapping entry.world after finalStore ∧
      AdministrativePreserved entry.mapping entry.store entry.mapping finalStore ∧
      CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store entry.mapping entry.world after finalStore ∧
      (∀ sourceValue, outcome = .value sourceValue → Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after sourceValue node.type) ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context entry.environment entry.heap id otherOutcome otherHeap →
        otherOutcome = embed outcome ∧ otherHeap = after := by
  obtain ⟨fuel,solved,other,otherFound,typed,certificate⟩ := certificate
  cases Option.some.inj (otherFound.symm.trans found)
  obtain ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,_,effect,determines⟩ :=
    CellAwareReadProductCompletion.completes functions extension GeneralizedLocalDescriptorHeap.ordinary_cells
      (uninitialized context fuel) semantic entry.runtime.graph.nodeOccurrencesUnique selectedBodies entry.runtime entry.covers
      certificate found typed entry.environments entry.heaps entry.heapTyped entry.locals entry.agrees
  refine ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,effect,?_,determines⟩
  intro sourceValue same
  subst outcome
  have result := Staging.Recursive.SelectedPreservation.expression selectedBodies
    entry.runtime entry.covers entry.locals entry.heapTyped typed trace
  exact ⟨result.heap_typed,result.value_typed sourceValue rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
