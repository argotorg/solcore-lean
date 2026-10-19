import Solcore.SourceSemantics.CoreLowering.CellAwareReadEffects
import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource

/-! Both directions of accepted ordinary reads preserve the real mixed heap.
Native completion is assembled from the selected cell and literal code; the
independent Source trace is then identified by local read uniqueness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

theorem Certificate.scoped_preserves_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  obtain ⟨value, finalStore, evaluation⟩ := certificate.cell_native_terminates functions extension ordinaryCells
    binding environments heaps heapTyped locals agrees
  obtain ⟨actualOutcome, actualHeap, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
      environments heaps heapTyped locals agrees uninitialized evaluation
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have absent := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup read certificate.monomorphic
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read absent sourceTrace trace
  exact ⟨value, finalStore, evaluation, represented, finalHeaps, frame, metadata, effect⟩

theorem Certificate.scoped_reflects_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  exact certificate.scoped_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
    environments heaps heapTyped locals agrees uninitialized evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
