import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics

/-! The real child compiler and retained issuer supply materialized body scope
and diagnostics. Original source identities survive the actual substitution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

/-- The instantiated body selects its own recursive Source scope from the
actual descriptor and compiler preparation, without a lexical History. -/
theorem Materialization.scope_at (material : Materialization compiled mapping world function) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan material.code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar material.code.active function) := by
  have receipt := material.source_receipt
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at receipt
  exact CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope material.code receipt material.unique

theorem Materialization.original_source (material : Materialization compiled mapping world function) :
    ∃ original : SourceSpecialization.SpecializedFunction,
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan material.inputs.current.owner = .ok original ∧
      material.descriptor.source = original.function.typedBody ∧
      function.source = original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution := by
  obtain ⟨original, selected, same, _active, source⟩ :=
    LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
  refine ⟨original, ?_, ?_, material.source.trans source⟩
  · simpa only [material.indexed.plan, ← material.indexed.owner] using selected
  · exact material.descriptorSource.trans (material.candidateSource.symm.trans same.symm)

private theorem reference_original {substitution : TypeSystem.Substitution} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId}
    (form : (node.applySubstitution substitution).form = .reference name (.local binder)) :
    node.form = .reference name (.local binder) := by
  cases original : node.form <;>
    simp_all [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution]
  rename_i originalName resolution
  cases resolution <;> simp_all [ReferenceResolution.applySubstitution]


/-- A body read uses its original issued token in the actual public receiving
inventory. No diagnostic premise is supplied by the caller of the body. -/
theorem Materialization.uninitialized (material : Materialization compiled mapping world function)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (material.code.reasonAt id) := by
  obtain ⟨original, selected, descriptorSource, source⟩ := material.original_source
  have unique : NodeOccurrencesUnique original.function.typedBody := descriptorSource ▸ material.descriptorUnique
  have contained : ContainsExpression
      (original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution) id node :=
    source ▸ lookupExpression?_sound found
  have nodeContained : ContainsNode
      (original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution)
      (.expression id) (.expression node) := ⟨contained.1, congrArg NodeId.expression contained.2⟩
  obtain ⟨originalNode, originalContained, transformed⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution nodeContained
  cases originalNode with
  | statement originalNode => cases transformed
  | expression originalNode =>
    have same : originalNode.applySubstitution material.packet.original.emission.prepared.substitution = node :=
      Node.expression.inj transformed
    have originalForm := reference_original (same.symm ▸ form)
    have originalContains : ContainsExpression original.function.typedBody id originalNode :=
      ⟨originalContained.1, NodeId.expression.inj originalContained.2⟩
    obtain ⟨issued, present, callback, own, ownFound⟩ := material.issuer
    obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
      CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
        selected unique originalContains originalForm ownFound
    apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
    apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
      (by simpa only [material.reasons, callback, token] using decoded)
    exact .readUninitialized location binder

/-- Every actual body leaf uses its original issued token. -/
theorem Materialization.body_uninitialized (material : Materialization compiled mapping world function)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (material.code.reasonAt id) :=
  material.uninitialized receiver found form location

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
