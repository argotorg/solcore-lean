import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
import Solcore.SourceSemantics.SourceCompiledBodySelection

/-! A real cached body uses the same flexible finalizer and rigid application
when a discovered lambda record is recovered at an earlier initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist CoreLowering.GeneralizedLocalLexicalSubtree
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Recover a complete original record from a real specialized lambda body.
The earlier closure premise is for this actual preserved initializer subtree. -/
theorem local_lambda_node_before (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node} {node : Node}
    (preserved : RawSubtreePreserved before
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : node ∈ nodes) :
    ∃ original, original ∈ before.nodes ∧ original.id = node.id ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (original.applySubstitution selected.body.finalized.substitution) = node := by
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := body_node_descends graph.wellFormed.nodeOccurrencesUnique
    graph.wellFormed.childEdgesExist accepted member
  have contains : ContainsNode row.function.typedBody node.id node :=
    ⟨localLambdaBodyNodes_members accepted member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨original, originalContains, originalSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds]
      using result
  refine ⟨original, preserved.node_inverse beforeClosed present unique originalContains.1
    (.inr (by simpa only [originalContains.2] using rawPath)),
    originalContains.2, ?_⟩
  rw [originalSame]
  exact finalSame

/-- The actual local reference keeps its target binder and identity when it is
recovered from the earlier initializer table. Coercion metadata is preserved
exactly by the two source substitutions. -/
theorem local_lambda_read_before (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : RawSubtreePreserved before
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    ∃ original : ExpressionNode, Node.expression original ∈ before.nodes ∧
      original.id = read.id ∧ original.form = .reference name (.local binder) ∧
      original.requirements = read.requirements ∧
      original.localSchemeInstantiationStart = read.localSchemeInstantiationStart := by
  obtain ⟨raw, rawMember, _, same⟩ :=
    selected.local_lambda_node_before preserved beforeClosed present accepted member
  have mapped : Node.expression read ∈
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (before.applySubstitution selected.body.finalized.substitution)).nodes :=
    List.mem_map.mpr ⟨raw.applySubstitution selected.body.finalized.substitution,
      List.mem_map.mpr ⟨raw, rawMember, rfl⟩, same⟩
  obtain ⟨finalized, finalMember, finalId, finalForm, finalRequirements, finalStart⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original mapped form
  obtain ⟨original, originalMember, originalId, originalForm, originalRequirements, originalStart⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  exact ⟨original, originalMember, originalId.trans finalId, originalForm,
    originalRequirements.trans finalRequirements, originalStart.trans finalStart⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
