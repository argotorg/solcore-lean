import Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder

/-! Local reads on any canonical path beneath an actual initializer existed
before that declaration's local identity was allocated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Invert any canonical descendant of the initializer, including paths into
nested lambda bodies that the direct lexical collector intentionally skips. -/
theorem local_lambda_descendant_node_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId} {node : Node}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (member : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id) :
    ∃ earlier ∈ before.nodes, ∃ raw : Node, SameNodeShape earlier raw ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (raw.applySubstitution selected.body.finalized.substitution) = node := by
  have contains : ContainsNode row.function.typedBody node.id node := ⟨member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨raw, rawContains, rawSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique (evidenceSource selected) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds] using result
  obtain ⟨earlier, earlierMember, shape⟩ :=
    SourceInferenceSoundness.NodeShapesPreserved.node_inverse preserved closed present unique
      rawContains.1 (.inr (by simpa only [rawContains.2] using rawPath))
  refine ⟨earlier, earlierMember, raw, shape, ?_⟩
  rw [rawSame]
  exact finalSame

/-- Coercion metadata does not affect the local target recovered at the
initializer checkpoint. -/
theorem local_lambda_descendant_read_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (member : Node.expression read ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) (.expression read.id))
    (form : read.form = .reference name (.local binder)) :
    ∃ earlier : ExpressionNode, Node.expression earlier ∈ before.nodes ∧
      earlier.id = read.id ∧ earlier.form = .reference name (.local binder) := by
  obtain ⟨earlier, earlierMember, raw, shape, same⟩ :=
    selected.local_lambda_descendant_node_before_shape preserved beforeClosed present member path
  have mapped : Node.expression read ∈
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (({owner := before.owner, inputs := [], roots := [], nodes := [raw]} : TypedSource).applySubstitution selected.body.finalized.substitution)).nodes :=
    List.mem_map.mpr ⟨raw.applySubstitution selected.body.finalized.substitution,
      List.mem_map.mpr ⟨raw, List.mem_singleton_self _, rfl⟩, same⟩
  obtain ⟨finalized, finalMember, finalId, finalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original mapped form
  obtain ⟨original, originalMember, originalId, originalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  have rawEq : Node.expression original = raw := List.mem_singleton.mp originalMember
  rw [← rawEq] at shape
  cases earlier with
  | statement _ => cases shape
  | expression earlier =>
    exact ⟨earlier, earlierMember, shape.1.trans (originalId.trans finalId),
      shape.2.trans originalForm⟩


private theorem annotation_expected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

/-- Actual retained reads need only their canonical path from the initializer;
no membership in a separately collected lexical-body table is required. -/
theorem local_lambda_descendant_read_binder_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : Node.expression read ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody
      (.expression localInstance.binding.initializer) (.expression read.id))
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  have actualPath := path
  rw [initializerEq] at actualPath
  cases actual with
  | statement receipt here =>
      have graph := selected.statement_initializer_graph receipt here
      have step := ChildStep.statement_initializer here.accepted receipt.form rfl
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
        selected.local_lambda_descendant_read_before_shape
          (before := receipt.ready.toTypedSource []) shapes graph.1
          (graph.2 (List.mem_singleton_self _)) member actualPath form
      have before := selected.statement_initializer_read_cutoff checked receipt here
        earlier earlierMember name binder earlierForm
      rw [← same]
      exact before
  | header receipt here =>
      have graph := selected.header_initializer_graph receipt here
      have step := ChildStep.forItem_initializer here.accepted receipt.form
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
        selected.local_lambda_descendant_read_before_shape
          (before := receipt.ready.toTypedSource []) shapes graph.1
          (graph.2 (List.mem_singleton_self _)) member actualPath form
      have before := selected.header_initializer_read_cutoff checked receipt here
        earlier earlierMember name binder earlierForm
      rw [← same]
      exact before

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
