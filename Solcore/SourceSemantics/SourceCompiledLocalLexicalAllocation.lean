import Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder
import Solcore.SourceSemantics.SourceCompiledInitializerAllocationBounds

/-! Initialized owners inside a discovered lexical body were recorded before
its enclosing declaration. The actual ready graph retains their full binder
record, and the same local allocator bounds their stable identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
open LocalGeneralizationBoundaries
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Invert any canonical descendant of the initializer, including paths into
nested lambda bodies that the direct lexical collector intentionally skips. -/
private theorem node_before_shape (selected : BodySelection compiled row fuel)
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

/-- The complete raw initialized binding is recovered at the earlier table;
only node syntax, rather than expression typing metadata, must be preserved. -/
theorem local_lambda_initialized_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId} {node : Node}
    {nested : InitializedLetBinding}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    ∃ original ∈ initializedLetBindings before,
      StructuralSubstitution.applyInitializedLetBinding row.parameterSubstitution
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original) = nested := by
  have localMember := member
  simp only [initializedLetBindings, List.flatMap_singleton] at localMember
  obtain ⟨earlier, earlierMember, rawNode, shape, same⟩ :=
    node_before_shape selected preserved closed present nodeMember path
  have singleton : nested ∈ initializedLetBindings
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (({before with nodes := [rawNode]} : TypedSource).applySubstitution selected.body.finalized.substitution)) := by
    simpa only [SourceSpecialization.applyTypedSource, TypedSource.applySubstitution,
      List.map_singleton, initializedLetBindings, List.flatMap_singleton, same] using localMember
  change nested ∈ initializedLetBindings
    (StructuralSubstitution.applyTypedSource row.parameterSubstitution
      (({before with nodes := [rawNode]} : TypedSource).applySubstitution
        selected.body.finalized.substitution)) at singleton
  rw [StructuralSubstitution.initializedLetBindings_applyTypedSource,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at singleton
  obtain ⟨finalized, finalMember, finalSame⟩ := List.mem_map.mp singleton
  obtain ⟨original, originalMember, originalSame⟩ := List.mem_map.mp finalMember
  refine ⟨original, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨earlier, earlierMember, ?_⟩
    cases earlier with
    | expression expression =>
      cases rawNode with
      | expression rawExpression => cases originalMember
      | statement rawStatement => cases shape
    | statement statement =>
      cases rawNode with
      | expression rawExpression => cases shape
      | statement rawStatement =>
        change original ∈ statementInitializedLetBindings statement.form
        rw [shape.2]
        simpa only [initializedLetBindings, List.flatMap_singleton] using originalMember
  · rw [originalSame]
    exact finalSame

private theorem local_lambda_initialized_le (selected : BodySelection compiled row fuel)
    {state : State} {initializer : ExpressionId} {node : Node}
    {nested : InitializedLetBinding}
    (preserved : NodeShapesPreserved state.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (state.toTypedSource []))
    (present : NodeId.expression initializer ∈ nodeIds (state.toTypedSource []))
    (allocated : InitializedBindersAllocated state)
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    nested.binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨original, originalMember, same⟩ := selected.local_lambda_initialized_before_shape
    preserved closed present nodeMember path member
  have bound := initialized_binding_allocated allocated originalMember
  have idEq := congrArg (fun binding : InitializedLetBinding => binding.binder.id.binderIndex) same
  change original.binder.id.binderIndex = nested.binder.id.binderIndex at idEq
  exact idEq ▸ bound

private theorem annotation_expected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

/-- Both forms of initialized declaration use their exact actual ready state. -/
theorem local_lambda_initialized_binder_le
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {node : Node} {nested : InitializedLetBinding}
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression localInstance.binding.initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    nested.binder.id.binderIndex ≤ localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  have actualPath := path
  rw [initializerEq] at actualPath
  cases actual with
  | statement receipt here =>
    have graph := selected.statement_initializer_graph receipt here
    have step := ChildStep.statement_initializer here.accepted receipt.form rfl
      (annotation_expected receipt.annotationAccepted) receipt.child
    have bound := selected.local_lambda_initialized_le
      (selected.actualCall_final_nodeShapes (.child here step)) graph.1
      (graph.2 (List.mem_singleton_self _))
      (selected.statement_initializer_allocated checked receipt here) nodeMember actualPath member
    rw [← same]
    exact bound
  | header receipt here =>
    have graph := selected.header_initializer_graph receipt here
    have step := ChildStep.forItem_initializer here.accepted receipt.form
      (annotation_expected receipt.annotationAccepted) receipt.child
    have bound := selected.local_lambda_initialized_le
      (selected.actualCall_final_nodeShapes (.child here step)) graph.1
      (graph.2 (List.mem_singleton_self _))
      (selected.header_initializer_allocated checked receipt here) nodeMember actualPath member
    rw [← same]
    exact bound

private theorem item_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ item_ids).append (flatMap_sublist post _ _ item_ids)

private theorem initialized_defined {source : TypedSource} {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings source) : binding.binder.id ∈ definedLocalIds source := by
  obtain ⟨node, present, bound⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases bound
  | statement statement =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨.statement statement, present, ?_⟩
    exact (form_ids statement.form).subset (List.mem_map.mpr ⟨binding, bound, rfl⟩)

/-- A distinct initialized owner in the actual lexical body precedes its
containing declaration. Its owner declaration is derived from source identity
ownership, so different full IDs cannot hide equal local allocator indices. -/
theorem local_lambda_initialized_binder_lt
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {node : Node} {nested : InitializedLetBinding}
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression localInstance.binding.initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]})
    (different : nested.binder.id ≠ localInstance.binding.binder.id) :
    nested.binder.id.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have bound := selected.local_lambda_initialized_binder_le checked origin nodeMember path member
  have ownership : LocalIdentityOwnership row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.LocalIdentityOwnership.applyParameters row.parameterSubstitution
      selected.body.resources.local_identity_ownership
  have nestedGlobal : nested ∈ initializedLetBindings row.function.typedBody := by
    apply List.mem_flatMap.mpr
    refine ⟨node, nodeMember, ?_⟩
    simpa only [initializedLetBindings, List.flatMap_singleton] using member
  obtain ⟨statement, statementMember, statementForm⟩ :=
    localLambdaBindings_statement_origin origin.binding_member
  have targetGlobal : (⟨localInstance.binding.binder,
      .expression localInstance.binding.initializer⟩ : InitializedLetBinding) ∈
      initializedLetBindings row.function.typedBody := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement statement, statementMember, ?_⟩
    change _ ∈ statementInitializedLetBindings statement.form
    rw [statementForm]
    exact List.mem_singleton_self _
  have owners := (ownership.owned _ (initialized_defined nestedGlobal)).trans
    (ownership.owned _ (initialized_defined targetGlobal)).symm
  have indices : nested.binder.id.binderIndex ≠ localInstance.binding.binder.id.binderIndex := by
    intro equal
    apply different
    have eta (id : Resolved.LocalId) : id = ⟨id.owner, id.binderIndex⟩ := by cases id; rfl
    calc
      nested.binder.id = ⟨nested.binder.id.owner, nested.binder.id.binderIndex⟩ := eta _
      _ = ⟨localInstance.binding.binder.id.owner, localInstance.binding.binder.id.binderIndex⟩ := by rw [owners, equal]
      _ = localInstance.binding.binder.id := (eta _).symm
  omega

theorem local_lambda_direct_initialized_binder_lt
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {nodes : List Node} {nested : InitializedLetBinding}
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := nodes})
    (different : nested.binder.id ≠ localInstance.binding.binder.id) :
    nested.binder.id.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨node, nodeMember, binding⟩ := List.mem_flatMap.mp member
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
    graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist accepted nodeMember
  apply selected.local_lambda_initialized_binder_lt checked origin
    (localLambdaBodyNodes_members accepted nodeMember) path ?_ different
  simpa only [initializedLetBindings, List.flatMap_singleton] using binding

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
