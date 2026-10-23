import Solcore.SourceSemantics.SourceCompiledActualCallGraphClosure
import Solcore.SourceSemantics.SourceInferenceActualNodeShapeSuffix
import Solcore.SourceSemantics.SourceInferenceShapeInverseClosure
import Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
import Solcore.SourceSemantics.SourceCompiledLocalLexicalSubtree
import Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins
import Solcore.SourceSemantics.SourceCompiledInitializerReadCutoff

/-! Actual discovery bindings retain their original initialized checker call.
The enclosing local allocator is taken from that same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Return-type unification preserves the actual node table selected for
finalization, so a reached child keeps its syntax in that same evidence source. -/
theorem actualCall_final_nodeShapes (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    NodeShapesPreserved call.final.nodes (evidenceSource selected).nodes := by
  have shapes := CallOccurrence.finalNodeShapes here
  change NodeShapesPreserved call.final.nodes selected.body.body.state.nodes at shapes
  change NodeShapesPreserved call.final.nodes selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact shapes

/-- Rigid and flexible finalization retain both the actual owner ID and its
initializer ID. The recovered call is reached by this same body inference. -/
theorem local_lambda_actual_origin (selected : BodySelection compiled row fuel)
    {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    ∃ rawBinder : TypedBinder,
      rawBinder.id = binding.binder.id ∧
      ActualGeneralization.Origin selected.inferenceCall rawBinder binding.initializer := by
  obtain ⟨statement, statementMember, statementForm⟩ :=
    localLambdaBindings_statement_origin member
  rw [selected.source] at statementMember
  obtain ⟨finalized, finalBinder, finalMember, _, finalForm, rigid⟩ :=
    SourceCompiledLocalGeneralizationEvents.specialized_initialized_statement_original
      statementMember statementForm
  rw [selected.body.resources.source_eq] at finalMember
  obtain ⟨raw, rawBinder, rawMember, _, rawForm, flexible⟩ :=
    SourceCompiledLocalGeneralizationEvents.solved_initialized_statement_original finalMember finalForm
  have initialized : ({binder := rawBinder, initializer := .expression binding.initializer} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement raw, rawMember, ?_⟩
    change _ ∈ statementInitializedLetBindings raw.form
    rw [rawForm]
    exact List.mem_singleton_self _
  obtain ⟨initializer, initSame, actual⟩ := selected.actual_initialized_origin initialized
  have sameInitializer : initializer = binding.initializer :=
    (NodeId.expression.inj initSame).symm
  refine ⟨rawBinder, ?_, sameInitializer ▸ actual⟩
  have rigidId := congrArg TypedBinder.id rigid
  have flexibleId := congrArg TypedBinder.id flexible
  exact flexibleId.trans rigidId

/-- Recover the earlier syntax of an actual discovered lambda node. Both
substitutions apply to the retained raw record; only its shape is required at
the earlier checkpoint. -/
theorem local_lambda_node_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node} {node : Node}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : node ∈ nodes) :
    ∃ earlier ∈ before.nodes, ∃ raw : Node,
      SameNodeShape earlier raw ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (raw.applySubstitution selected.body.finalized.substitution) = node := by
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
    graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist accepted member
  have contains : ContainsNode row.function.typedBody node.id node :=
    ⟨localLambdaBodyNodes_members accepted member, rfl⟩
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
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds]
      using result
  obtain ⟨earlier, earlierMember, shape⟩ :=
    SourceInferenceSoundness.NodeShapesPreserved.node_inverse preserved beforeClosed present unique
      rawContains.1 (.inr (by simpa only [rawContains.2] using rawPath))
  refine ⟨earlier, earlierMember, raw, shape, ?_⟩
  rw [rawSame]
  exact finalSame

/-- Coercion metadata does not affect the local target recovered at the
initializer checkpoint. -/
theorem local_lambda_read_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    ∃ earlier : ExpressionNode, Node.expression earlier ∈ before.nodes ∧
      earlier.id = read.id ∧ earlier.form = .reference name (.local binder) := by
  obtain ⟨earlier, earlierMember, raw, shape, same⟩ :=
    selected.local_lambda_node_before_shape preserved beforeClosed present accepted member
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


/-- The same statement initializer supplies its actual read cutoff. The graph
and shape arguments are filled by the actual-prefix and actual-suffix producers
in the final connection. -/
private theorem statement_read_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result))
    (sameBinder : receipt.binding.1.id = localInstance.binding.binder.id)
    (sameInitializer : receipt.value.id = localInstance.binding.initializer)
    (preserved : NodeShapesPreserved receipt.ready.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (receipt.ready.toTypedSource []))
    (present : NodeId.expression receipt.value.id ∈ nodeIds (receipt.ready.toTypedSource []))
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have root : NodeId.expression localInstance.binding.initializer ∈
      nodeIds (receipt.ready.toTypedSource []) := sameInitializer ▸ present
  obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
    selected.local_lambda_read_before_shape preserved closed root accepted member form
  have before := selected.statement_initializer_read_cutoff checked receipt here
    earlier earlierMember name binder earlierForm
  rw [← sameBinder]
  exact before

private theorem header_read_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2))
    (sameBinder : receipt.binding.1.id = localInstance.binding.binder.id)
    (sameInitializer : receipt.value.id = localInstance.binding.initializer)
    (preserved : NodeShapesPreserved receipt.ready.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (receipt.ready.toTypedSource []))
    (present : NodeId.expression receipt.value.id ∈ nodeIds (receipt.ready.toTypedSource []))
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have root : NodeId.expression localInstance.binding.initializer ∈
      nodeIds (receipt.ready.toTypedSource []) := sameInitializer ▸ present
  obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
    selected.local_lambda_read_before_shape preserved closed root accepted member form
  have before := selected.header_initializer_read_cutoff checked receipt here
    earlier earlierMember name binder earlierForm
  rw [← sameBinder]
  exact before


private theorem annotation_expected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

/-- An actual direct lexical body can only read a binder allocated before its
own declaration. The initialized owner and every graph/cutoff fact are derived
from this same checked body's real recursive path. -/
theorem local_lambda_read_binder_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {nodes : List Node} {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  cases actual with
  | statement receipt here =>
      have graph := selected.statement_initializer_graph receipt here
      have step := ChildStep.statement_initializer here.accepted receipt.form rfl
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      exact statement_read_lt selected checked receipt here same initializerEq.symm shapes graph.1
        (graph.2 (List.mem_singleton_self _)) accepted member form
  | header receipt here =>
      have graph := selected.header_initializer_graph receipt here
      have step := ChildStep.forItem_initializer here.accepted receipt.form
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      exact header_read_lt selected checked receipt here same initializerEq.symm shapes graph.1
        (graph.2 (List.mem_singleton_self _)) accepted member form

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
