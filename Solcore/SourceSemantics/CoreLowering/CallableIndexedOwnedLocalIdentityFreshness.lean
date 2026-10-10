import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix

/-! Genuine whole-source identity ownership supplies the two static freshness
facts used by a lambda Site shell. Both conclusions keep the same source and
actual occurrence; native typing and runtime graph validity are not inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
open Core Frontend SourceInference

private def nodeBinders : Node → List TypedBinder
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
          | .letDecl binder _ => some binder
          | _ => none
      | .matchWith resolution => resolution.cases.flatMap fun arm =>
          SourceCoreDataPlaces.patternBinders arm.pattern
      | _ => []

private def nodeHiddenIds : Node → List Resolved.LocalId
  | .statement node => match node.form with
      | .matchWith resolution => [resolution.hiddenScrutinee]
      | _ => []
  | .expression _ => []

private theorem declared_binders (source : TypedSource) :
    SourceCoreDataPlaces.declaredBinders source = source.inputs ++ source.nodes.flatMap nodeBinders := by
  unfold SourceCoreDataPlaces.declaredBinders
  apply congrArg (fun selected : Node → List TypedBinder => source.inputs ++ source.nodes.flatMap selected)
  funext node
  cases node <;> rfl

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      MatchPatternInstruction.binderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;>
      simp [SourceCoreDataPlaces.instructionBinders, MatchPatternInstruction.binderIds] at ih ⊢ <;>
      exact ih

private theorem pattern_ids (pattern : TypedMatchPattern) :
    (SourceCoreDataPlaces.patternBinders pattern).map (·.id) = pattern.binderIds := by
  cases resolution : pattern.resolution <;>
    simp only [SourceCoreDataPlaces.patternBinders, TypedMatchPattern.binderIds, resolution]
  all_goals try rfl
  all_goals exact instruction_ids _

private theorem for_ids (items : List ForItemForm) :
    ((items.filterMap fun | .letDecl binder _ => some binder | _ => none).map (·.id)) =
      items.flatMap ForItemForm.definedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp [ForItemForm.definedLocalIds, ih]

private theorem node_inventory (node : Node) :
    ((nodeBinders node).map (·.id) ++ nodeHiddenIds node).Perm node.definedLocalIds := by
  cases node with
  | expression expression =>
    cases form : expression.form <;>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds, form,
        ExpressionForm.definedLocalIds, List.map_nil, List.append_nil] <;>
      exact List.Perm.refl _
  | statement statement =>
    cases form : statement.form with
    | matchWith resolution =>
      simpa only [nodeBinders, nodeHiddenIds, Node.definedLocalIds,
        form, StatementForm.definedLocalIds, List.map_flatMap, pattern_ids] using
        List.perm_append_singleton resolution.hiddenScrutinee
          (resolution.cases.flatMap fun arm => arm.pattern.binderIds)
    | forLoop initial condition post body =>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds,
        form, StatementForm.definedLocalIds, List.append_nil, for_ids, List.flatMap_append]
      exact List.Perm.refl _
    | _ =>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds, form,
        StatementForm.definedLocalIds, List.map_nil, List.map_cons, List.append_nil] <;>
      exact List.Perm.refl _

private theorem nodes_inventory (nodes : List Node) :
    ((nodes.flatMap fun node => (nodeBinders node).map (·.id)) ++
      nodes.flatMap nodeHiddenIds).Perm (nodes.flatMap Node.definedLocalIds) := by
  induction nodes with
  | nil => exact List.Perm.refl _
  | cons node rest ih =>
    have reorder := (List.perm_append_comm_assoc
      (rest.flatMap fun node => (nodeBinders node).map (·.id))
      (nodeHiddenIds node) (rest.flatMap nodeHiddenIds)).append_left
        ((nodeBinders node).map (·.id))
    have assembled :
        (((nodeBinders node).map (·.id)) ++ (nodeHiddenIds node ++
          ((rest.flatMap fun node => (nodeBinders node).map (·.id)) ++
            rest.flatMap nodeHiddenIds))).Perm
          (node.definedLocalIds ++ rest.flatMap Node.definedLocalIds) := by
      simpa only [List.append_assoc] using (node_inventory node).append ih
    simpa only [List.flatMap_cons, List.append_assoc] using reorder.trans assembled

private theorem source_inventory (source : TypedSource) :
    (((SourceCoreDataPlaces.declaredBinders source).map (·.id)) ++
      source.nodes.flatMap nodeHiddenIds).Perm source.definedLocalIds := by
  have assembled := (nodes_inventory source.nodes).append_left (source.inputs.map (·.id))
  rw [declared_binders, List.map_append, List.map_flatMap]
  simpa only [TypedSource.definedLocalIds, List.append_assoc] using assembled

/-- The actual lambda parameters are disjoint from declaration inputs in the
same globally unique source inventory. -/
theorem lambda_parameter_not_input {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (ownership : LocalIdentityOwnership source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    {binder : TypedBinder} (member : binder ∈ parameters) :
    binder.id ∉ source.inputs.map (·.id) := by
  have unique : source.definedLocalIds.Nodup := by
    simpa only [typedSourceDefinedLocalIds_eq_carrier] using ownership.unique
  have separates := (List.nodup_append.mp unique).2.2
  have defined : binder.id ∈ source.nodes.flatMap Node.definedLocalIds := by
    apply List.mem_flatMap.mpr
    refine ⟨.expression node, contains.1, ?_⟩
    simpa only [Node.definedLocalIds, form, ExpressionForm.definedLocalIds] using
      List.mem_map.mpr ⟨binder, member, rfl⟩
  intro input
  exact separates binder.id input binder.id defined rfl

/-- The compiler's input-kind test is false for every actual lambda parameter. -/
theorem lambda_parameter_kind {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (ownership : LocalIdentityOwnership source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    {binder : TypedBinder} (member : binder ∈ parameters) :
    source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  apply List.any_eq_false.mpr
  intro input present same
  have sameId : input.id = binder.id := of_decide_eq_true same
  exact lambda_parameter_not_input ownership contains form member
    (List.mem_map.mpr ⟨input, present, sameId⟩)

/-- The same accepted parameter receipt transports ordinary kinds to the
lowered parameter vector; no alternate binder inventory is introduced. -/
theorem lowered_parameter_kinds
    {values : SourceCoreCompatibleValues.Context}
    {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreBasic.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative)
    {id : ExpressionId} {node : ExpressionNode}
    (ownership : LocalIdentityOwnership function.source)
    (contains : ContainsExpression function.source id node)
    (form : node.form = .lambda function.parameters function.resultType function.body) :
    ∀ binding ∈ code.receipt.loweredParameters,
      function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
  intro binding member
  apply lambda_parameter_kind ownership contains form
  rw [CallableIndexedLambdaEntryPrefix.parameters code]
  exact List.mem_map.mpr ⟨binding, member, rfl⟩

/-- The globally unique inventory separates actual match-hidden identities
from every ordinary declaration, including inputs and pattern binders. -/
theorem match_hidden_fresh {source : TypedSource}
    (ownership : LocalIdentityOwnership source) :
    GenericImperativeMatch.MatchHiddenFresh source := by
  have unique : source.definedLocalIds.Nodup := by
    simpa only [typedSourceDefinedLocalIds_eq_carrier] using ownership.unique
  have reordered := (source_inventory source).symm.nodup unique
  have separates := (List.nodup_append.mp reordered).2.2
  intro id node resolution found form declared
  have hidden : resolution.hiddenScrutinee ∈ source.nodes.flatMap nodeHiddenIds := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement node, (lookupStatement?_sound found).1, ?_⟩
    simp only [nodeHiddenIds, form, List.mem_singleton]
  exact separates resolution.hiddenScrutinee declared resolution.hiddenScrutinee hidden rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
