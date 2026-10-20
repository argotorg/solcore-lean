import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews

/-! A lambda body cannot also be the complete declaration root list of a
successfully checked source forest. This distinguishes registry entry kinds. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic

theorem method_graph {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body) :
    OccurrenceGraphClosed body.source := by
  cases instantiates with
  | intro _ _ _ _ definitionMember _ _ _ _ sourceEq _ _ =>
    obtain ⟨retained, member, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨_, _, _, _, _, _, _, success⟩ := Frontend.checkProgram_success_method_body checked member
    rw [sourceEq]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters substitution
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed success)

theorem lambda_header {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : Substitution} {function : Dynamic.Closure} {contract : Contract}
    (origin : CallableLedger.LambdaOrigin plan owner id active function contract) :
    ∃ actual node, ContainsExpression function.source actual node ∧
      node.form = .lambda function.parameters function.resultType function.body := by
  cases origin with
  | original prepared receipt _ _ source parameters result body =>
    refine ⟨id, receipt.node, ?_, ?_⟩
    · rw [source]
      exact CallContractCertificates.expression_sound receipt.selected
    · rw [parameters, result, body]
      exact receipt.form
  | @contextual sidecar contextual _ _ prepared receipt _ _ source parameters result body =>
    refine ⟨id, receipt.node.applySubstitution contextual.substitution, ?_, ?_⟩
    · rw [source]
      exact FlexibleSubstitution.ContainsExpression.applySubstitution _
        (CallContractCertificates.expression_sound receipt.selected)
    · simp only [ExpressionNode.applySubstitution, receipt.form,
        ExpressionForm.applySubstitution, parameters, result, body]
  | applied recipe _ _ _ _ _ source parameters result body =>
    refine ⟨recipe.read.entry.view.principal.initializer,
      SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution), ?_, ?_⟩
    · rw [source]
      exact lookupExpression?_sound recipe.source_node
    · rw [parameters, result, body]
      exact recipe.source_node_form

  | independentApplied recipe _ _ _ _ _ paired header =>
    obtain ⟨node, found, _, form⟩ := (CallableIndependentSourceViews.of_pair paired).expression
      recipe.source_node
    exact ⟨_, node, lookupExpression?_sound found,
      form.trans (recipe.source_node_form.trans (recipe.header.trans header.symm))⟩

theorem root_exists {source : TypedSource} {id : NodeId}
    (reachable : Reachable source id) : ∃ root, root ∈ source.roots := by
  induction reachable with
  | root member => exact ⟨_, member⟩
  | child _ _ ih => exact ih

theorem statement_root_member {nodes : List NodeId} {ids : List StatementId}
    (roots : StatementRoots nodes ids) {root : NodeId} (member : root ∈ nodes) :
    ∃ id ∈ ids, root = .statement id := by
  induction roots with
  | nil => cases member
  | cons rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, by simp, rfl⟩
    · obtain ⟨id, member, same⟩ := ih member
      exact ⟨id, by simp [member], same⟩

theorem lambda_ne_whole_body {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : Ty}
    {body : List StatementId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    (roots : StatementRoots source.roots body) : False := by
  obtain ⟨root, member⟩ := root_exists (closed.allNodesReachable _ contains.1)
  obtain ⟨statement, inBody, rfl⟩ := statement_root_member roots member
  apply closed.rootsHaveNoParent member (parent := .expression id)
  refine ⟨.expression node, ⟨contains.1, congrArg NodeId.expression contains.2⟩, ?_⟩
  simp [nodeChildIds, Node.references, form, ExpressionForm.references, inBody]

theorem anonymous_ne_whole_body {program : CheckedProgram} {plan : Plan}
    {table : SourceCoreStageCodebook.Table} {function : Dynamic.Closure}
    {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected program plan table function scope)
    (closed : OccurrenceGraphClosed function.source)
    (roots : StatementRoots function.source.roots function.body) : False := by
  cases selected with
  | lambda _ _ _ _ origin | applied _ _ _ _ _ _ _ _ _ origin =>
    obtain ⟨id, node, contains, form⟩ := lambda_header origin
    exact lambda_ne_whole_body closed contains form roots

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
