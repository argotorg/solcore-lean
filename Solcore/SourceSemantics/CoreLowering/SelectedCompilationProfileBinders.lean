import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
import Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
import Solcore.SourceSemantics.SourceExecutableBinderInterfaces
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.SourceSemantics.Graph

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
open Frontend SourceInference TypeSystem CompilerProgramStaticProfile
open ExecutableBinderInterfaces

private theorem lambda_node {source : TypedSource} {initializer : ExpressionId}
    (direct : SourceSpecialization.isDirectLambdaInitializer source initializer = true) :
    ∃ node parameters result body, source.lookupExpression? initializer = some node ∧
      node.form = .lambda parameters result body := by
  unfold SourceSpecialization.isDirectLambdaInitializer at direct
  cases found : source.lookupExpression? initializer with
  | none => simp only [found, Bool.false_eq_true] at direct
  | some node =>
    cases node with
    | mk id span type actualForm requirements coercions start =>
      cases actualForm <;> simp only [found, Bool.false_eq_true] at direct
      case lambda parameters result body => exact ⟨_, parameters, result, body, rfl, rfl⟩

/-- A returned lambda occurrence cannot simultaneously initialize a local.
Both edges refer to the original complete occurrence graph. -/
theorem returned_lambda_not_initializer {source : TypedSource}
    (closed : OccurrenceGraphClosed source)
    {outer : StatementId} {outerNode node : StatementNode} {expression : ExpressionId}
    (outerFound : source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some expression))
    {binder : TypedBinder}
    (member : Node.statement node ∈ source.nodes)
    (form : node.form = .letDecl binder (some expression)) : False := by
  have returned : DirectChild source (.statement outer) (.expression expression) := by
    refine ⟨.statement outerNode, ?_, ?_⟩
    · exact ⟨(lookupStatement?_sound outerFound).1, by
        simpa only [Node.id] using congrArg NodeId.statement (lookupStatement?_sound outerFound).2⟩
    · simp only [nodeChildIds, Node.references, outerForm, StatementForm.references,
        Option.map_some, Option.toList_some, List.mem_singleton]
  have initialized : DirectChild source (.statement node.id) (.expression expression) := by
    refine ⟨.statement node, ⟨member, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, form, StatementForm.references,
      Option.map_some, Option.toList_some, List.mem_singleton]
  have sameId := NodeId.statement.inj (closed.childHasUniqueParent returned initialized)
  have nodeFound : source.lookupStatement? outer = some node :=
    lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique ⟨member, sameId.symm⟩
  have same := Option.some.inj (outerFound.symm.trans nodeFound)
  rw [← same, outerForm] at form
  cases form

private theorem mono_without_lambdas {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (lambdas : ∀ node ∈ specialized.function.typedBody.nodes, LambdaAllowed none node) :
    SourceMonomorphic specialized.function.typedBody := by
  intro binder member
  by_cases monomorphic : binder.scheme.quantified = []
  · exact monomorphic
  · obtain ⟨_, expression, _, _, direct⟩ :=
      SelectedCompilationSpecializationBinders.initialized_position accepted member monomorphic
    obtain ⟨node, parameters, result, body, found, form⟩ := lambda_node direct
    have allowed := lambdas (.expression node) (lookupExpression?_sound found).1
    simp only [LambdaAllowed, form] at allowed
    cases allowed

private theorem mono_returned_lambda {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed specialized.function.typedBody)
    {outer : StatementId} {outerNode : StatementNode} {expression : ExpressionId} {allowedNode : ExpressionNode}
    (outerFound : specialized.function.typedBody.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some expression))
    (found : specialized.function.typedBody.lookupExpression? expression = some allowedNode)
    (lambdas : ∀ node ∈ specialized.function.typedBody.nodes, LambdaAllowed (some allowedNode) node) :
    SourceMonomorphic specialized.function.typedBody := by
  intro binder member
  by_cases monomorphic : binder.scheme.quantified = []
  · exact monomorphic
  · obtain ⟨statement, initializer, present, statementForm, direct⟩ :=
      SelectedCompilationSpecializationBinders.initialized_position accepted member monomorphic
    obtain ⟨node, parameters, result, body, initializerFound, form⟩ := lambda_node direct
    have allowed := lambdas (.expression node) (lookupExpression?_sound initializerFound).1
    simp only [LambdaAllowed, form, Option.some.injEq] at allowed
    subst node
    have sameId : initializer = expression :=
      (lookupExpression?_sound initializerFound).2.symm.trans (lookupExpression?_sound found).2
    subst initializer
    exact False.elim (returned_lambda_not_initializer closed outerFound outerForm present statementForm)

private theorem item_binders_apply (substitution : ParameterSubstitution) (item : ForItemForm) :
    (SourceSpecialization.applyForItemForm substitution item).initializedLetBinders =
      item.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases item <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl

private theorem statement_binders_apply (substitution : ParameterSubstitution) (form : StatementForm) :
    (SourceSpecialization.applyStatementForm substitution form).initializedLetBinders =
      form.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases form <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl
  case forLoop initializer condition post body =>
    simp only [SourceSpecialization.applyStatementForm, StatementForm.initializedLetBinders,
      List.flatMap_map, List.map_append, List.map_flatMap, item_binders_apply]

private theorem node_binders_apply (substitution : ParameterSubstitution) (node : Node) :
    (SourceSpecialization.applyNode substitution node).initializedLetBinders =
      node.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases node with
  | expression _ => rfl
  | statement statement => exact statement_binders_apply substitution statement.form

/-- Rigid specialization preserves the entire initialized-binder inventory,
including loop headers and statements after returns. -/
theorem initializedLetBinders_applyParameters (substitution : ParameterSubstitution) (source : TypedSource) :
    (SourceSpecialization.applyTypedSource substitution source).initializedLetBinders =
      source.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  simp only [SourceSpecialization.applyTypedSource, TypedSource.initializedLetBinders,
    List.flatMap_map, List.map_flatMap, node_binders_apply]

theorem monomorphic_beforeParameters {source : TypedSource} {substitution : ParameterSubstitution}
    (monomorphic : SourceMonomorphic (SourceSpecialization.applyTypedSource substitution source)) :
    SourceMonomorphic source := by
  intro binder member
  apply monomorphic (SourceSpecialization.applyBinder substitution binder)
  rw [initializedLetBinders_applyParameters]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

/-- Every existing profile lane excludes a polymorphic initializer throughout
the original table. Factories use occurrence uniqueness, not a tail scan. -/
theorem of_row {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {rows : List SourceSpecialization.SpecializedFunction}
    (profile : Row compiled named rows)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) : SourceMonomorphic generic.typedBody := by
  have sourceEq := congrArg CheckedFunction.typedBody
    (CallableCoercionBodyProvenance.specialization_fields accepted).1
  have specializedClosed : OccurrenceGraphClosed named.specialized.function.typedBody := by
    rw [sourceEq]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters named.specialized.parameterSubstitution closed
  have monomorphic : SourceMonomorphic named.specialized.function.typedBody := by
    cases profile with
    | method _ _ _ profile => exact mono_without_lambdas accepted profile.lambdas
    | closedMethod profile _ => exact mono_without_lambdas accepted (primitive_lambdas profile)
    | coercedFactory _ _ profile _ =>
      exact mono_returned_lambda accepted specializedClosed
        profile.outerFound profile.outerForm profile.found profile.lambdas
    | ordinary _ _ profile =>
      cases profile with
      | «scoped» profile => exact mono_without_lambdas accepted profile.lambdas
      | factory profile =>
        exact mono_returned_lambda accepted specializedClosed
          profile.outerFound profile.outerForm profile.found profile.lambdas
      | scopedFactory profile =>
        exact mono_returned_lambda accepted specializedClosed
          profile.outerFound profile.outerForm profile.found profile.lambdas
  rw [sourceEq] at monomorphic
  exact monomorphic_beforeParameters monomorphic

/-- The exact final cache position selects its stored profile. The output
concerns the complete original checker carrier, not just the emitted body. -/
theorem of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    (profile : StaticProfile compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) : SourceMonomorphic generic.typedBody := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp selected
  have actual := profile.rows ⟨index, bound⟩
  rw [same] at actual
  obtain ⟨row⟩ := actual
  exact of_row row accepted closed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
