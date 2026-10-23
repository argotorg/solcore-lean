import Solcore.SourceSemantics.SourceCompiledLocalDomainSeparation
import Solcore.SourceSemantics.SourceCompiledLocalLexicalAllocation
import Solcore.SourceSemantics.SourceCompiledLocalCanonicalReadOrder
import Solcore.SourceSemantics.CoreLowering.CallableBodyGraphDescendants
import Solcore.SourceSemantics.CoreLowering.CallableLambdaRootReachability
import Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts

/-! The actual saved scope and selected caller determine complete substitution
agreement on each reached node. The proof retains this equality before any
projection to a body view. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
open CallableLambdaBodyReachability CallableBodyMetadataViews

private theorem expression_node {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

private theorem initialized_of_origin {source : TypedSource}
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance) :
    ({ binder := localInstance.binding.binder,
       initializer := .expression localInstance.binding.initializer } : InitializedLetBinding) ∈
      initializedLetBindings source := by
  obtain ⟨statement, member, form⟩ := localLambdaBindings_statement_origin origin.binding_member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

private theorem outside_same {lexical current : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical current)
    {q : TypeVarId} (outside : q ∉ current.domain) :
    lexical.apply (.variable q) = current.apply (.variable q) := by
  have lexicalOutside : q ∉ lexical.domain := fun member =>
    outside (extension.domain q member)
  rw [Substitution.apply_variable_of_lookup?_eq_none
      ((Substitution.lookup?_eq_none_iff_not_mem_domain lexical q).mpr lexicalOutside),
    Substitution.apply_variable_of_lookup?_eq_none
      ((Substitution.lookup?_eq_none_iff_not_mem_domain current q).mpr outside)]

/-- A concrete caller allocated after this target cannot change the target's
own or nested quantifiers. Captured ancestors agree by the actual saved-context
extension. The conclusion compares only this exact lambda's reached initializer and body. -/
theorem nodes_at_later_caller
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    (before : target.binding.binder.id.binderIndex < caller.binding.binder.id.binderIndex)
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    ∀ node ∈ named.specialized.function.typedBody.nodes,
      Reaches named.specialized.function.typedBody
        (lambdaRoots target.binding.initializer body) node.id →
      node.applySubstitution lexical = node.applySubstitution caller.substitution := by
  have covered : ResidualEntryCovered named.specialized.function.typedBody
      (body.map NodeId.statement) (target.binding.binder.scheme.quantified ++ lexical.domain) :=
    captured.body (fun _ member => List.mem_append.mpr member) (expression_node found) form
  intro node member reached
  rcases reached.lambda_roots_cases found form with atRoot | bodyPath
  · obtain ⟨variables, scope, origins⟩ := captured
    have actualScope : ResidualScopePath named.specialized.function.typedBody node.id variables := by
      simpa only [atRoot] using scope
    obtain ⟨types, binders⟩ :=
      SelectedCompilationResidualScopes.row_path_support cached row member actualScope
    apply GeneralizedLocalResidualAgreement.node_of_scope types binders
    intro q occurs
    rcases origins q occurs with own | saved
    · apply outside_same extension
      exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
        (initialized_of_origin targetOrigin) before own
    · exact (extension.action q saved).symm
  obtain ⟨variables, scope, origins⟩ := ResidualScopeReachability.scope_of_reaches covered bodyPath
  obtain ⟨types, binders⟩ :=
    SelectedCompilationResidualScopes.row_path_support cached row member scope
  apply GeneralizedLocalResidualAgreement.node_of_scope types binders
  intro q occurs
  rcases origins q occurs with entry | nested
  · rcases List.mem_append.mp entry with own | saved
    · apply outside_same extension
      exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
        (initialized_of_origin targetOrigin) before own
    · exact (extension.action q saved).symm
  · obtain ⟨id, statement, binder, initializer, parent, statementFound, statementForm, owned⟩ := nested
    have contained := lookupStatement?_sound statementFound
    let binding : InitializedLetBinding :=
      { binder := binder, initializer := .expression initializer }
    have localMember : binding ∈ initializedLetBindings
        {named.specialized.function.typedBody with nodes := [.statement statement]} := by
      simp only [initializedLetBindings, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change _ ∈ statementInitializedLetBindings statement.form
      rw [statementForm]
      exact List.mem_singleton_self _
    have globalMember : binding ∈ initializedLetBindings named.specialized.function.typedBody := by
      apply List.mem_flatMap.mpr
      refine ⟨.statement statement, contained.1, ?_⟩
      simpa only [initializedLetBindings, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using localMember
    have descendant : Descends named.specialized.function.typedBody
        (.expression target.binding.initializer) (Node.statement statement).id := by
      simpa only [Node.id, contained.2] using parent.descends_from_lambda found form
    have allocated := selected.local_lambda_initialized_binder_le checked targetOrigin
      contained.1 descendant localMember
    apply outside_same extension
    exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
      globalMember (Nat.lt_of_le_of_lt allocated before) owned

/-- The exact local read supplies the ordering used above. The saved-context
extension alone is never treated as a noninterference law. -/
theorem nodes_at_local_read
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    {read : ExpressionNode} {name : String}
    (readMember : Node.expression read ∈ named.specialized.function.typedBody.nodes)
    (readPath : Descends named.specialized.function.typedBody
      (.expression caller.binding.initializer) (.expression read.id))
    (readForm : read.form = .reference name (.local target.binding.binder.id))
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    ∀ node ∈ named.specialized.function.typedBody.nodes,
      Reaches named.specialized.function.typedBody
        (lambdaRoots target.binding.initializer body) node.id →
      node.applySubstitution lexical = node.applySubstitution caller.substitution :=
  nodes_at_later_caller selected artifact checked position row callerOrigin targetOrigin
    (selected.local_lambda_descendant_read_binder_lt checked callerOrigin readMember readPath readForm)
    extension captured found form

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement
