import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability

/-! A complete source with one local read and one lambda has only that read
in the recursive caller grammar. Exact preservation of its metadata supplies
the global original and compiler-view exclusions from actual node contents. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)

private theorem syntax_node {source : TypedSource} {id : ExpressionId}
    (tree : Syntax source id) : ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | leaf product => cases product <;> exact ⟨_, by assumption⟩
  | group found _ _ | tuple found _ _ | call found _ _ _
  | unary found _ _ | binary found _ _ _ | conditional found _ _ _ _ =>
    exact ⟨_, found⟩

private theorem syntax_not_lambda {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) : False := by
  cases tree with
  | leaf product =>
    cases product with
    | literal other atomic =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at atomic
      cases atomic
    | read other shape | group other shape _ | pair other shape _ _ =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at shape
      cases shape
  | group other shape _ | tuple other shape _ | call other shape _ _
  | unary other shape _ | binary other shape _ _ | conditional other shape _ _ _ =>
    have same := Option.some.inj (other.symm.trans found)
    subst node
    rw [form] at shape
    cases shape

/-- The original lookup is restricted by the complete retained occurrence list. -/
theorem expression_cases {source : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) : node = read ∨ node = lambda := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa using present

/-- Even a metadata view cannot turn the outer lambda into a supported read. -/
theorem syntax_read {source view : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    (viewRead : view.lookupExpression? read.id = some read)
    {id : ExpressionId} (tree : Syntax view id) :
    id = read.id ∧ view.lookupExpression? id = some read := by
  obtain ⟨actual, found⟩ := syntax_node tree
  obtain ⟨original, originalFound, _sameId, sameForm⟩ := metadata.expression found
  rcases expression_cases nodes originalFound with same | same
  · subst original
    have identity : id = read.id := (lookupExpression?_sound originalFound).2.symm
    exact ⟨identity, identity.symm ▸ viewRead⟩
  · subst original
    exact False.elim (syntax_not_lambda tree found (sameForm.symm.trans lambdaForm))

/-- Real local-read metadata and an empty local-polymorphism catalog provide
all global exclusions required by the retained compiler policy. -/
theorem metadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named) {source view : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {name : String} {binder : Resolved.LocalId}
    (viewOf : LambdaMetadataViews.MetadataView source view)
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    (viewRead : view.lookupExpression? read.id = some read)
    (readForm : read.form = .reference name (.local binder))
    (requirements : read.requirements = []) (coercions : read.coercions = [])
    (locals : prepared.base.locals.bindings = []) : MetadataFor prepared named view where
  requirements := by
    intro id tree node found
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    exact same.symm ▸ requirements
  coercions := by
    intro id tree node found
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    exact same.symm ▸ coercions
  initializer := by intro id tree; simp only [locals, List.find?_nil]
  arguments := by
    intro id tree node found callee ids actual form
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    subst node
    rw [readForm] at form
    cases form
  localRead := by intro id tree node found name binder form; simp only [locals, List.any_nil]

/-- All actual references in this one-statement body lead to its local read. -/
theorem reached_node {source : TypedSource} {read : ExpressionNode} {statement : StatementNode}
    {name : String} {binder : Resolved.LocalId}
    (readFound : source.lookupExpression? read.id = some read)
    (readForm : read.form = .reference name (.local binder))
    (statementFound : source.lookupStatement? statement.id = some statement)
    (statementForm : statement.form = .returnStmt (some read.id))
    {id : NodeId}
    (reached : CallableLambdaBodyReachability.Reaches source [.statement statement.id] id) :
    id = .statement statement.id ∨ id = .expression read.id := by
  induction reached with
  | root member => exact Or.inl (List.mem_singleton.mp member)
  | expression parent found edge ih =>
      rcases ih with same | same
      · cases same
      · cases same
        have identical := Option.some.inj (found.symm.trans readFound)
        subst identical
        simp [readForm, ExpressionForm.references] at edge
  | statement parent found edge ih =>
      rcases ih with same | same
      · cases same
        have identical := Option.some.inj (found.symm.trans statementFound)
        subst identical
        exact Or.inr (by simpa [statementForm, StatementForm.references] using edge)
      · cases same

/-- The finite actual encoder receipt cannot refer to the unsupported lambda. -/
theorem lowered_read_id {source : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    id = read.id := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  rcases expression_cases nodes certificate.metadata.found with same | same
  · exact ((lookupExpression?_sound certificate.metadata.found).2.symm.trans (congrArg ExpressionNode.id same))
  · have form := certificate.form
    rw [same, lambdaForm] at form
    cases form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
