import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles

/-! Original source metadata for any number of ordinary local reads and lambda
occurrences. The recursive expression grammar excludes lambda formation, so
only actual read nodes contribute its policy exclusions. Statement structure
and the number or placement of reads are unrestricted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)

/-- One original occurrence is either an ordinary read with its exact metadata,
or a lambda whose formation uses a separate compiler certificate. -/
def NodeMetadata (node : ExpressionNode) : Prop :=
  (∃ name binder, node.form = .reference name (.local binder) ∧
    node.requirements = [] ∧ node.coercions = []) ∨
  (∃ parameters result body, node.form = .lambda parameters result body)

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
  | group other shape _ | tuple other shape _ | call other shape _ _ | constructor other shape _ _
  | unary other shape _ | binary other shape _ _ | conditional other shape _ _ _ =>
    have same := Option.some.inj (other.symm.trans found)
    subst node
    rw [form] at shape
    cases shape

private theorem read_of_syntax {source : TypedSource}
    (nodes : ∀ id node, source.lookupExpression? id = some node → NodeMetadata node)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (found : source.lookupExpression? id = some node) :
    ∃ name binder, node.form = .reference name (.local binder) ∧
      node.requirements = [] ∧ node.coercions = [] := by
  rcases nodes id node found with read | ⟨parameters, result, body, form⟩
  · exact read
  · exact False.elim (syntax_not_lambda tree found form)

/-- The complete original occurrence metadata and authentic empty local
polymorphism catalog discharge the retained production policy exclusions. -/
theorem metadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named) {source : TypedSource}
    (nodes : ∀ id node, source.lookupExpression? id = some node → NodeMetadata node)
    (locals : prepared.base.locals.bindings = []) : MetadataFor prepared named source where
  requirements := by
    intro id tree node found
    obtain ⟨_, _, _, requirements, _⟩ := read_of_syntax nodes tree found
    exact requirements
  coercions := by
    intro id tree node found
    obtain ⟨_, _, _, _, coercions⟩ := read_of_syntax nodes tree found
    exact coercions
  initializer := by intro id tree; simp only [locals, List.find?_nil]
  arguments := by
    intro id tree node found callee ids actual form
    obtain ⟨_, _, read, _, _⟩ := read_of_syntax nodes tree found
    rw [read] at form
    cases form
  localRead := by intro id tree node found name binder form; simp only [locals, List.any_nil]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
