import Lean
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.SourceSemantics.SourceSpecializationStatementReferences

/-! Ordinary recursive evaluation follows the same source edges as the actual
lexical collector. Lambda bodies enter through their own invocation roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem

open Lean Meta Elab Tactic in
private def unfoldActualChildren : TacticM Unit := do
  let original := `Solcore.Frontend.SourceSpecializationWorklist.directLexicalChildren
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous lexical child definition: {original}"
      found := some name
  let some name := found | throwError "missing lexical child definition: {original}"
  let definition := mkIdent name
  evalTactic (← `(tactic| unfold localLambdaLexicalChildren $definition:ident))

theorem localLambdaLexicalChildren_statement
    {source : TypedSource} {id : StatementId} {statement : StatementNode} {child : NodeId}
    (found : source.lookupStatement? id = some statement)
    (member : child ∈ statement.form.references) :
    child ∈ localLambdaLexicalChildren source (.statement id) := by
  unfold TypedSource.lookupStatement? at found
  cases looked : source.lookupNode? id.occurrence with
  | none => simp only [looked, reduceCtorEq] at found
  | some node =>
    cases node with
    | expression expression => simp only [looked, reduceCtorEq] at found
    | statement actual =>
      simp only [looked, Option.some.injEq] at found
      subst actual
      run_tac unfoldActualChildren
      simp only [NodeId.occurrenceId, looked]
      exact SourceSpecialization.statementChildNodeIds_of_reference member

theorem localLambdaLexicalChildren_expression
    {source : TypedSource} {id : ExpressionId} {expression : ExpressionNode} {child : NodeId}
    (found : source.lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (member : child ∈ expression.form.references) :
    child ∈ localLambdaLexicalChildren source (.expression id) := by
  unfold TypedSource.lookupExpression? at found
  cases looked : source.lookupNode? id.occurrence with
  | none => simp only [looked, reduceCtorEq] at found
  | some node =>
    cases node with
    | statement statement => simp only [looked, reduceCtorEq] at found
    | expression actual =>
      simp only [looked, Option.some.injEq] at found
      subst actual
      cases expression with
      | mk nodeId span type form requirements coercions localStart =>
        cases form <;> try exact False.elim (nonLambda _ _ _ rfl)
        all_goals run_tac unfoldActualChildren
        all_goals
          simpa only [NodeId.occurrenceId, looked,
            SourceSpecialization.expressionChildNodeIds_eq_references] using member

namespace LocalLambdaLexicalPath

theorem statement_child
    {source : TypedSource} {roots : List NodeId} {id : StatementId}
    {statement : StatementNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.statement id))
    (found : source.lookupStatement? id = some statement)
    (member : child ∈ statement.form.references) :
    LocalLambdaLexicalPath source roots child :=
  .child previous (localLambdaLexicalChildren_statement found member)

theorem expression_child
    {source : TypedSource} {roots : List NodeId} {id : ExpressionId}
    {expression : ExpressionNode} {child : NodeId}
    (previous : LocalLambdaLexicalPath source roots (.expression id))
    (found : source.lookupExpression? id = some expression)
    (nonLambda : ∀ parameters result body, expression.form ≠ .lambda parameters result body)
    (member : child ∈ expression.form.references) :
    LocalLambdaLexicalPath source roots child :=
  .child previous (localLambdaLexicalChildren_expression found nonLambda member)

end LocalLambdaLexicalPath
end Solcore.Frontend.SourceSpecializationWorklist
