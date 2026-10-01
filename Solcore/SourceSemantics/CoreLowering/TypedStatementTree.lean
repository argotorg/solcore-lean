import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! A fixed-scope function sequence with typed compatible expressions.
The static source spine retains raw result types and independent expression
 typing. Unreachable suffixes of explicit returns need no execution certificate.
Scalar-key mapping indexes use ordinary comparator code and typed captures.
Let bindings, assignments, scoped statements and calls are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatements
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) :
    List StatementId → TypeSystem.Ty → Prop where
  | nil : Syntax source context [] .unit
  | returnUnit {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) : Syntax source context (id :: rest) .unit
  | returnValue {id node expression expressionNode expected} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context (id :: rest) expected
  | tail {id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context [id] expected
  | discard {id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context rest expected) : Syntax source context (id :: rest) expected

inductive Tree (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil : Tree readFuel values source context solved reasonAt scope [] .unit .unit (LocalLoop.fallthrough .unit)
  | returnUnit {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree readFuel values source context solved reasonAt scope rest expected type body) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

/-- The existing production body wrapper, with no extra Core instruction. -/
abbrev finish := CompatibleStatements.finish

end Solcore.SourceSemantics.CoreLowering.TypedStatements
