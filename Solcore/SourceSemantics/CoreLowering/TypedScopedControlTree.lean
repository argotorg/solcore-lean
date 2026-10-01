import Solcore.SourceSemantics.CoreLowering.TypedScopedStatementMeaning

/-! A recursive typed control spine over the production LocalLoop traversal.
Ordinary expression sequences are leaves; block, if, and expression prefixes
can appear recursively at any depth. Inner lists use scoped mode and the same
raw enclosing return type. Allocation and calls are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedScopedControl
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) :
    Bool → List StatementId → TypeSystem.Ty → Prop where
  | fragment {mode statements expected}
      (child : TypedScopedStatements.Syntax source context mode statements expected) :
      Syntax source context mode statements expected
  | discard {mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | block {mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source context false statements expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | ifThen {mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (thenSyntax : Syntax source context false thenBody expected)
      (elseSyntax : Syntax source context false (elseBody.getD []) expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

inductive Tree (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | fragment {mode statements expected type code}
      (child : TypedScopedStatements.Tree readFuel values source context solved reasonAt scope mode statements expected type code) :
      Tree readFuel values source context solved reasonAt scope mode statements expected type code
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree readFuel values source context solved reasonAt scope mode rest expected type body) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree readFuel values source context solved reasonAt scope false statements expected type innerCode)
      (remaining : Tree readFuel values source context solved reasonAt scope mode rest expected type body) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree readFuel values source context solved reasonAt scope false thenBody expected type thenCode)
      (elseTree : Tree readFuel values source context solved reasonAt scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree readFuel values source context solved reasonAt scope mode rest expected type body) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

end Solcore.SourceSemantics.CoreLowering.TypedScopedControl
