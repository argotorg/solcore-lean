import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning

/-! Genuine lexical Source syntax supplies facts at actual expression and
statement sites. Tail facts use the actual successful Source prefix, so a
stopping block or branch does not require typing its unexecuted suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
open Frontend SourceInference GenericLexicalStatements
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Syntax source expressionSyntax context mode (id :: rest) expected

def ExpressionFacts (source : TypedSource) (context : SourceSemantics.Context)
    (id : ExpressionId) (node : ExpressionNode) : Prop :=
  ExpressionHasType source context id node.type

theorem expression {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {child : ExpressionId} {node : ExpressionNode}
    (facts : HeadFacts source expressionSyntax context id expected)
    (slot : ExpressionSlot source id child)
    (found : source.lookupExpression? child = some node) :
    ExpressionFacts source context child node := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> cases slot <;> simp_all [ExpressionFacts]

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {statements : List StatementId}
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) :
    Syntax source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> simp_all

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Syntax source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> cases boolean <;> simp_all

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (typedSyntax : Syntax source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Syntax source expressionSyntax nextContext mode rest expected := by
  cases typedSyntax with
  | returnUnit _ found form sourceType =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique (lookupStatement?_sound found) form executed
    cases impossible
  | returnValue _ found form sourceType expressionFound valueType typed value =>
    obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form executed
    cases impossible
  | tail found form sourceType expressionFound valueType typed value =>
    have same := Option.some.inj (found.symm.trans ‹source.lookupStatement? id = some node›)
    subst same
    exact False.elim (notTail rfl rfl _ form)
  | uninitialized found form declaration monomorphic extended ordinary remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letUninitialized unique (lookupStatement?_sound found) form executed
    have same := Dynamic.BinderExtends.functional extended actualExtension
    exact same ▸ remaining
  | initialized found form declaration monomorphic extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letInitialized unique (lookupStatement?_sound found) form monomorphic executed
    have same := Dynamic.BinderExtends.functional extended actualExtension
    exact same ▸ remaining
  | discard found form notTail sourceType expressionFound typed value remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.expression unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | block found form sourceType inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | ifThen found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | terminalBlock unique found form sourceType inner stops =>
    have impossible := block_terminates unique found form stops executed
    cases impossible
  | terminalIf unique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops =>
    have impossible := conditional_terminates unique found form thenStops elseStops executed
    cases impossible

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) :
    StaticSites (Syntax source expressionSyntax) (HeadFacts source expressionSyntax)
      (ExpressionFacts source) program evidence source where
  head := fun typedSyntax => ⟨_, _, typedSyntax⟩
  expression := expression
  block := block
  branch := branch
  tail := tail unique

end Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
