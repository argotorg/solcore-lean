import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree

/-! The lexical slice of the shared body scanner recovers its changing Source
contexts from original statement typing. The executable test inspects original
forms only and bounds the traversal by the original node inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySyntax
open Core Frontend SourceInference GenericLexicalStatements

inductive Syntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
    SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop where
  | nil {context mode expected} (allowed : mode = false ∨ expected = .unit) : Syntax source expressionSyntax context mode [] expected
  | returnUnit {context mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) : Syntax source expressionSyntax context mode (id :: rest) .unit
  | returnValue {context mode id node expression expressionNode expected} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression) : Syntax source expressionSyntax context mode (id :: rest) expected
  | tail {context id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression) : Syntax source expressionSyntax context true [id] expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source expressionSyntax nextContext mode rest expected) :
      Syntax source expressionSyntax context mode (id :: rest) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : expressionSyntax initializer)
      (remaining : Syntax source expressionSyntax nextContext mode rest expected) :
      Syntax source expressionSyntax context mode (id :: rest) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Syntax source expressionSyntax context false statements expected)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (thenSyntax : Syntax source expressionSyntax context false thenBody expected)
      (elseSyntax : Syntax source expressionSyntax context false (elseBody.getD []) expected)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected

  | terminalBlock {context mode id node statements rest expected}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = expected)
      (inner : Syntax source expressionSyntax context false statements expected)
      (stops : Stopped source statements) : Syntax source expressionSyntax context mode (id :: rest) expected
  | terminalIf {context mode id node condition conditionNode thenBody elseBody rest expected}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (sourceType : node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (thenSyntax : Syntax source expressionSyntax context false thenBody expected)
      (elseSyntax : Syntax source expressionSyntax context false elseBody expected)
      (thenStops : Stopped source thenBody) (elseStops : Stopped source elseBody) :
      Syntax source expressionSyntax context mode (id :: rest) expected

def lexicalOnly (source : TypedSource) : Nat → List StatementId → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | fuel + 1, id :: rest =>
    match source.lookupStatement? id with
    | none => false
    | some node => match node.form with
      | .returnStmt _ => true
      | .letDecl _ _ | .expression _ _ => lexicalOnly source fuel rest
      | .block inner => lexicalOnly source fuel inner && lexicalOnly source fuel rest
      | .ifThen _ left right => lexicalOnly source fuel left && lexicalOnly source fuel (right.getD []) && lexicalOnly source fuel rest
      | _ => false

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id rest facts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ next first remaining, StatementHasType source control context id next first ∧
      StatementsHaveType source control next rest final remaining := by
  cases typed with
  | singleton head => exact ⟨_,_,_,head,.nil _ _⟩
  | cons head tail => exact ⟨_,_,_,head,tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id node facts}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original,contains,same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

theorem of_scan {source approved expected mode statements}
    (scan : ScopedSourceBodyAdmission.Scan source approved expected mode statements)
    (unique : NodeOccurrencesUnique source) {fuel : Nat}
    (lexical : lexicalOnly source fuel statements = true)
    {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    Syntax source approved context mode statements expected := by
  induction scan generalizing fuel control context final facts with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form sourceType expectedUnit =>
      subst expected
      exact .returnUnit rest found form sourceType
  | returning rest found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue actual =>
        exact .returnValue rest found form sourceType expressionFound valueType
          (by simpa only [result, valueType] using actual) value
  | tail found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionValue actual =>
        exact .tail found form sourceType expressionFound valueType (expression_at unique expressionFound actual) value
  | absent found form declaration monomorphic ordinary _ ih =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form] at lexical
        obtain ⟨_, _, _, head, tail⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | letUninitialized _ extended => exact .uninitialized found form declaration monomorphic extended ordinary (ih lexical result tail)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form] at lexical
        obtain ⟨_, _, _, head, tail⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | letInitialized actual _ extended =>
          exact .initialized found form declaration monomorphic extended ordinary expressionFound valueType
            (by simpa only [valueType] using actual) value (ih lexical result tail)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found form continuing sourceType expressionFound value _ ih =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form] at lexical
        obtain ⟨_, _, _, head, tail⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | expressionValue actual | expressionDiscard actual =>
          exact .discard found form (by rcases continuing with same | same <;> simp_all) continuing sourceType expressionFound
            (expression_at unique expressionFound actual) value (ih lexical result tail)
  | block found form _ _ inner remaining =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form, Bool.and_eq_true] at lexical
        obtain ⟨_, _, _, head, tail⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | block actual => exact .block found form (inner lexical.1 result actual) (remaining lexical.2 result tail)
  | conditional found form _ conditionFound conditionType value _ _ _ left right remaining =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form, Bool.and_eq_true] at lexical
        obtain ⟨_, _, _, head, tail⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | ifWithoutElse condition actual =>
          exact .ifThen found form conditionFound conditionType
            (by simpa only [conditionType] using condition) value (left lexical.1.1 result actual)
            (right lexical.1.2 result (.nil _ _)) (remaining lexical.2 result tail)
        | ifWithElse condition first second =>
          exact .ifThen found form conditionFound conditionType
            (by simpa only [conditionType] using condition) value (left lexical.1.1 result first)
            (right lexical.1.2 result second) (remaining lexical.2 result tail)
  | terminalBlock found form sourceType _ stops _ inner =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form, Bool.and_eq_true] at lexical
        obtain ⟨_, _, _, head, _⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | block body => exact .terminalBlock unique found form sourceType (inner lexical.1 result body) (stops.stopped unique body)
  | terminalConditional found form sourceType conditionFound conditionType value _ _ first second _ left right =>
      cases fuel with
      | zero => simp [lexicalOnly] at lexical
      | succ fuel =>
        simp only [lexicalOnly, found, form, Bool.and_eq_true] at lexical
        obtain ⟨_, _, _, head, _⟩ := head_tail typed
        have original := form_at unique found head
        rw [form] at original
        cases original with
        | ifWithElse condition firstTyped secondTyped =>
          exact .terminalIf unique found form sourceType conditionFound conditionType
            (by simpa only [conditionType] using condition) value
            (left lexical.1.1 result firstTyped) (right lexical.1.2 result secondTyped)
            (first.stopped unique firstTyped) (second.stopped unique secondTyped)
  | breaking _ found form | continuing _ found form =>
      cases fuel <;> simp [lexicalOnly, found, form] at lexical
  | whileLoop found form | assign found form | assignProjected found form
  | bitNot found form | bitNotProjected found form | forLoop found form
  | matching found form | terminalMatch found form =>
      cases fuel <;> simp [lexicalOnly, found, form] at lexical

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySyntax
