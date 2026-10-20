import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree

/-! The common lexical compiler tree with its original scoped-discard guard.
This finite body grammar is independent of named-function materialization and
accepts no execution law. Allocation and dead-suffix receipts are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree
open Core Frontend SourceInference GenericLexicalStatements

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {context scope mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree layouts owner active frame globals onError values source expressions context scope mode [] expected type (LocalLoop.fallthrough type)
  | returnUnit {context scope mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {context scope mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : expressions context scope expression lowered) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {context scope id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : expressions context scope expression lowered) :
      Tree layouts owner active frame globals onError values source expressions context scope true [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : expressions context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : expressions context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions context scope false statements expected type innerCode)
      (stops : Stopped source statements)
      (issued : IssuedSuffix source scope mode rest type suffix) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode suffix)
  | terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions context scope false elseBody expected type elseCode)
      (thenStops : Stopped source thenBody) (elseStops : Stopped source elseBody)
      (issued : IssuedSuffix source scope mode rest type suffix) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix)


theorem Tree.forget {layouts owner active frame globals onError values source expressions context scope mode statements expected type code}
    (tree : Tree layouts owner active frame globals onError values source expressions context scope mode statements expected type code) :
    GenericLexicalStatements.Tree layouts owner active frame globals onError values source expressions context scope mode statements expected type code := by
  induction tree <;> first
  | solve | apply GenericLexicalStatements.Tree.nil <;> assumption
  | solve | apply GenericLexicalStatements.Tree.returnUnit <;> assumption
  | solve | apply GenericLexicalStatements.Tree.returnValue <;> assumption
  | solve | apply GenericLexicalStatements.Tree.tail <;> assumption
  | solve | apply GenericLexicalStatements.Tree.uninitialized <;> assumption
  | solve | apply GenericLexicalStatements.Tree.initialized <;> assumption
  | solve | apply GenericLexicalStatements.Tree.discard <;> assumption
  | solve | apply GenericLexicalStatements.Tree.block <;> assumption
  | solve | apply GenericLexicalStatements.Tree.ifThen <;> assumption
  | solve | apply GenericLexicalStatements.Tree.terminalBlock <;> assumption
  | solve | apply GenericLexicalStatements.Tree.terminalIf <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree
