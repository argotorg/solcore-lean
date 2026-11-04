import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.Core.LocalLoop
import Solcore.Core.OptionalCell
import Solcore.Core.LanguageResult
import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
import Solcore.SourceSemantics.CoreLowering.GenericCellHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarked
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.CaptureCopyIndexedTyping
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies

/-!
# Cell-aware ordinary bodies

Ordinary body trees and their syntax and collectors, allocation and continuations, parameter meaning and frames, snapshots of generalized declarations, and the indirect-call prefixes these bodies run.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySyntax
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode
/-! The code a generalized declaration emits. Its scope copies wrap the bundle
initializer and the marked descriptor allocation; the continuation runs over
the original scope. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode
open Core

/-- The bundle initializer bound below the descriptor allocation, inside the
copies. -/
def snapshotInner (payload : Ty) (initializer allocation : Expr) : Expr :=
  LanguageResult.bind (OptionalCell.referenceType payload) initializer (LanguageResult.success allocation)

/-- The copies with the bundle and its allocation, then the continuation over
the original scope. -/
def snapshotSequence (type : Ty) (copied body : Expr) : Expr :=
  LanguageResult.bind (LocalLoop.controlType type) copied body

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
/-! A real uninitialized declaration allocates an absent ordinary cell in the
mixed heap. Earlier generalized descriptors retain their exact stored rows. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells model cells)
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame
    cells)
  (sameDefinitions : layouts.definitions = definitions)
  (registered : frame.Registered definitions)
  {context nextContext : SourceSemantics.Context}

include ordinaryCells sameDefinitions registered in
theorem allocate_absent_at_source {allocationSource : TypedSource} {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (catalog)
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures canonical (absentRequest allocationSource scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have referenceAt : canonical[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (absentRequest allocationSource scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (absentRequest allocationSource scope binder payload) = false := ordinary
    change canonical[scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
      (absentRequest allocationSource scope binder payload) then 0 else 1) + globals]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same sameDefinitions registered environments
      (show EnvironmentsAgree Renaming.id canonical canonical from fun found => found) heaps referenceAt read
      (.absent rfl) (ordinaryCells.inject (.uninitialized projection)) (.ordinary allocated) initial ready
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inl rfl) evaluated agrees,
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference,
    nextHeaps, (by cases extended; exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))), agrees.lift _,
    .cons (.cellRef nextReference.typed) (actualTyped.weaken ⟨_, rfl⟩), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

/- Compatibility wrapper using the semantic source for the allocation request. -/
include ordinaryCells sameDefinitions registered in
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (catalog)
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures canonical (absentRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  exact allocate_absent_at_source (allocationSource := source) ordinaryCells producer sameDefinitions registered mono extended ordinary projection
    allocation annotation same  environments heaps locals agrees actualTyped reference read allocated initial ready

end Solcore.SourceSemantics.CoreLowering.CellAwareAbsentAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareBodyFrames
/-! Heap correspondence across the temporary callable-context write. The
context cell is source-unmapped and has a registered native frame type. A child
semantic frame is applied to the installed store; restoring the caller then
recovers preservation of every original administrative location. This uses a
semantic child contract, not a claim that arbitrary typed code avoids writes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBodyFrames
open Core Frontend GeneralHeap CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

variable {nativeDefinitions : DataEnvironment} {cells : GenericHeap.CellModel nativeDefinitions}

/-- Installing a related callable frame changes no represented source cell.
The new native carrier is typed by its registered definition independently of
the metadata-history witness carried alongside it. -/
theorem install {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost nextGhost : GhostFrame}
    (registered : layout.Registered nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost store)
    (nextHistory : Current inputs table next nextGhost) :
    GenericHeap.CellHeapRepresents cells mapping world heap (store.set location (encode layout next)) ∧
      CellState inputs table layout location next nextGhost (store.set location (encode layout next)) := by
  have written : store.write? location (encode layout next) = some (store.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩
  exact ⟨heaps.write_administrative (fun found => unmapped (List.mem_of_getElem? found)) typed
    (encode_runtime_typed world registered next) written, ⟨Store.write?_reads_written written, nextHistory⟩⟩

/-- A completed nested source body keeps the installed current token. Its
history is carried from entry and its value is preserved by the semantic frame. -/
theorem body_current {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {before after : Store} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame}
    (unmapped : location ∉ mapping)
    (current : CellState inputs table layout location native ghost before)
    (frame : AdministrativePreserved mapping before finalMap after) :
    CellState inputs table layout location native ghost after := by
  have unchanged := (frame location unmapped (List.getElem?_eq_some_iff.mp current.read).1).2
  exact ⟨unchanged.trans current.read, current.history⟩

/-- The completed child semantic frame prevents the context cell from becoming
a source alias. Restoration preserves the represented final heap and recovers
the original caller token and the complete original administrative frame. -/
theorem restore {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {after : Dynamic.Heap} {before bodyStore : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame}
    (registered : layout.Registered nativeDefinitions)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost before)
    (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after bodyStore)
    (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping (before.set location (encode layout next)) finalMap bodyStore) :
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after (bodyStore.set location (encode layout current)) ∧
      AdministrativePreserved mapping before finalMap (bodyStore.set location (encode layout current)) ∧
      CellState inputs table layout location current currentGhost (bodyStore.set location (encode layout current)) := by
  have bound := (List.getElem?_eq_some_iff.mp caller.read).1
  have installed : before.write? location (encode layout next) = some (before.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩
  have finalTyped := worlds.lookup typed
  have written : bodyStore.write? location (encode layout current) = some (bodyStore.set location (encode layout current)) :=
    Store.write?_eq_some_iff.mpr ⟨heaps.runtime_hasTypes.location_lt finalTyped, rfl⟩
  have finalUnmapped := (frame location unmapped (by simpa using bound)).1
  refine ⟨heaps.write_administrative (fun found => finalUnmapped (List.mem_of_getElem? found)) finalTyped
    (encode_runtime_typed finalWorld registered current) written, ?_,
    ⟨Store.write?_reads_written written, caller.history⟩⟩
  intro other absent oldBound
  obtain ⟨stillAbsent, unchanged⟩ := frame other absent (by simpa using oldBound)
  refine ⟨stillAbsent, ?_⟩
  by_cases same : other = location
  · subst other
    exact (Store.write?_reads_written written).trans caller.read.symm
  · exact (Store.write?_preserves_other written same).trans
      (unchanged.trans (Store.write?_preserves_other installed same))

/-- Protected snapshots remain valid while the temporary context is installed
when their actual locations are distinct. Full closure environments may still
retain unused references; this is a store contract over selected locations. -/
theorem install_snapshots {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame} {records : List CallableIndexedSnapshots.Record}
    (caller : CellState inputs table layout location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All inputs table layout mapping store records)
    (distinct : ∀ record ∈ records, record.location ≠ location) :
    CallableIndexedSnapshots.All inputs table layout mapping (store.set location (encode layout next)) records := by
  intro record member
  exact (snapshots record member).other_write (distinct record member)
    (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CellAwareBodyFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareParameterTyped
/-! Type preservation through the actual indexed parameter prefix. The
argument projection, snapshot, marker and source cell are the emitted prefix's
real operations. The final actual environment includes every retained argument
temporary; its typing is derived from the initial environment and allocations.
No continuation execution or final environment typing is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareParameterTyped
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning

/-- Each parameter leaves its payload temporary below its source-cell reference. -/
def prefixContext (bindings : List Binding) (initial : Core.Context) : Core.Context :=
  bindings.foldl (fun context binding => OptionalCell.referenceType binding.2 :: binding.2 :: context) initial

theorem prefixContext_length (bindings : List Binding) (initial : Core.Context) :
    (prefixContext bindings initial).length = 2 * bindings.length + initial.length := by
  induction bindings generalizing initial with
  | nil => simp [prefixContext]
  | cons binding rest ih =>
    simpa [prefixContext, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (OptionalCell.referenceType binding.2 :: binding.2 :: initial)

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
namespace Stateful

theorem prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts layout cells)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt (catalog := catalog) producer contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      (∃ suffix, finalStore = store ++ suffix) ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
          finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩ := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, ⟨[], by simp⟩, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, actualTyped, .refl _ _ _, ⟨initial, protocol.refl initial⟩⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextHeaps, nextReference, frame,
        nextState, nextRelated⟩ :=
        producer.complete allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl)
          (ordinaryCells.inject (.initialized head)) (.ordinary Dynamic.Heap.Allocates.append)
          initial (readyAt initial read)
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, storeExtension, finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState, finalRelated⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext) nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped nextState
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, ?_, finalActualLayout, ?_, finalTyped, ?_, ⟨finalState, protocol.trans nextRelated finalRelated⟩⟩
      · obtain ⟨suffix, storeEq⟩ := storeExtension
        exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE renamedAllocation)

end Stateful

end Solcore.SourceSemantics.CoreLowering.CellAwareParameterTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLambdaViewPrefix
/-! A closure's entry copies its captured cells and then installs its
parameters, reaching the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
the compiler view is retained independently of the canonical closure source.
Body correspondence remains a separate concrete static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLambdaViewPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- The allocation authenticator observes the same owner, binder inputs,
forms, and statement metadata in every genuine metadata view. -/
theorem sourceView_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) :
    SourceCoreAllocationCodebook.sourceView source = SourceCoreAllocationCodebook.sourceView view := by
  have go {before after : List Node} (related : DataPatternValues.ListRel LambdaMetadataViews.NodeView before after) :
      before.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) =
      after.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) := by
    induction related with
    | nil => rfl
    | cons head _ ih =>
      cases head with
      | expression sameId sameForm => simp only [List.map_cons, sameId, sameForm, ih]
      | statement => exact congrArg (List.cons _) ih
  simp only [SourceCoreAllocationCodebook.sourceView, metadata.owner, metadata.inputs, metadata.roots]
  exact congrArg (fun nodes => SourceCoreAllocationCodebook.MetadataSource.mk view.owner view.inputs view.roots nodes) (go metadata.nodes)

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (cells : GenericHeap.CellModel ambient.definitions)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : Scope) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copiedContext : Core.Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) environment canonical ambient.definitions
  heaps : GenericHeap.CellHeapRepresents cells mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  storeExtension : ∃ suffix, store = initialStore ++ suffix
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CellAwareParameterTyped.prefixContext bindings copiedContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

private theorem liftMany_insertion (count cutoff : Nat) :
    DataMatchCoreAllocation.liftMany count (Renaming.insertion cutoff) = Renaming.insertion (cutoff + count) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [DataMatchCoreAllocation.liftMany, Renaming.lift_insertion, ih]
    congr 1
    omega

namespace Stateful

/-- The entry copies the closure's captured cells through the marked
allocator, then the actual prefix receipts construct parameter allocation, the
typed body environment and the surviving context-reference slot. Its read and
unmapped status follow from allocation preservation. The protected state
crosses the copies administratively and is rebound to the copied slots. No
final body facts are assumed. -/
theorem entry_of_accepted_with_spine_of_copies
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol layouts layout cells)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (inputIds : function.source.inputs.map TypedBinder.id = view.inputs.map TypedBinder.id)
    (copies : ∀ id, (SourceSemantics.CaptureBinders.copiedBinder? function.source id).isSome =
      (SourceSemantics.CaptureBinders.copiedBinder? view id).isSome)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry cells function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨copiesEnvironment, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap,
      copiedWorld, copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds,
      copiedFrame, ⟨copiedSuffix, copiedStoreEq⟩, copiedRead, copiedLookups, _copiedTypes, copiedTyped,
      copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix_cells (pre := [DataPatternValues.packValues nativeArguments])
      (preContext := [SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)])
      copied definitions registered environments heaps actualLayout rfl types actualTyped reference read
  have sourceCopy := copy.of_copiedIds fun id => (copies id).symm
  obtain ⟨copiedUnmapped, _⟩ := copiedFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨extendedState, extendedRelated⟩ := ProtectedStateTransition.AdministrativeTransport.transition protocol
    transport initial copiedMaps copiedWorlds copiedFrame sourceCopy.metadata_extends
  obtain ⟨reboundState, reboundRelated⟩ := rebinds extendedState copiedCanonical slots
  have copiedReference : copiedCanonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) := by
    rw [slots _ (by omega)]
    exact reference
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) copiedCanonical
      (DataPatternValues.packValues nativeArguments :: copiedCanonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, storeExtension, sourceLayout, lookups, spine, finalTyped, agreement, transition⟩ :=
    CellAwareParameterTyped.Stateful.prefix_typed tree ordinaryCells protocol producer definitions registered
      (represented.extend copiedMaps copiedWorlds) copiedEnvironments copiedHeaps
      sourceLayout copiedLookups copiedTyped (allTypes := bindings.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by
        intro binding member
        have same := congrArg (fun ids : List Resolved.LocalId =>
          ids.any (fun id => decide (id = binding.1.id))) inputIds
        simp only [List.any_map] at same
        exact same.symm.trans (kinds binding member))
      (by simpa using copiedReference) copiedRead copiedUnmapped reboundState readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : bindings.length + scope.length + 1 + globals = added.length + (scope.length + 1 + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using copiedReference
  have finalLookups : EnvironmentsAgree (Renaming.comp embedding (Renaming.insertion bindings.length))
      finalCanonical finalActual := by
    intro index value found
    apply lookups
    have transported := sourceLayout found
    simpa only [liftMany_insertion, Nat.zero_add] using transported
  have bodyEq : (body.weakenAt bindings.length).rename embedding =
      body.rename (Renaming.comp embedding (Renaming.insertion bindings.length)) := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
  rw [bodyEq] at agreement
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation copiedUnmapped
    (List.getElem?_eq_some_iff.mp copiedRead).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  have copiedLocals := Dynamic.EnvironmentCopies.agrees initialLocals sourceCopy
  have finalStoreExtension : ∃ suffix, finalStore = store ++ suffix := by
    obtain ⟨suffix, storeEq⟩ := storeExtension
    exact ⟨copiedSuffix ++ suffix, by rw [storeEq, copiedStoreEq, List.append_assoc]⟩
  refine ⟨⟨copiesEnvironment, copiedHeap, copiedContext, environment, heap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, Renaming.comp embedding (Renaming.insertion bindings.length),
    sourceCopy, allocated, by simpa [CallableIndexedParameters.scope_eq] using finalEnvironments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 copiedLocals allocated,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans preservation, finalStoreExtension,
    sourceCopy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocated), finalLookups, finalTyped,
    finalReference, unchanged.trans copiedRead, finalUnmapped, copyAgreement.continuation.trans agreement⟩,
    added, copiedCanonical, prefixLength, canonicalEq, slots, ?_⟩
  have composed : ProtectedStateTransition.Transition protocol initial
      ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
        finalMap, finalWorld, heap, finalStore, finalCanonical⟩ := by
    obtain ⟨reached, related⟩ := transition
    exact ⟨reached, protocol.trans (protocol.trans extendedRelated reboundRelated) related⟩
  simpa only [CallableIndexedParameters.scope_eq] using composed

/-- Compatibility with the original full metadata-view receipt. -/
theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol layouts layout cells)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry cells function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  exact entry_of_accepted_with_spine_of_copies functions ordinaryCells onError protocol producer transport rebinds
    (congrArg (List.map TypedBinder.id) viewOfSource.inputs)
    (fun id => by rw [LambdaMetadataViews.MetadataView.copiedBinder viewOfSource])
    accepted copied parameters kinds extended definitions registered represented environments heaps initialLocals
    actualLayout types actualTyped reference read unmapped initial readyAt

end Stateful

end Solcore.SourceSemantics.CoreLowering.CellAwareLambdaViewPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyCollector
/-! Extract the finite lexical tree from actual contextual compiler success.
The retained scoped-discard guard and each allocator receipt come from the
original Source grammar and real compiler branch, respectively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyCollector
open Core Frontend SourceInference GenericLexicalStatements
open CompatibleEncoding (bind_ok)
private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

open CompatibleStatementBindings (binder_projected scope_bind)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Arbitrarily mixed ordinary lets are extracted from the real
compiler, including each actual marker/snapshot allocator receipt. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareOrdinaryBodySyntax.Syntax source expressionSyntax context mode statements expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | nil allowed =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    cases accepted
    exact .nil allowed
  | @returnUnit context mode id node rest found form sourceType =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .returnUnit rest found form
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .returnValue rest found form expressionFound valueType (extractExpressions context declarations syntaxValue expressionFound typed generated)
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .tail found form expressionFound valueType (extractExpressions context declarations syntaxValue expressionFound typed generated)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih
          (scope_bind payload declarations declaration extended) projection generated)

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (extractExpressions context declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih
          (scope_bind lowered.type declarations declaration extended) projection generatedBody)

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail continuing sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        exact .discard found form notTail continuing expressionFound (extractExpressions context declarations syntaxValue expressionFound typed generated)
          (ih declarations projection generatedBody)

  | @block context mode id node statements rest expected found form inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      exact .block found form (innerIH declarations projection generatedInner) (restIH declarations projection generatedBody)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH declarations projection generatedThen) (elseIH declarations projection generatedElse) (restIH declarations projection generatedBody)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH declarations projection generatedThen) (elseIH declarations projection generatedElse) (restIH declarations projection generatedBody)

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      exact .terminalBlock exactUnique found form
        (innerIH declarations projection generatedInner) stops
        (IssuedSuffix.of_accepted generatedSuffix)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      exact .terminalIf exactUnique found form conditionFound conditionType
        (extractExpressions context declarations conditionSyntax conditionFound typed generatedCondition)
        (thenIH declarations projection generatedThen)
        (elseIH declarations projection generatedElse)
        thenStops elseStops (IssuedSuffix.of_accepted generatedSuffix)

/-- The complete production body wrapper keeps the extracted binding spine. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareOrdinaryBodySyntax.Syntax source expressionSyntax context true statements expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError values source certificates
        context scope true statements expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy extractExpressions syntaxTree declarations projection generated⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyCollector
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
/-! Ordinary initialized declarations use the actual marked allocation producer
in a mixed heap. The successful initializer value is allocated at its reached
state, preserving every existing descriptor and the real caller transition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells model cells)
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts frame
    cells)
  (sameDefinitions : layouts.definitions = definitions)
  (registered : frame.Registered definitions)
  {context nextContext : SourceSemantics.Context}

include ordinaryCells sameDefinitions registered in
theorem allocate_initialized_at_source {allocationSource : TypedSource} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest allocationSource scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  have canonicalLayout : EnvironmentsAgree (initializedRequest allocationSource scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (initializedRequest allocationSource scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest allocationSource scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest allocationSource scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, captures, capturedTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same sameDefinitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (ordinaryCells.inject (.initialized represented)) (.ordinary allocated) initial ready
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, captures, capturedTyped, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons ((model.runtime_hasType represented).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation, transition⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

/- Compatibility wrapper using the semantic source for the allocation request. -/
include ordinaryCells sameDefinitions registered in
theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog
      mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩ := by
  exact allocate_initialized_at_source (allocationSource := source) ordinaryCells producer sameDefinitions registered mono extended ordinary
    allocation annotation same represented environments heaps locals agrees actualTyped reference read allocated initial ready

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
/-! An ordinary initializer may change the store before allocation. Both
continuation directions retain that reached store; failure skips allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
open Core Frontend SourceInference ReadOnly CoreProof
open CompatibleStatementInitialized (sequence)

private theorem body_rename (body : Expr) (embedding : Renaming) :
    (body.weakenAt 1).rename embedding.lift.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  congr 1
  funext index
  cases index <;> rfl

theorem agreement {actual : Environment} {store middleStore nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) middleStore)
    (allocated : Evaluates (value :: actual) middleStore (allocation.rename embedding.lift) reference nextStore) :
    ContinuationAgreement actual store ((sequence output initializer allocation body).rename embedding)
      (reference :: value :: actual) nextStore
      (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) := by
  have combined := (ContinuationAgreement.bind (type := LocalLoop.controlType output)
    (body := .letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)) initialized).trans
    (ContinuationAgreement.letE allocated)
  simpa only [sequence, LanguageResult.bind, Expr.rename, body_rename, Renaming.lift] using combined

theorem smaller {actual : Environment} {store middleStore nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) middleStore)
    (allocated : Evaluates (value :: actual) middleStore (allocation.rename embedding.lift) reference nextStore)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((sequence output initializer allocation body).rename embedding) result finalStore) :
    ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (reference :: value :: actual) nextStore
      (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore := by
  have combined : EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType output) (initializer.rename embedding)
        (.letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)))
      result finalStore := by
    simpa only [sequence, LanguageResult.bind, Expr.rename, Renaming.lift] using completed
  obtain ⟨branchSize, branchSmaller, branch⟩ := combined.bind_success initialized
  obtain ⟨tailSize, tailSmaller, tail⟩ := branch.let_body allocated
  exact ⟨tailSize, Nat.lt_trans tailSmaller branchSmaller, body_rename body embedding ▸ tail⟩

theorem failure {actual : Environment} {store finalStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output payload : Ty} {reason : Word}
    (failed : Evaluates actual store (initializer.rename embedding) (.inLeft payload (.word reason)) finalStore) :
    Evaluates actual store ((sequence output initializer allocation body).rename embedding)
      (.inLeft (LocalLoop.controlType output) (.word reason)) finalStore := by
  rw [TypedLexicalControl.sequence_rename]
  exact LanguageResult.bind_failure _ failed

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotTyping
/-! Native typing of a generalized declaration's snapshot code. Inverting the
copies types the bundle initializer in the original scope, and the descriptor
allocation fixes the type of the cell the continuation binds. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotTyping
open Core Frontend SourceInference
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

/-- A scope slot holds a cell of its payload type in the scope's own context. -/
theorem scope_cell {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {index : Nat} {id : Resolved.LocalId} {payload : Ty} (found : scope[index]? = some (id, payload)) :
    (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some (.cell (OptionalCell.cellType payload)) := by
  rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
  simp [SourceCoreLocalCell.coreContext, found]

/-- A typed snapshot declaration types its bundle initializer in the original
context and its continuation below the descriptor cell. -/
theorem snapshot_children {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) request)
    (same : annotation.original = allocation.expression)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {payload type result : Ty}
    {initializer captured body : Expr} {definitions : DataEnvironment} {context : Core.Context}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope (fun index => index) (snapshotInner payload initializer annotation.expression) = .ok captured)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (cellPayload : Ty), scope[index]? = some (id, cellPayload) →
      context[index]? = some (.cell (OptionalCell.cellType cellPayload)))
    (typed : HasType context (snapshotSequence type captured body) result definitions) :
    (∃ initializerType, HasType context initializer initializerType definitions) ∧
      HasType (OptionalCell.referenceType request.payloadType :: context) body result definitions := by
  unfold snapshotSequence LanguageResult.bind at typed
  cases typed with
  | caseE capturedTyped _ next =>
    have inner := CaptureCopyTyping.copyScopeIndexed_body_hasType copied slots capturedTyped
    unfold snapshotInner LanguageResult.bind LanguageResult.success at inner
    cases inner with
    | caseE initializerTyped _ allocated =>
      cases allocated with
      | inRight _ allocationTyped =>
        have resultType := TypedLexicalWhile.Native.annotated_result allocation annotation same allocationTyped
        subst resultType
        exact ⟨⟨_, initializerTyped⟩, next⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareIndirectCalleeFaultBounds
/-! A semantic or nested stage fault in the actual callee stops the original
indirect parent before any gate or argument runs.
The strict staged child IH supplies the computation and its actual post once;
no full staged meaning or body/application law is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectCalleeFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- One failure receipt carries its exact tag, failing Scope and token through
the original sum bind. Actual transient effects remain in after/finalStore. -/
def ResultAt (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (token : Word)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
  RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
    faults (.fault failure) (.inLeft lowered.type (.word token)) ∧
  GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type (.fault failure) reached

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The genuine staged parent grade makes the executed callee strictly smaller.
Both semantic and nested stage failures propagate by the same original rule. -/
theorem preserves_callee_fault (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow bridge context model cells stages invocation certificate faults budget)
    {childSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      ResultAt (cells := cells) (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown evaluated
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨.calleeFault occurrence child, _, finalStore, finalMap, finalWorld, whole, .fault matched,
      finalHeaps, maps, worlds, frame, metadata, reached, related,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The supplied first-bind child is the original strict native computation.
Its independently returned staged Source grade grows by one parent step; the
failure tag/scope, token and exact reached caller state are unchanged. -/
theorem reflects_callee_fault (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow bridge context model cells stages invocation certificate faults budget)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize failure after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      ResultAt (cells := cells) (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown completed.sound
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨Staging.Recursive.Size.stepSize [sourceSize], _, after, finalMap, finalWorld,
      .calleeFault occurrence trace, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectCalleeFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareIndirectNativePrefix
/-! Whole-parent finite native inversion with the strict staged callee IH.
A semantic or nested stage callee fault produces the original parent. A value
retains its original gate and strict suffix for actual argument/application
producers. Source and native grades and the actual reached state remain
independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectNativePrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- A successful callee keeps the original full receiving-model payload and
its actual reached state. The following guard reads at that same store. -/
def CalleePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (carrier : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) finalStore ∧
  GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
  GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context calleeNode.type (.value sourceValue) reached

/-- A callee fault records the actual strict native child and independent
staged Source grade, and constructs the original parent at the same endpoint. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize failure token after finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareIndirectCalleeFaultBounds.ResultAt (cells := cells)
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial failure after token finalStore finalMap finalWorld

/-- A successful callee retains its actual staged trace/post and the original
second bind. Its suffix remains measured at the original strict native budget. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (cells := cells) (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functionModel compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The actual whole-parent completion yields its strict callee child. That
child uses the staged reflection IH once. Faults keep both exact failure tags;
values keep the original guard/suffix computation and the same reached state. -/
theorem reflects_prefix (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow bridge context model cells stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultPrefix (cells := cells) (registry := registry) (faults := faults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial budget value finalStore ∨
    ValuePrefix (cells := cells) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler prepared initial budget value finalStore := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child childStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      children _ childStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | @fault failure token matched =>
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown child.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      left
      refine ⟨_, sourceSize, failure, token, after, finalMap, finalWorld, child, childStrict,
        trace, .calleeFault occurrence trace, ?_, whole, .fault matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related,
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩
      rw [loweredType]
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      children _ childStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value represented =>
      right
      refine ⟨_, sourceSize, _, after, _, _, finalMap, finalWorld, child, childStrict, trace,
        ⟨child.sound, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩, ?_⟩
      cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed gate gateStrict => exact .failed gate gateStrict
      | continued gate suffixTrace gateStrict suffixStrict => exact .passed gate suffixTrace gateStrict suffixStrict

end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectNativePrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentPrefix
/-! The actual staged callee post constructs its original scoped boundary.
The first gate either constructs the exact staged rejection, retaining the
selected original row and exact token, or exposes the real argument helper.
That helper uses the ordered staged argument producer at the same reached
caller state. Application and diagnostic receiver transport follow separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CellAwareIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

include sourceEq found sourceParent tree unique parentTyped in
/-- Original parent typing and the actual ordered compiler tree determine the
raw callee and argument rows. The SourceParent requirements, output coercions
and physical-count cuts remain explicit for this exact compiler receipt. -/
theorem source_rows :
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      ExpressionsHaveTypes invocation.source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
      compiler.original.type = rawResult := by
  have rawTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have rawUnique : NodeOccurrencesUnique source := by
    simpa only [sourceEq] using unique
  have rawParentTyped : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent rawTree rawUnique rawParentTyped found
  exact ⟨rawParameter, rawResult, calleeFunction,
    by simpa only [sourceEq] using argumentsTyped, bundle, originalResult⟩

private theorem foldlApplication_ne_function
    (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (head_ne : ∀ parameter result, head ≠ .function parameter result)
    (parameter result : TypeSystem.Ty) :
    arguments.foldl TypeSystem.Ty.application head ≠ .function parameter result := by
  induction arguments generalizing head with
  | nil => exact head_ne parameter result
  | cons argument arguments induction =>
      exact induction (.application head argument)
        (by intro candidateParameter candidateResult equality; cases equality)

private theorem nominal_ne_function
    (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty)
    (parameter result : TypeSystem.Ty) :
    TypeSystem.Ty.nominal declaration arguments ≠ .function parameter result :=
  foldlApplication_ne_function (.constructor (.declaration declaration)) arguments
    (by intro candidateParameter candidateResult equality; cases equality) parameter result

private theorem value_is_function {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value := by
  cases value with
  | closure function => exact .closure function
  | global function => exact .global function
  | builtin function => exact .builtin function
  | constructed instantiation arguments =>
    rcases Dynamic.ValueHasType.constructed_inv typed with
      ⟨same, valid, _⟩ | ⟨_inner, impossible, _⟩
    · cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
        have impossible := same.trans resultType_eq
        exact False.elim ((nominal_ne_function dataType.id
          (ParameterSubstitution.orderedArguments instantiation.parameterSubstitution dataType.parameters)
          parameter result) impossible.symm)
    · cases impossible
  | unit | bool | word | integer | product | proxy | mapping => cases typed

include positive caller view originalUnique sourceEq found sourceParent tree unique parentTyped in
/-- The actual callee payload comes from the positive receiving model. Its
Source function type and reached admission supply genuine callable shape;
the original scoped boundary factory then runs at that same payload. -/
theorem scoped_boundary {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (cells := cells) (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  obtain ⟨_rawParameter, _rawResult, calleeFunction, _argumentsTyped, _bundle, _originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  obtain ⟨reached, _related, admitted⟩ := post.2.2.2.2.2.2.2
  have typedSource := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value admitted |>.1
  rw [calleeFunction] at typedSource
  have actualOrigin := SelectedCompilationCallableOrigins.Origins.origin
    (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (faults := semanticFaults) (profile := profile) post.2.1 (value_is_function typedSource)
  exact CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view compiler prepared
    caller view originalUnique actualOrigin

/-- The stage branch retains its actual invocation and occurrence, exact
selected original row/metadata and native word. Its diagnostic representation
is identified later by the receiving codebook, not by changing the failure. -/
def StageRejectedPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld originalNode originalMetadata reason,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (cells := cells) (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
      CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row ∧
      Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
        (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id
        (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word (dispatch.reason reason)) ∧ finalStore = calleeStore

/-- A real argument failure retains the cumulative reached state and full
receiving-model relation, with neither semantic nor nested stage tag changed. -/
def ArgumentFaultPrefix (value : Value) (finalStore : Store) : Prop :=
  ∃ calleeSize argumentsSize sourceValue calleeHeap failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareIndirectCalleeFaultBounds.ResultAt (cells := cells)
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functions compiler initial failure after token finalStore finalMap finalWorld

/-- Successful arguments retain their independent Source grade and actual
packed payload, raw callee/bundle/original-result rows, reached caller state
and strict original second-gate/application computation. No application trace
or body result is asserted here. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

private theorem argument_fault_post {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : CellAwareStagedExpressionSequence.PostAdmission bridge
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow
      bridge context model cells stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareIndirectNativePrefix.FaultPrefix (cells := cells)
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix (cells := cells) (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∨
    ArgumentFaultPrefix (cells := cells) (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix (cells := cells) (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CellAwareIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed initial admitted
      budget children completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        obtain ⟨_calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CellAwareStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CellAwareStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
/-- Source function typing excludes data-valued callees before direct dispatch. -/
theorem callable_shape {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value :=
  value_is_function typed

end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentFaultBounds
/-! The original indirect parent stops at a real argument failure. Its strict
callee and ordered argument hypotheses run at their actual reached states.
The first gate is reconstructed from the authentic scoped boundary; semantic
and nested stage failures retain the same tag, token and transient effects. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CellAwareIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include guardFrame in
omit positive in
/-- The real original row supplies first-gate success at the callee store.
No native acceptance or verdict is added to a compiler certificate. -/
theorem first_gate {sourceValue : Dynamic.Value} {carrier : Value}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (boundary : BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (calleeStore : Store) :
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore := by
  cases boundary with
  | user dispatch selected =>
      have passed := dispatch.accepted (by simpa only [guardFrame, prepared.call] using accepted)
      have read : Evaluates (carrier :: actual) calleeStore (.second (.var 0))
          (.word dispatch.contract) calleeStore := by
        exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
      have gate := prepared.site.dispatch_known .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
        dispatch.contract dispatch.row dispatch.found read
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments passed] at gate
      simpa only [CallableContract.resultValue] using gate
  | builtin receipt =>
      exact receipt.first_gate compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict Source descent constructs the callee and argument computations.
The argument fold runs after the accepted first gate and its actual effects
are the parent post; the second gate and application are never evaluated. -/
theorem preserves_argument_fault (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow
      bridge context model cells stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value} {calleeHeap after : Dynamic.Heap}
    {failure : Staging.Recursive.Failure}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id
      (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      CellAwareIndirectCalleeFaultBounds.ResultAt (cells := cells)
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      have calleePost : ∃ carrier, CalleePost (cells := cells) (registry := registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨_, calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := calleePost
      obtain ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
        calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := post
      obtain ⟨originalNode, originalMetadata, _contains, _form, _callView, boundary⟩ :=
        CellAwareIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
            calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨_rawParameter, _rawResult, _functionType, argumentsTyped, _bundle, _result⟩ :=
        CellAwareIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CellAwareStagedExpressionSequence.preserves_fault bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := first_gate (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      have whole : Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
          (.inLeft compiler.resultType (.word token)) finalStore := by
        apply LanguageResult.bind_success compiler.resultType calleeEvaluated
        apply LanguageResult.bind_success compiler.resultType gate
        apply LanguageResult.bind_failure compiler.resultType
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context compiler.original.type (.fault failure) reached := by
        cases failure with
        | semantic reason => exact ⟨postAdmission.rows, by intro _ impossible; cases impossible⟩
        | stage origin call reason => exact postAdmission.rows
      exact ⟨.argumentsFault occurrence calleeTrace accepted argumentsTrace,
        token, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related, parentAdmission⟩

omit positive in
/-- The constructive whole argument-prefix reflection already contains the
actual parent trace and reached failure receipt. This branch exposes the
independent Source grade without rebuilding or relabeling the child failure. -/
theorem reflects_argument_fault_prefix {value : Value} {finalStore : Store}
    (reflected : CellAwareIndirectArgumentPrefix.ArgumentFaultPrefix (cells := cells) (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (faults := faults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore) :
    ∃ sourceSize failure after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CellAwareIndirectCalleeFaultBounds.ResultAt (cells := cells)
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, _sourceValue, _calleeHeap, failure, after, token, finalMap, finalWorld,
    _callee, _accepted, _arguments, parent, sameValue, result⟩ := reflected
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize], failure, after, token,
    finalMap, finalWorld, parent, sameValue, result⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectArgumentFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareIndirectValuesPrefix
/-! Source preservation constructs the callee and ordered argument prefix
at their actual reached states. It retains callee typing and its complete
post for builtin and user application. The application itself follows later. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectValuesPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CellAwareIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


/-- Both native prefix actions use the same represented callee and argument
packet. The callee post is retained before the argument effects are composed. -/
def ValuesPrefix (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeStore calleeMap calleeWorld carrier values argumentsStore finalMap finalWorld
      originalNode originalMetadata,
    CalleePost (cells := cells) (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore ∧
    Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes
      (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached

include positive prepared sourceEq certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict callee preservation and the real ordered argument fold construct
the full prefix once. The returned admission belongs to the argument endpoint. -/
theorem preserves_values (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow
      bridge context model cells stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {sources : List Dynamic.Value}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    ValuesPrefix (cells := cells) (functionModel := functionModel) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      rename_i carrier
      have post : CalleePost (cells := cells) (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := calleeNode) bridge functions compiler initial
          sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      have sourceValueTyped : Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type :=
        calleeAdmission.at_value.1
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CellAwareIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      obtain ⟨rawParameter, rawResult, functionType, argumentsTyped, bundle, resultType⟩ :=
        CellAwareIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, finalMap, finalWorld, argumentsEvaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CellAwareStagedExpressionSequence.preserves_values bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := CellAwareIndirectArgumentFaultBounds.first_gate
        (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeStore, calleeMap, calleeWorld,
        carrier, values, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
        post, sourceValueTyped, gate, argumentsEvaluated, represented,
        GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related,
        postAdmission.at_values⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectValuesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareParameterMeaning
/-! Actual marked parameter allocation retains all generalized descriptor
cells in the input heap and reaches the original native body continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareParameterMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning (Arguments)

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
theorem Tree.prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      (∃ suffix, finalStore = store ++ suffix) ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, ⟨[], by simp⟩, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, .refl _ _ _⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _capturedSlots, _capturedTyped, allocationEval, nextHeaps, nextReference, frame⟩ :=
        CallableIndexedCellAllocation.preserves_with_captures allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl)
          (ordinaryCells.inject (.initialized head)) (.ordinary Dynamic.Heap.Allocates.append)
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, storeExtension, finalSourceLayout, finalActualLayout, spine, agreement⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, ?_, finalActualLayout, ?_, ?_⟩
      · obtain ⟨suffix, storeEq⟩ := storeExtension
        exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE renamedAllocation)

end Solcore.SourceSemantics.CoreLowering.CellAwareParameterMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareTerminalMetadataBodyBounds
/-! Actual lambda metadata views preserve terminal statements literally.
Complete original body typing determines the used child and declared result;
strict expression hypotheses then construct both body directions at the same
reached parameter state. No execution law is part of the static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalMetadataBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
  {invocation : Staging.Recursive.Scope}
  (view : LambdaMetadataViews.MetadataView invocation.source compilerSource)

include receipt view in
/-- The genuine metadata relation retains each complete statement node.
It does not identify arbitrary expression output types or coercion paths. -/
theorem source_head : Head invocation expression statements := by
  cases receipt.terminal with
  | returning rest found form =>
    exact .returning rest (lookupStatement?_sound (view.statement found)) form
  | tail found form =>
    exact .tail (lookupStatement?_sound (view.statement found)) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
  {context staticFinal : SourceSemantics.Context} {expected : TypeSystem.Ty} {facts : BodyFacts}
  {registry : Staging.Recursive.Registry}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (bodyTyped : StatementsHaveType invocation.source { returnType := expected }
    context statements staticFinal facts)
  (complete : BodyCompletes expected facts)
  (certifies : ∀ child, policy.lowerExpression receipt.childFuel compilerSource scope expression reasonAt = .ok child →
    certificate scope expression child)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- Original whole-body trace, complete Source typing and the literal receipt
construct the used strict expression step and full body post internally. -/
theorem preserves_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow
      bridge context model cells registry invocation certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment
      before statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult expected bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected outcome reached := by
  have head := source_head receipt view
  obtain ⟨node, found, sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped complete
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique head trace
  have sameOutcome : outcome = childOutcome :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt ξ]
  obtain ⟨_sourceTrace, _sourceResult, meaning⟩ :=
    CellAwareStagedTerminalBody.preserves bridge head
      (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
      budget children escaped
      ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
      child (sameSize ▸ within)
  simpa only [sameType, receipt.sameType] using meaning

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- The literal emitted body exposes a strict native child. Its reflection
constructs a separately graded original body and the same reached full post. -/
theorem reflects_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow
      bridge context model cells registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult expected (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected outcome reached := by
  have head := source_head receipt view
  obtain ⟨node, found, sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped complete
  rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt ξ] at completed
  have meaning := CellAwareStagedTerminalBody.reflects bridge head
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
    completed within
  simpa only [sameType, receipt.sameType] using meaning

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalMetadataBodyBounds
end
