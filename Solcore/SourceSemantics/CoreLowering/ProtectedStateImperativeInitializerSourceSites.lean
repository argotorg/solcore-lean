import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds

/-! Original Source initializer syntax and item typing retain the pending
condition, body, and post facts. Finite projections follow the same static
binder contexts; the catalog fold supplies its existing recursion. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeInitializerSourceSites
open Frontend SourceInference
open ProtectedStateImperativeCatalogReady

def Facts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ (control : SourceSemantics.ControlContext) (final bodyFinal : SourceSemantics.Context)
    (bodyFacts : SourceSemantics.BodyFacts) (postFinal : SourceSemantics.Context),
    GenericImperativeMatch.Syntax source expressionSyntax context
      (.initializers items condition post statements) expected ∧
    ForItemsHaveType source control context items final ∧
    ExpressionHasType source final condition .bool ∧
    StatementsHaveType source control.enterLoop final statements bodyFinal bodyFacts ∧
    ForItemsHaveType source control.enterLoop final post postFinal

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

theorem done {context : SourceSemantics.Context} {condition : ExpressionId}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context [] condition post statements expected) :
    CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax context condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, _conditionTyped, bodyTyped, postTyped⟩ := facts
  cases typed
  exact CallableIndexedOwnedAdmittedForBounds.LoopFacts.of_done syntaxTree bodyTyped postTyped

theorem absent {context next : SourceSemantics.Context} {binder : TypedBinder}
    {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context (.letDecl binder none :: rest) condition post statements expected)
    (extended : BinderExtends source.owner context binder next) :
    Facts source expressionSyntax next rest condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, conditionTyped, bodyTyped, postTyped⟩ := facts
  cases syntaxTree with
  | initializerUninitialized _ _ syntaxExtended _ remaining =>
    cases typed with
    | cons head tail =>
      cases head with
      | letUninitialized _ _ typedExtended =>
        exact ⟨control, final, bodyFinal, bodyFacts, postFinal,
          Dynamic.BinderExtends.functional syntaxExtended extended ▸ remaining,
          Dynamic.BinderExtends.functional typedExtended extended ▸ tail,
          conditionTyped, bodyTyped, postTyped⟩

theorem initialized {context next : SourceSemantics.Context} {binder : TypedBinder} {expression : ExpressionId}
    {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context (.letDecl binder (some expression) :: rest) condition post statements expected)
    (extended : BinderExtends source.owner context binder next) :
    Facts source expressionSyntax next rest condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, conditionTyped, bodyTyped, postTyped⟩ := facts
  cases syntaxTree with
  | initializerInitialized _ mono syntaxExtended _ _ _ _ _ remaining =>
    cases typed with
    | cons head tail =>
      cases head with
      | letInitialized _ _ _ typedExtended =>
        exact ⟨control, final, bodyFinal, bodyFacts, postFinal,
          Dynamic.BinderExtends.functional syntaxExtended extended ▸ remaining,
          Dynamic.BinderExtends.functional typedExtended extended ▸ tail,
          conditionTyped, bodyTyped, postTyped⟩
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)

theorem discard {context : SourceSemantics.Context} {expression : ExpressionId}
    {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context (.expression expression :: rest) condition post statements expected) :
    Facts source expressionSyntax context rest condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, conditionTyped, bodyTyped, postTyped⟩ := facts
  cases syntaxTree with
  | initializerDiscard _ _ _ remaining =>
    cases typed with
    | cons head tail => cases head; exact ⟨control, final, bodyFinal, bodyFacts, postFinal, remaining, tail, conditionTyped, bodyTyped, postTyped⟩

theorem assignment {context : SourceSemantics.Context} {resolution : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List ForItemForm}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context (.assignValue resolution operator rhs :: rest) condition post statements expected) :
    Facts source expressionSyntax context rest condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, conditionTyped, bodyTyped, postTyped⟩ := facts
  cases syntaxTree with
  | initializerAssign _ _ _ _ _ remaining =>
    cases typed with
    | cons head tail => cases head; exact ⟨control, final, bodyFinal, bodyFacts, postFinal, remaining, tail, conditionTyped, bodyTyped, postTyped⟩

theorem snapshot {context : SourceSemantics.Context} {resolution : AssignmentResolution}
    {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : Facts source expressionSyntax context (.assignBitNot resolution :: rest) condition post statements expected) :
    Facts source expressionSyntax context rest condition post statements expected := by
  obtain ⟨control, final, bodyFinal, bodyFacts, postFinal, syntaxTree, typed, conditionTyped, bodyTyped, postTyped⟩ := facts
  cases syntaxTree with
  | initializerBitNot _ _ _ remaining =>
    cases typed with
    | cons head tail => cases head; exact ⟨control, final, bodyFinal, bodyFacts, postFinal, remaining, tail, conditionTyped, bodyTyped, postTyped⟩

theorem sites : InitializerSites (Facts source expressionSyntax)
    (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax) source :=
  ⟨done, absent, initialized, discard, assignment, snapshot⟩

theorem for_parent {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements) :
    Facts source expressionSyntax context items condition post statements expected := by
  obtain ⟨mode, rest, syntaxTree, typed⟩ := facts
  obtain ⟨control, final, postFinal, bodyFinal, bodyFacts, itemTyped, conditionTyped, bodyTyped, postTyped⟩ :=
    ProtectedStateImperativeTypedSourceSites.for_loop unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form
  cases syntaxTree
  case forLoop initial remaining =>
    simp_all
    exact ⟨control, final, bodyFinal, bodyFacts, postFinal, initial, itemTyped, conditionTyped, bodyTyped, postTyped⟩
  case body syntaxTree => cases syntaxTree <;> simp_all
  all_goals simp_all

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeInitializerSourceSites
