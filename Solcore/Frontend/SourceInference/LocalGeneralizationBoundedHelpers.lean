import Solcore.Frontend.SourceInference.LocalGeneralizationRetainedStatements
import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedInitialization
import Solcore.Frontend.SourceInference.LocalReadScopeHelpers

/-! Actual helper computations introduce no declaration events. Their genuine
ledger and lexical-scope receipts transport already recorded boundaries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail

namespace Progress

theorem of_unchanged {before after : State}
    (nodes : after.nodes = before.nodes) (binders : after.localBinders = before.localBinders)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after) : Progress before after :=
  of_nodes_eq nodes reads scope (fun below => State.LocalBindersBelowNextLocal.transport binders scope.next below)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress state next :=
  of_unchanged (unify_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (LocalReadEvents.Progress.unify accepted) (LocalReadScopeProgress.Progress.unify accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) : Progress state result.state :=
  of_unchanged (withExpected_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope accepted))
    (LocalReadEvents.Progress.withExpected accepted) (LocalReadScopeProgress.Progress.withExpected accepted)

theorem selectFunctionCandidateFrom {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerLiteralOrigins
      call expected state = .ok result) : Progress state result.state :=
  of_unchanged (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted))
    (LocalReadEvents.Progress.selectFunctionCandidateFrom accepted)
    (LocalReadScopeProgress.Progress.selectFunctionCandidateFrom accepted)

theorem inferUnaryOperator {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (inferUnaryOperator_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (LocalReadEvents.Progress.inferUnaryOperator accepted) (LocalReadScopeProgress.Progress.inferUnaryOperator accepted)

theorem inferBinaryOperator {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (inferBinaryOperator_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (LocalReadEvents.Progress.inferBinaryOperator accepted) (LocalReadScopeProgress.Progress.inferBinaryOperator accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_unchanged (applyFunctionType_occurrenceState_eq accepted).1
    (congrArg LexicalScope.binders (localReadScope_applyFunctionType_lexicalScope accepted))
    (LocalReadEvents.Progress.applyFunctionType accepted) (LocalReadScopeProgress.Progress.applyFunctionType accepted)

theorem fresh (state : State) : Progress state state.fresh.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.fresh _)

theorem allocateExpressionId (state : State) : Progress state state.allocateExpressionId.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.refl _)

theorem allocateStatementId (state : State) : Progress state state.allocateStatementId.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.refl _)

theorem allocateHiddenLocal (state : State) : Progress state state.allocateHiddenLocal.2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.allocateHiddenLocal _)

theorem allocateBinder (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool) (requirements : List LocalSchemeRequirement) :
    Progress state (state.allocateBinder name scheme span comptime requirements).2 :=
  of_nodes_eq rfl (LocalReadEvents.Progress.of_nodes_eq rfl (State.DirectRequirementsProgress.refl _))
    (LocalReadScopeProgress.Progress.allocateBinder _ _ _ _ _ _)
    (State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (LocalReadEvents.Progress.freshTypes _ _)
    (LocalReadScopeProgress.Progress.freshTypes _ _)
    (Detail.freshTypes_preserves_localBindersBelowNextLocal _ _)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (LocalReadEvents.Progress.freshDataConstructorInstantiation _ _ _)
    (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation _ _ _)
    (Detail.freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal _ _ _)

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 :=
  of_unchanged rfl rfl (LocalReadEvents.Progress.addRequirementWithId _ _)
    (LocalReadScopeProgress.Progress.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _)
    (LocalReadEvents.Progress.addRequirementsWithIds _ _) (LocalReadScopeProgress.Progress.addRequirementsWithIds _ _)
    (State.addRequirementsWithIds_preserves_localBindersBelowNextLocal _ _)


theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 := by
  apply of_retained (RetainedStatements.recordExpressionWithExpected accepted)
    (LocalReadEvents.Progress.recordExpressionWithExpected accepted nonlocal)
    (LocalReadScopeProgress.Progress.recordExpressionWithExpected accepted nonlocal)
  intro below
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (withExpected fit).binders below

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  apply of_retained ?_ (LocalReadEvents.Progress.localIdentifier form allocation found accepted)
    (LocalReadScopeProgress.Progress.localIdentifier form allocation found accepted)
    (fun below => inferExprFuel_preserves_localBindersBelowNextLocal below accepted)
  have retained := RetainedStatements.recordExpressionWithExpected
    (Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
  rw [State.addRequirementsWithIds_nodes] at retained
  have allocationState : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  simpa only [RetainedStatements, allocationState, State.allocateExpressionId_nodes] using retained

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : Progress state (state.modifyStatementNode id modify) :=
  of_retained (RetainedStatements.modifyStatementNode state id modify forms)
    (LocalReadEvents.Progress.modifyStatementNode _ _ _)
    (LocalReadScopeProgress.Progress.modifyStatementNode _ _ _) (fun below => below)

private theorem attachExpressionCoercions_binders (state : State) (entries : List ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).localBinders = state.localBinders := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  have scope := LocalReadScopeProgress.Progress.recordSelectedCallResult source callee name arguments attempt result trailing state
  apply of_retained (RetainedStatements.recordSelectedCallResult _ _ _ _ _ _ _ _)
    (LocalReadEvents.Progress.recordSelectedCallResult _ _ _ _ _ _ _ _) scope
  intro below
  apply State.LocalBindersBelowNextLocal.transport (before := state) ?_ scope.next below
  change (Detail.attachExpressionCoercions state attempt.argumentCoercions).localBinders = state.localBinders
  exact attachExpressionCoercions_binders _ _

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  of_retained (RetainedStatements.recordExpression _ _ _ _ _ _ _)
    (LocalReadEvents.Progress.recordIndirectCall _ _ _ _) (LocalReadScopeProgress.Progress.recordIndirectCall _ _ _ _)
    (fun below => below)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
