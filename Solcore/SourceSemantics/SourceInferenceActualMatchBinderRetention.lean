import Solcore.SourceSemantics.SourceInferenceActualBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualMatchCompletion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem statement_match_default
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      {body : Syntax.Block} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
      (default : arms.value.defaultBody = some body)
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  unfold matchCompletion at completion
  simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
  split at completion
  · contradiction
  · cases Except.ok.inj completion
    exact .append _ _


theorem statement_match_cases
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)  :
    BindersRetained (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
    unfold matchCompletion at completion
    simp only [child, defaultEq, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
    split at completion
    · contradiction
    · cases Except.ok.inj completion
      exact .append _ _
  | some body =>
    cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
    | error error => simp [matchCompletion, child, defaultEq, bodyAccepted, bind, Except.bind] at completion
    | ok bodyResult =>
      exact (inferStatementsFuel_origins_progress bodyAccepted).retained.trans
        (statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted)

private theorem afterScrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState)) :
    BindersRetained scrutineeState.nodes result.state.nodes := by
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
    exact (inferMatchCasesFuel_origins_progress casesAccepted).retained.trans
      (statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted)

theorem statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context scrutinee none allocated value childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by simpa only [matchScrutinee, single] using child
  exact afterScrutinee accepted form allocation scrutineeAccepted


theorem statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)  :
    BindersRetained (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
  let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
    id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
    unfold matchScrutinee
    split
    · rename_i sourceEq
      exact False.elim (multiple _ sourceEq)
    · simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
  exact (BindersRetained.append _ _).trans (afterScrutinee accepted form allocation scrutineeAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
