import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceActualMatchCompletion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

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
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child).inputs inputs).progress child).2.1
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  unfold matchCompletion at completion
  simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
  split at completion
  · contradiction
  · cases Except.ok.inj completion
    exact .of_inference_eq ready.solved rfl

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
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child).inputs inputs).progress child).2.1
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
    unfold matchCompletion at completion
    simp only [child, defaultEq, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
    split at completion
    · contradiction
    · cases Except.ok.inj completion
      exact .of_inference_eq ready.solved rfl
  | some body =>
    cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
    | error error => simp [matchCompletion, child, defaultEq, bodyAccepted, bind, Except.bind] at completion
    | ok bodyResult =>
      have bodyProgress := ((ChildStep.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted).inputs inputs).progress bodyAccepted
      exact bodyProgress.1.trans (statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted inputs)

private theorem afterScrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (inputs : (CallIndex.statement (fuel+1) context source expectedReturn initial result).Inputs)
    (ready : scrutineeState.InferenceReady) : scrutineeState.InferenceProgress result.state := by
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
    have after := ((ChildStep.statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted).inputs inputs).progress casesAccepted
    have hiddenProgress : scrutineeState.InferenceProgress hiddenState := .of_inference_eq ready.solved rfl
    exact hiddenProgress.trans (after.1.trans (statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted inputs))

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
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context scrutinee none allocated value childFinal).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_single accepted form allocation single child).inputs inputs).progress child).2.1
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by simpa only [matchScrutinee, single] using child
  exact afterScrutinee accepted form allocation scrutineeAccepted inputs ready

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
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_many accepted form allocation multiple child).inputs inputs).progress child).2.1
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
  have tupleReady : tupleState.InferenceReady := ready.allocateExpressionId.recordNode _
  have tupleProgress : childFinal.InferenceProgress tupleState := .of_inference_eq ready.solved rfl
  exact tupleProgress.trans (afterScrutinee accepted form allocation scrutineeAccepted inputs tupleReady)

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
