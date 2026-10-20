import Solcore.Frontend.SourceInference.DirectCallOriginsProgress

/-! Selected candidate batches are exactly the signature identities recorded
on their real declaration-call node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.DirectCallEvents
open TypeSystem Detail

private theorem candidateWithExpected_direct_unchanged
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : candidateWithExpected context state actual expected = .ok (some result)) :
    Unchanged state result.state := by
  unfold candidateWithExpected at accepted
  cases fitted : withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    subst result
    exact withExpected_direct_eq fitted
  | error error =>
    cases error <;> simp_all
    rename_i error
    cases error <;> simp_all

private theorem fitArguments_direct_unchanged
    {context : Context} {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : ArgumentFitResult}
    (accepted : fitArguments context state arguments parameters = .ok (some result)) :
    Unchanged state result.state := by
  induction arguments generalizing state parameters result with
  | nil =>
    cases parameters <;> simp_all [fitArguments]
    subst result
    rfl
  | cons argument arguments ih =>
    cases parameters with
    | nil => simp [fitArguments] at accepted
    | cons parameter parameters =>
      unfold fitArguments at accepted
      cases fitted : candidateWithExpected context state argument (some parameter) with
      | error error => simp [fitted, bind, Except.bind] at accepted
      | ok value =>
        cases value with
        | none => simp [fitted, bind, Except.bind] at accepted
        | some fit =>
          simp only [fitted, bind, Except.bind] at accepted
          cases remaining : fitArguments context fit.state arguments parameters with
          | error error => simp [remaining] at accepted
          | ok value =>
            cases value with
            | none => simp [remaining] at accepted
            | some tail =>
              simp only [remaining, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at accepted
              subst result
              exact Unchanged.trans (candidateWithExpected_direct_unchanged fitted)
                (ih (result := tail) remaining)

theorem tryFunctionCandidate_direct_batch
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.directCallRequirements = state.directCallRequirements ++ result.signatureRequirements := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals have argumentsSame := fitArguments_direct_unchanged (by assumption)
  all_goals have resultSame := candidateWithExpected_direct_unchanged (by assumption)
  all_goals
    change _ ++ _ = _
    rw [State.addRequirementsWithIds_direct_eq, resultSame, argumentsSame]

theorem selectFunctionCandidateFrom_direct_batch
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.directCallRequirements = state.directCallRequirements ++ result.signatureRequirements := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_direct_batch selected

/-- Recording the selected call discharges exactly its pending signature batch. -/
theorem recordSelectedCallResult_pending
    {before state : State} {attempt : CandidateAttemptResult}
    (nodes : state.nodes = before.nodes)
    (direct : state.directCallRequirements = before.directCallRequirements ++ attempt.signatureRequirements)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (result : InferredExpression) (trailing : List CoercionStep) :
    Progress before (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  rw [recordSelectedCallResult_direct_unchanged, direct] at member
  rcases List.mem_append.mp member with prior | fresh
  · have original : HasCall state.nodes requirement := by
      rw [nodes]
      exact origins requirement prior
    apply (original.attachExpressionCoercions attempt.argumentCoercions).mono
    intro node present
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · let calleeId := (Detail.attachExpressionCoercions state attempt.argumentCoercions).allocateExpressionId.1
    let callNode : ExpressionNode := {
      id := result.id, span := source.span, type := result.type
      form := .call calleeId (arguments.map (·.id)) (.declaration attempt.instantiation)
      requirements := coercionRequirements attempt.callCoercions ++ attempt.signatureRequirements ++
        coercionRequirements trailing
      coercions := attempt.callCoercions ++ trailing }
    refine ⟨callNode, ?_, calleeId, arguments.map (·.id), attempt.instantiation, rfl, ?_⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ fresh)

namespace Progress

theorem selectAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (source callee : Syntax.Expr) :
    Progress state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_pending (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_batch accepted) source callee name arguments _ _

theorem selectFitAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected selectedExpected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {fitted : ExpectationResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call selectedExpected state = .ok attempt)
    (fit : Detail.withExpected context attempt.state attempt.result expected = .ok fitted)
    (source callee : Syntax.Expr) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt
      fitted.expression fitted.coercions fitted.state).2 :=
  recordSelectedCallResult_pending
    ((withExpected_occurrenceState_eq fit).1.trans (selectFunctionCandidateFrom_occurrenceState_eq accepted).1)
    ((withExpected_direct_eq fit).trans (selectFunctionCandidateFrom_direct_batch accepted))
    source callee name arguments _ _

end Progress
end Solcore.Frontend.SourceInference.DirectCallEvents
