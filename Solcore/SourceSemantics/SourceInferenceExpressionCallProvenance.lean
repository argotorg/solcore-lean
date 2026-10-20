import Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness
import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! Successful call dispatch retains the actual constructor exclusion and
indirect-callee branch tests needed to identify its immediate child calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem

inductive CallExpressionDispatchProvenanceFacts
    (context : Frontend.SourceInference.Context)
    (source callee : Syntax.Expr)
    (arguments : Syntax.DelimitedList Syntax.Expr)
    (id : ExpressionId) (expected : Option TypeSystem.Ty)
    (fuel : Nat) (allocated : Frontend.SourceInference.State)
    (result : InferredExpression × Frontend.SourceInference.State) : Prop where
  | constructor
      {dataType : ProgramDataSignature}
      {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation}
      {constructorState : Frontend.SourceInference.State}
      (discovery : Detail.constructorCalleeCandidates context allocated callee =
        .ok [(dataType, constructor)])
      (freshInstantiation :
        Detail.freshDataConstructorInstantiation dataType constructor allocated =
          (instantiation, constructorState))
      (application : Detail.inferConstructorApplicationFuel fuel context source
        id instantiation arguments.elements expected constructorState =
          .ok result) :
      CallExpressionDispatchProvenanceFacts context source callee arguments id expected
        fuel allocated result
  | selected
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {candidates : List ProgramFunctionSignature}
      {integerLiterals : List IntegerLiteralOrigin}
      {attempt : Detail.CandidateAttemptResult}
      (nonconstructor : Detail.constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (candidateOrigin :
        SelectedCallCandidatesOrigin context name candidates)
      (selection : Detail.selectFunctionCandidateFrom context name candidates
        inferredArguments integerLiterals id expected argumentState =
          .ok attempt)
      (recording : Detail.recordSelectedCall source callee name
        inferredArguments attempt = result) :
      CallExpressionDispatchProvenanceFacts context source callee arguments id expected
        fuel allocated result
  | builtin
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {function : BuiltinFunctionId}
      (nonconstructor : Detail.constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (recording : Detail.recordBuiltinFunctionCall source callee name function
        inferredArguments id expected argumentState = .ok result) :
      CallExpressionDispatchProvenanceFacts context source callee arguments id expected
        fuel allocated result
  | indirect
      {inferredArguments : List InferredExpression}
      {argumentState calleeState : Frontend.SourceInference.State}
      {inferredCallee : InferredExpression}
      {application : Detail.IndirectApplicationResult}
      (nonconstructor : Detail.constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (indirect : SourceInferenceExecution.IndirectCalleeAt context callee argumentState)
      (calleeSuccess : Detail.inferExprFuel fuel context callee none
        argumentState = .ok (inferredCallee, calleeState))
      (applicationSuccess : Detail.applyFunctionType context id
        inferredCallee.type inferredArguments expected calleeState =
          .ok application)
      (recording : Detail.recordIndirectCall source inferredCallee
        inferredArguments application = result) :
      CallExpressionDispatchProvenanceFacts context source callee arguments id expected
        fuel allocated result

/-- Invert a successful source call into the exact semantic tail executed by
the frontend. -/
theorem inferExprFuel_success_call_dispatch_provenance_facts
    {fuel : Nat}
    {context : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : source.value = .call callee arguments)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context source expected initial =
      .ok result) :
    CallExpressionDispatchProvenanceFacts context source callee arguments id expected
      fuel allocated result := by
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates context allocated callee with
  | error error =>
      simp [discovery] at success
  | ok candidates =>
      cases candidates with
      | nil =>
          simp only [discovery] at success
          repeat' first | split at success
          all_goals
            try simp_all [pure, Pure.pure, Except.pure]
          all_goals
            first
            | apply CallExpressionDispatchProvenanceFacts.indirect
              · exact discovery
              · assumption
              · simp_all [SourceInferenceExecution.IndirectCalleeAt]
              · assumption
              · assumption
              · assumption
            | apply CallExpressionDispatchProvenanceFacts.builtin <;> assumption
            | apply CallExpressionDispatchProvenanceFacts.selected
              · exact discovery
              · assumption
              · first
                | apply SelectedCallCandidatesOrigin.qualified <;> assumption
                | apply SelectedCallCandidatesOrigin.unqualified <;> assumption
              · assumption
              · assumption
      | cons first rest =>
          rcases first with ⟨dataType, constructor⟩
          cases rest with
          | nil =>
              simp only [discovery] at success
              generalize freshEq :
                Detail.freshDataConstructorInstantiation dataType constructor
                  allocated = pair at success
              rcases pair with ⟨instantiation, constructorState⟩
              exact .constructor discovery freshEq success
          | cons second tail =>
              simp [discovery] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
