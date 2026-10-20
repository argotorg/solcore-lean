import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLambdaParameters

/-! Actual overload selection and call-node recording preserve the privacy
proved for the retained candidate and its real requirement batch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem selectFunctionCandidateFrom_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  obtain ⟨signature, member, tried⟩ := Detail.selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_private catalog (cataloged member) ready bound argumentsBelow expectedBelow
    argumentsSafe expectedSafe live tried

private theorem attach_fields (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).inference = state.inference ∧
      (Detail.attachExpressionCoercions state entries).localBinders = state.localBinders ∧
      (Detail.attachExpressionCoercions state entries).requirements = state.requirements := by
  induction entries generalizing state with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => Detail.appendExpressionCoercions node entry.coercions))

/-- The real recording fold modifies only occurrence/node metadata; it
retains the candidate's inferred type and exact requirement ledger. -/
theorem recordSelectedCall_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult)
    (safe : Safe protectedVars attempt.state attempt.result.type)
    (live : LiveBindersSafe protectedVars attempt.state) :
    let result := Detail.recordSelectedCall source callee name arguments attempt
    SafeTransport protectedVars attempt.state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = attempt.state.requirements := by
  dsimp only
  have fields := attach_fields attempt.state attempt.argumentCoercions
  have inference : (Detail.recordSelectedCall source callee name arguments attempt).2.inference = attempt.state.inference := fields.1
  have binders : (Detail.recordSelectedCall source callee name arguments attempt).2.localBinders = attempt.state.localBinders := fields.2.1
  have transport : SafeTransport protectedVars attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  exact ⟨transport, transport _ safe, live.transport binders transport, fields.2.2⟩

/-- Indirect-call recording similarly retains the accepted application's
state and output type, including its already committed coercion requirements. -/
theorem recordIndirectCall_private {protectedVars : List TypeVarId}
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : Detail.IndirectApplicationResult)
    (safe : Safe protectedVars application.state application.result.type)
    (live : LiveBindersSafe protectedVars application.state) :
    let result := Detail.recordIndirectCall source callee arguments application
    SafeTransport protectedVars application.state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = application.state.requirements := by
  dsimp only
  have transport : SafeTransport protectedVars application.state (Detail.recordIndirectCall source callee arguments application).2 :=
    .of_substitution_eq rfl
  exact ⟨transport, transport _ safe, live.transport rfl transport, rfl⟩

/-- Binary overloads may fit the candidate output once more. Recording
preserves this actual fitted state and output, including its new requirements. -/
theorem recordSelectedCallResult_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State)
    (safe : Safe protectedVars state result.type)
    (live : LiveBindersSafe protectedVars state) :
    let recorded := Detail.recordSelectedCallResult source callee name arguments attempt result coercions state
    SafeTransport protectedVars state recorded.2 ∧ Safe protectedVars recorded.2 recorded.1.type ∧
      LiveBindersSafe protectedVars recorded.2 ∧ recorded.2.requirements = state.requirements := by
  dsimp only
  have fields := attach_fields state attempt.argumentCoercions
  have inference : (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2.inference = state.inference := fields.1
  have binders : (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2.localBinders = state.localBinders := fields.2.1
  have transport : SafeTransport protectedVars state (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2 :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  exact ⟨transport, transport _ safe, live.transport binders transport, fields.2.2⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
