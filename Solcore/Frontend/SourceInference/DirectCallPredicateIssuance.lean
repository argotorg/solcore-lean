import Solcore.Frontend.SourceInference.CatalogedDirectCallCandidate

/-! Selected declaration candidates retain their actual ordered raw
requirement IDs and predicates before any source body typing theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.DirectCallPredicateEvents
open TypeSystem Detail

theorem tryFunctionCandidate_correspond
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      result.instantiation.predicates result.signatureRequirements := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals exact State.addRequirementsWithIds_correspond _ _

theorem selectFunctionCandidateFrom_correspond
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    RequirementPredicatesCorrespond result.state.requirements
      result.instantiation.predicates result.signatureRequirements := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_correspond selected

end Solcore.Frontend.SourceInference.DirectCallPredicateEvents
