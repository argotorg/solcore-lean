import Solcore.SourceSemantics.SourceInferenceProtectedVariableCandidates
import Solcore.SourceSemantics.SourceInferenceProtectedVariableApplications
import Solcore.SourceSemantics.SourceInferenceProtectedVariableBuiltins
import Solcore.SourceSemantics.SourceInferenceProtectedVariableReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem selectFunctionCandidateFrom_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    FixesProtected protectedVars result.state := by
  obtain ⟨signature, member, tried⟩ := Detail.selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_fixes_protected catalog (cataloged member) ready bound argumentsBelow
    argumentsSafe expectedSafe live fixed tried

private theorem attach_inference (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).inference = state.inference := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => Detail.appendExpressionCoercions node entry.coercions))

theorem recordSelectedCall_fixes_protected {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult)
    (fixed : FixesProtected protectedVars attempt.state) :
    FixesProtected protectedVars (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  fixed.of_substitution_eq (congrArg InferState.substitution (attach_inference _ _))

theorem recordSelectedCallResult_fixes_protected {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State)
    (fixed : FixesProtected protectedVars state) :
    FixesProtected protectedVars (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2 :=
  fixed.of_substitution_eq (congrArg InferState.substitution (attach_inference _ _))

theorem recordIndirectCall_fixes_protected {protectedVars : List TypeVarId}
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : Detail.IndirectApplicationResult)
    (fixed : FixesProtected protectedVars application.state) :
    FixesProtected protectedVars (Detail.recordIndirectCall source callee arguments application).2 :=
  fixed.of_substitution_eq rfl

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
