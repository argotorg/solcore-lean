import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeExpressionSteps

/-! Actual operator and selected-call suffixes preserve a generalization
created by a child. Each step uses the accepted compiler computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem unaryOperator
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operand : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {result : OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (operandBelow : operand.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (operandSafe : Safe binder.scheme.quantified state operand)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferUnaryOperator context operator operand expected integerLiterals state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferUnaryOperator_private catalog ready operandBelow expectedBelow
    operandSafe expectedSafe lifetime.live accepted
  have properties := inferUnaryOperator_inferenceProperties ready operandBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem binaryOperator
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {result : OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (leftSafe : Safe binder.scheme.quantified state left)
    (rightSafe : Safe binder.scheme.quantified state right)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferBinaryOperator_private catalog ready leftBelow rightBelow expectedBelow
    leftSafe rightSafe expectedSafe lifetime.live accepted
  have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem selectCandidate
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiterals : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {result : CandidateAttemptResult}
    (catalog : LifetimeInferenceContext context)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : selectFunctionCandidateFrom context name candidates arguments integerLiterals
      call expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.result.type]) := by
  have privacy := selectFunctionCandidateFrom_private catalog.catalog cataloged ready lifetime.bound
    argumentsBelow expectedBelow argumentsSafe expectedSafe lifetime.live accepted
  have properties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
    (fun signature member => catalog.formation.function_scheme_body_variablesBelow
      (cataloged member) (catalog.canonical signature (cataloged member)) _) expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem fitExpected
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSafe : Safe binder.scheme.quantified state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : withExpected context state actual expected = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.expression.type]) := by
  have privacy := withExpected_private ready actualBelow expectedBelow actualSafe expectedSafe
    lifetime.live accepted
  have properties := withExpected_inferenceProperties ready actualBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (withExpected_new_requirements_private catalog ready actualSafe expectedSafe accepted)

theorem recordSelectedResult
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep)
    (ready : state.InferenceReady)
    (resultBelow : result.type.VariablesBelow state.inference.next)
    (resultSafe : Safe binder.scheme.quantified state result.type) :
    let recorded := recordSelectedCallResult source callee name arguments attempt result coercions state
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) := by
  dsimp only
  have privacy := recordSelectedCallResult_private source callee name arguments attempt result coercions state
    resultSafe lifetime.live
  have properties := recordSelectedCallResult_inferenceProperties source callee name arguments
    attempt result coercions state ready resultBelow
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

theorem recordSelected
    {attempt : CandidateAttemptResult}
    (lifetime : GeneralizationLifetime event entryNext attempt.state outputs)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (ready : attempt.state.InferenceReady)
    (resultBelow : attempt.result.type.VariablesBelow attempt.state.inference.next)
    (resultSafe : Safe binder.scheme.quantified attempt.state attempt.result.type) :
    let recorded := recordSelectedCall source callee name arguments attempt
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) :=
  lifetime.recordSelectedResult source callee name arguments attempt attempt.result []
    ready resultBelow resultSafe

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
