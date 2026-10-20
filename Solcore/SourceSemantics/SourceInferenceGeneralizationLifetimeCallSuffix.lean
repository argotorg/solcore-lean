import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeOperatorSteps

/-! Actual indirect and builtin call suffixes preserve child generalizations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem applyIndirect
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {result : IndirectApplicationResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeSafe : Safe binder.scheme.quantified state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : applyFunctionType context call callee arguments expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.result.type]) := by
  have privacy := applyFunctionType_private catalog ready lifetime.bound calleeBelow argumentsBelow
    expectedBelow calleeSafe argumentsSafe expectedSafe lifetime.live accepted
  have properties := applyFunctionType_inferenceProperties ready calleeBelow argumentsBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem recordIndirect
    {application : IndirectApplicationResult}
    (lifetime : GeneralizationLifetime event entryNext application.state outputs)
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (ready : application.state.InferenceReady)
    (resultBelow : application.result.type.VariablesBelow application.state.inference.next)
    (resultSafe : Safe binder.scheme.quantified application.state application.result.type) :
    let recorded := recordIndirectCall source callee arguments application
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) := by
  dsimp only
  have privacy := recordIndirectCall_private source callee arguments application resultSafe lifetime.live
  have properties := recordIndirectCall_inferenceProperties source callee arguments application ready resultBelow
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

theorem recordBuiltin
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := recordBuiltinFunctionCall_private argumentsSafe expectedSafe lifetime.live accepted
  have properties := recordBuiltinFunctionCall_inferenceProperties ready argumentsBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
