import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializerReturnPrivacy
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceActiveQuantifierOrigins

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization ProtectedVariables

/-- The actual statement preserves return-type privacy, including a new generalized binder. -/
theorem StatementBoundary.return_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected childFuel inferenceContext statement expectedReturn initial result frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn) :
    ∀ binder ∈ result.state.localBinders, Safe binder.scheme.quantified result.state expectedReturn := by
  intro binder member
  rcases inferStatementFuel_quantified_origin boundary.accepted binder member with old | mono | created
  · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
      initial boundary.invariant.ready boundary.operational.requirements (boundary.operational.quantifiersBelow binder old)
      (boundary.operational.privacy binder old) (boundary.scope.catalog checked) (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) boundary.invariant.returnBelow (returnSafe binder old)
      result boundary.accepted).1 _ (returnSafe binder old)
  · intro q _ quantified
    simp [mono] at quantified
  · obtain ⟨initializerFuel, receipt, rfl⟩ := created
    have idEq : result.id = initial.allocateStatementId.1 :=
      congrArg Detail.StatementResult.id receipt.completed
    have recorded : .statement {
        id := initial.allocateStatementId.1, span := statement.span, type := .unit
        form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes := by
      apply boundary.rawSubtree.nodes _ receipt.recorded
      exact .inl (congrArg NodeId.statement idEq.symm)
    let occurrence := BodyInitializerOccurrence.ofReceipt checked boundary.scope receipt boundary.invariant.ready
      boundary.operational recorded boundary.extension
    have safe := occurrence.generalized_type_safe checked boundary.scope boundary.invariant.ready
      boundary.operational boundary.invariant.returnBelow
    simpa only [occurrence, BodyInitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
