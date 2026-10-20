import Solcore.SourceSemantics.SourceInferenceGeneralizedScrutineeState
import Solcore.SourceSemantics.SourceCompiledGeneralizedPatternEntry

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization ProtectedVariables

/-- Every actual scrutinee shape enters its first pattern with privacy derived
from that scrutinee computation, including the synthetic tuple branch. -/
theorem patternEntered_after_scrutinees
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel expressionFuel patternFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr}
    {patternSource : Syntax.Pattern} {entry scrutineeState initial resultState : State}
    {scrutinee : InferredExpression} {inferred : TypedMatchPattern}
    {hidden : Resolved.LocalId} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (entryReady : entry.InferenceReady)
    (entryOperational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (expressionAccepted : inferMatchScrutineesFuel expressionFuel inferenceContext span sources entry =
      .ok (scrutinee, scrutineeState))
    (allocation : scrutineeState.allocateHiddenLocal = (hidden, initial))
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply scrutinee.type))
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel patternFuel inferenceContext patternSource scrutinee.type initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution scrutinee.type inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have canonical := scope.functionsCanonical checked
  have properties := inferMatchScrutineesFuel_inferenceProperties entryReady formation canonical
    expressionAccepted
  have actualScrutinees := entryOperational.ofMatchScrutinees entryReady catalog formation canonical expressionAccepted
  have privacy := actualScrutinees.2
  have operational := actualScrutinees.1.allocateHiddenLocal
  have initialEq := congrArg Prod.snd allocation
  simp only at initialEq
  subst initial
  exact patternEntered checked scope invariant actual operational owner properties.2.2
    expectedAdmissible privacy extension integerPatterns requirements occurs covered accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
