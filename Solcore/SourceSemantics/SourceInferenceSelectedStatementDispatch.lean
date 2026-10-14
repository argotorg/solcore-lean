import Solcore.SourceSemantics.SourceInferenceSelectedUnannotatedLetBranch
import Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedLetBranches
import Solcore.SourceSemantics.SourceInferenceSelectedStatementControlSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedStatementAtomicSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedStatementExpressionSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedStatementAssignmentSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedForLoopSoundness

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

def ActualInferMatchStatementFuelRootedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    (∃ scrutinees arms, statement.value = .matchWith scrutinees arms) →
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

theorem actualInferStatementFuelRootedSoundness_zero : ActualInferStatementFuelRootedSoundness 0 := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement initial result evidenceState roots
    finalized semanticSource frames semanticContext success
  simp only [Detail.inferStatementFuel] at success
  cases success

theorem actualInferStatementFuelRootedSoundness_step {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel)
    (itemsSound : ActualInferForItemsFuelRootedSoundness fuel)
    (matchSound : ActualInferMatchStatementFuelRootedSoundness (fuel + 1)) :
    ActualInferStatementFuelRootedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement initial result evidenceState roots
    finalized semanticSource frames semanticContext success resources interfaces signaturesEq ownerEq parametersEq
    assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension
    semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  cases form : statement.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | none =>
      cases initializer with
      | none => simp [Detail.inferStatementFuel, form, bind, Except.bind] at success
      | some initializer =>
        exact actualInferStatementFuelRootedSoundness_letUnannotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
    | some annotation =>
      cases initializer with
      | none => exact actualInferStatementFuelRootedSoundness_letAnnotatedUninitialized form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
      | some initializer => exact actualInferStatementFuelRootedSoundness_letAnnotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | returnStmt value =>
    cases value with
    | none =>
      exact actualInferStatementFuel_returnUnit_atomicBranch form allocation success formation functions
        invariant actual operational extension
    | some value =>
      exact actualInferStatementFuel_returnValue_scopedBranch form allocation success resources interfaces
        signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual
        operational returnAdmissible extension raw patterns literals requirements covered actualCovered expressionSound
  | expression expression trailing =>
    exact actualInferStatementFuel_expression_scopedBranch form allocation success resources interfaces
      signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual
      operational returnAdmissible extension raw patterns literals requirements covered actualCovered expressionSound
  | assignValue target operator value =>
    exact actualInferStatementFuelRootedSoundness_assignValue placeSound expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | assignBitNot target operator =>
    exact actualInferStatementFuelRootedSoundness_assignBitNot placeSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | matchWith scrutinees arms => exact matchSound ⟨scrutinees, arms, form⟩ success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | forLoop span initializer condition post body =>
    exact actualInferStatementFuelRootedSoundness_forLoop itemsSound expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | whileLoop condition body =>
    exact actualInferStatementFuelRootedSoundness_whileLoop expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | ifThen condition thenBody elseBody =>
    cases elseBody with
    | none => exact actualInferStatementFuelRootedSoundness_ifWithoutElse expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
    | some elseBody => exact actualInferStatementFuelRootedSoundness_ifWithElse expressionSound bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | block body => exact actualInferStatementFuelRootedSoundness_block bodySound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements covered actualCovered
  | breakStmt =>
    exact actualInferStatementFuel_break_atomicBranch form allocation success formation functions
      invariant actual operational extension
  | continueStmt =>
    exact actualInferStatementFuel_continue_atomicBranch form allocation success formation functions
      invariant actual operational extension
  | assembly body => simp [Detail.inferStatementFuel, form] at success
  | error => simp [Detail.inferStatementFuel, form] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
