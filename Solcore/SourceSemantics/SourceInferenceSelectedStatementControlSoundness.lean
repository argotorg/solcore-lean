import Solcore.SourceSemantics.SourceInferenceSelectedStatementBodies
import Solcore.SourceSemantics.SourceInferenceSelectedStatementConditionSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferStatementFuelRootedSoundness_block {fuel : Nat}
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .block body →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
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
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_block_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered bodySound

theorem actualInferStatementFuelRootedSoundness_whileLoop {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .whileLoop condition body →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
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
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_whileLoop_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_whileLoop_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

theorem actualInferStatementFuelRootedSoundness_ifWithoutElse {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .ifThen condition body none →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
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
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_ifWithoutElse_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_ifWithoutElse_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

theorem actualInferStatementFuelRootedSoundness_ifWithElse {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body elseBody : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .ifThen condition body (some elseBody) →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
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
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body elseBody initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_ifWithElse_of_scoped_bodies statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_ifWithElse_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

end Solcore.SourceSemantics.SourceInferenceSoundness
