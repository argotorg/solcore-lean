import Solcore.SourceSemantics.SourceInferenceSelectedConstructorInstantiation

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualFreshConstructorApplication_typing {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial constructorState resultState evidenceState : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {inferred : InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource} {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context},
    dataType ∈ inferenceContext.signatures.dataTypes →
    constructor ∈ dataType.constructors →
    Detail.freshDataConstructorInstantiation dataType constructor initial = (instantiation, constructorState) →
    Detail.inferConstructorApplicationFuel fuel inferenceContext source id instantiation arguments expected constructorState = .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ type ∈ expected, type.VariablesBelow initial.inference.next) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn source id arguments instantiation expected initial constructorState resultState evidenceState
    dataType constructor inferred roots finalized semanticSource frames semanticContext dataMember constructorMember fresh
    success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical
    invariant actual operational expectedBelow semantic final raw patterns literals requirements retained coercionsRetained
    childrenRetained covered actualCovered
  have freshInvariant := invariant.freshConstructor dataType constructor
  have freshOperational := operational.freshConstructor dataType constructor
  rw [fresh] at freshInvariant freshOperational
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor initial invariant.ready
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember initial.inference.next)
  rw [fresh] at properties
  have binders := invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical)
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [invariant.signatures_eq_whole, ← signaturesEq]; exact catalog
  have activeData : dataType ∈ semanticContext.signatures.dataTypes := by
    rw [invariant.signatures_eq_whole, ← signaturesEq]; exact dataMember
  have range := resources.substitutionRangeAdmissible binders invariant.signatures_eq_whole invariant.typeParametersEq
    invariant.declarationEq invariant.residual
  have valid := freshConstructor_admissible_afterSubstitution activeCatalog binders invariant.residual range
    activeData constructorMember fresh
  exact actualConstructorApplication_typing recursive success resources interfaces extension signaturesEq ownerEq typeParametersEq
    assumptionsEq formation functions catalog canonical freshInvariant actual freshOperational properties.2.2.2.1
    properties.2.2.2.2 (fun type member => (expectedBelow type member).weaken properties.1.next_le) valid
    semantic final raw patterns literals requirements retained coercionsRetained childrenRetained covered actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
