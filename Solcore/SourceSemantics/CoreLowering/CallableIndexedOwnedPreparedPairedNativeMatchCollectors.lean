import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors

/-! The same match certificate retains actual and fixed native witnesses.
Two independent constructor inversions strengthen one accepted compiler
certificate. One finite_children call then keeps the original ordered body
requests, with both typings at their identical scopes and code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren

/-- Native witnesses are supplied only for the actual emitted scrutinee and
ordered body requests. Their result types and contexts remain independent. -/
theorem finite_typed_of_lower
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {reason : Word} {code : Expr}
    {expressionCertificate : ExpressionCertificate} {administrative fixedAdministrative : Core.Context}
    (expressionExtract : ∀ childFuel lowered,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok lowered →
      ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions →
      HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
        lowered.expression fixedNativeType definitions → expressionCertificate scope resolution.scrutinee lowered)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      result reasonAt reason = .ok code)
    {type fixedType : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions)
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) code fixedType definitions) :
    ∃ requests,
      Certificate compilation source scope id resolution result reason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests,
        (∃ childFuel, lowerBody childFuel source request.scope request.statements result reasonAt reason = .ok request.code) ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code type definitions ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ fixedAdministrative) request.code fixedType definitions := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements result reasonAt reason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  have actual := CallableIndexedOwnedPreparedNativeMatchCollectors.typed_expressions_and_bodies
    onError allocator sameDefinitions raw typed
  have paired := CallableIndexedOwnedPreparedNativeMatchCollectors.typed_expressions_and_bodies
    onError allocator sameDefinitions actual fixedTyped
  have selected := Certificate.mapExpressionAt paired (fun lowered generated => by
    obtain ⟨⟨⟨childFuel, compiled⟩, nativeType, childTyped⟩, fixedNativeType, fixedChildTyped⟩ := generated
    exact expressionExtract childFuel lowered compiled childTyped fixedChildTyped)
  obtain ⟨requests, receipt, length, known⟩ := Certificate.finite_children selected
  refine ⟨requests, receipt, length, ?_⟩
  intro request member
  obtain ⟨⟨generated, actualTyped⟩, fixedBodyTyped⟩ := known request member
  exact ⟨generated, actualTyped, fixedBodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
