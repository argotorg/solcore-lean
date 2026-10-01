import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
import Solcore.SourceSemantics.CoreLowering.GenericMatchChildren

/-! Actual compatible lowering retains the finite ordered body callbacks and
supplies their native typing from the enclosing generated code. Duplicates
remain in the receipt, with exact source scopes and compiler equations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeReceipts
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren

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
    {expressionCertificate : ExpressionCertificate}
    (expressionExtract : ∀ childFuel lowered,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok lowered →
      expressionCertificate scope resolution.scrutinee lowered)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      result reasonAt reason = .ok code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    ∃ requests,
      Certificate compilation source scope id resolution result reason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests,
        (∃ childFuel, lowerBody childFuel source request.scope request.statements result reasonAt reason = .ok request.code) ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code type definitions := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements result reasonAt reason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  have native := CompatibleMatchNativeChildren.Certificate.typed_bodies onError allocator sameDefinitions raw typed
  have selected := Certificate.mapExpressionAt native (fun lowered generated => by
    obtain ⟨childFuel, compiled⟩ := generated
    exact expressionExtract childFuel lowered compiled)
  exact Certificate.finite_children selected

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeReceipts
