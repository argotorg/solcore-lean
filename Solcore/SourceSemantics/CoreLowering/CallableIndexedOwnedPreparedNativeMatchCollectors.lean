import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeReceipts

/-! The literal compatible match retains native typing of its actual scrutinee
beside the existing native body receipts. The marked hidden allocation only
affects the continuation; its initializer is the raw lowered expression.
One enclosing HasType supplies both parts. Source lookup, Source typing and
compiler occurrence equations stay separate. This is a static collector. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren
open CompatibleEncoding (bind_ok)

def TypedExpression (definitions : DataEnvironment) (administrative : Core.Context)
    (certificate : ExpressionCertificate) : ExpressionCertificate :=
  fun scope id lowered => certificate scope id lowered ∧
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType definitions

private theorem initializer_child
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {binder : TypedBinder} {payload output : Ty}
    {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Renaming.id binder
      output payload initializer body = .ok code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      initializer nativeType definitions := by
  rw [allocator] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, _allocated, exactCode⟩ := bind_ok accepted
  cases exactCode
  cases typed with | caseE initial _ _ => exact ⟨_, initial⟩

/-- The original real body typing producer runs once. Scrutinee typing is
added from that same emitted hidden-initialization wrapper, without replay. -/
theorem typed_expressions_and_bodies
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressionCertificate bodyCertificate code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    Certificate compilation source scope id resolution result reason
      (TypedExpression definitions administrative expressionCertificate)
      (CompatibleMatchNativeChildren.TypedBody definitions administrative type bodyCertificate) code := by
  have native := CompatibleMatchNativeChildren.Certificate.typed_bodies
    onError allocator sameDefinitions certificate typed
  cases native with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression
      sameType arms fallback branches hiddenCompiled =>
    obtain ⟨nativeType, scrutineeTyped⟩ := initializer_child onError allocator hiddenCompiled typed
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection
      ⟨expression, nativeType, scrutineeTyped⟩ sameType arms fallback branches hiddenCompiled

/-- The actual finite compiler collector supplies each expression factory
with its own native witness and every body with its original ordered action. -/
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
    {expressionCertificate : ExpressionCertificate} {administrative : Core.Context}
    (expressionExtract : ∀ childFuel lowered,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → expressionCertificate scope resolution.scrutinee lowered)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      result reasonAt reason = .ok code)
    {type : Ty}
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
  have native := typed_expressions_and_bodies onError allocator sameDefinitions raw typed
  have selected := Certificate.mapExpressionAt native (fun lowered generated => by
    obtain ⟨⟨childFuel, compiled⟩, nativeType, childTyped⟩ := generated
    exact expressionExtract childFuel lowered compiled childTyped)
  exact Certificate.finite_children selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
