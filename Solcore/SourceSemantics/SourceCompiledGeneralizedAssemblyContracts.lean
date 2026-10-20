import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionDispatch
import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializedConnection
import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedHeaderInitializer

/-! The recursive assembly uses the original selected function throughout.
Its remaining generalization inputs concern concrete initializer occurrences
and their actual semantic boundaries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def StatementRootedSoundness (selected : Selected compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementBoundary selected childFuel inferenceContext statement expectedReturn
      initial result frames target →
    StatementConclusion selected inferenceContext expectedReturn result frames target

structure SelectedInitializerBarriers (selected : Selected compiled row fuel) : Prop where
  statement : ∀ {source : Syntax.Statement} {expectedReturn : Ty}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
      (occurrence : InitializerOccurrence selected source),
    StatementBoundary selected (occurrence.childFuel + 1) occurrence.inferenceContext source expectedReturn
      occurrence.entry occurrence.result frames target →
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)
  header : ∀ {childFuel : Nat} {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
      {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target →
    ∀ receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final),
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
