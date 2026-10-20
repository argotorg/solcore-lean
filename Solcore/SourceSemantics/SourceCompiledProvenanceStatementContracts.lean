import Solcore.SourceSemantics.SourceCompiledProvenanceExpressionContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceTyping

/-! Exact-call provenance accompanies the existing semantic boundaries.
Generalization barriers are requested only for those same calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def StatementRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.statement childFuel inferenceContext statement expectedReturn initial result) →
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementBoundary selected childFuel inferenceContext statement expectedReturn
      initial result frames target →
    StatementConclusion selected inferenceContext expectedReturn result frames target

def StatementsRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.statements childFuel inferenceContext statements expectedReturn initial result) →
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementsBoundary selected childFuel inferenceContext statements expectedReturn
      initial result frames target →
    StatementsConclusion selected inferenceContext expectedReturn result frames target

def ForItemRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expectedReturn : Ty}
    {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItem childFuel inferenceContext item initial inferred final) →
    ForItemBoundary selected childFuel inferenceContext item expectedReturn
      initial inferred final frames target →
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target

def ForItemsRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {items : List Syntax.ForItem} {expectedReturn : Ty}
    {initial : State} {result : Detail.InferredForItems}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItems childFuel inferenceContext items initial result) →
    ForItemsBoundary selected childFuel inferenceContext items expectedReturn
      initial result frames target →
    ForItemsConclusion selected inferenceContext expectedReturn result frames target

def PlaceRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.place childFuel inferenceContext expression initial place final) →
    PlaceBoundary selected childFuel inferenceContext expression initial place final frames target →
    PlaceConclusion selected place final target

structure BodyInitializerBarriersFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) : Prop where
  statement : ∀ {source : Syntax.Statement} {expectedReturn : Ty}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
      (occurrence : BodyInitializerOccurrence selected source),
    provenance (.statement (occurrence.childFuel + 1) occurrence.inferenceContext
      source expectedReturn occurrence.entry occurrence.result) →
    StatementBoundary selected (occurrence.childFuel + 1) occurrence.inferenceContext source expectedReturn
      occurrence.entry occurrence.result frames target →
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)
  header : ∀ {childFuel : Nat} {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
      {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItem (childFuel + 1) inferenceContext item initial inferred final) →
    ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target →
    ∀ receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final),
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
