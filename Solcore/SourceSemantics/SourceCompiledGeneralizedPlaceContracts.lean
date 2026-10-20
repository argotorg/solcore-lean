import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
import Solcore.SourceSemantics.SourceInferenceGeneralizedPlaceState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure PlaceBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (initial : State) (place : PlaceResolution) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferPlaceFuel childFuel inferenceContext expression initial = .ok (place, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawKeys : ∀ key, .expression key ∈ place.references →
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression key)
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  covered : ∀ key, .expression key ∈ place.references →
    TemplateScopeCovered selected.body.finalized.typedSource target (.expression key)
  actualCovered : ∀ key, .expression key ∈ place.references →
    ActualContext.Covers selected.body.finalized frames (.expression key)

def PlaceConclusion (selected : BodySelection compiled row fuel)
    (place : PlaceResolution) (final : State) (target : SourceSemantics.Context) : Prop :=
  SourcePlaceHasType selected.body.finalized.typedSource target
    (place.applySubstitution selected.body.finalized.substitution)
    (selected.body.finalized.substitution.apply place.type) ∧
  GeneralizedActualStateInvariant final (evidenceSource selected) ∧
  ∀ binder ∈ final.localBinders,
    ProtectedVariables.Safe binder.scheme.quantified final place.type

def PlaceRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    PlaceBoundary selected childFuel inferenceContext expression initial place final frames target →
    PlaceConclusion selected place final target

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
