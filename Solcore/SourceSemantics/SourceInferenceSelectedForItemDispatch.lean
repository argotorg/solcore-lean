import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicForItem
import Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedForItems
import Solcore.SourceSemantics.SourceInferenceSelectedForItemBranches
import Solcore.SourceSemantics.SourceInferenceSelectedPlaceSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedForItemsSequencing

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferForItemFuelRootedSoundness_zero : ActualInferForItemFuelRootedSoundness 0 := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item initial final inferred evidenceState roots
    finalized semanticSource frames semanticContext control success
  simp [Detail.inferForItemFuel] at success

theorem actualInferForItemFuelRootedSoundness_step {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel) :
    ActualInferForItemFuelRootedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item initial final inferred evidenceState roots
    finalized semanticSource frames semanticContext control success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  cases form : item.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | none =>
      cases initializer with
      | none => simp [Detail.inferForItemFuel, form, bind, Except.bind] at success
      | some initializer =>
        exact actualInferForItemFuelRootedSoundness_letUnannotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
    | some annotation =>
      cases initializer with
      | none =>
        exact actualInferForItemFuelRootedSoundness_letAnnotatedUninitialized form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
      | some initializer =>
        exact actualInferForItemFuelRootedSoundness_letAnnotatedInitialized expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | expression expression =>
    exact actualInferForItemFuelRootedSoundness_expression expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | assignValue target operator value =>
    exact actualInferForItemFuelRootedSoundness_assignValue placeSound expressionSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings
  | assignBitNot target operator =>
    exact actualInferForItemFuelRootedSoundness_assignBitNot placeSound form success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog parameters invariant actual operational returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered bindings actualCovered actualBindings

end Solcore.SourceSemantics.SourceInferenceSoundness
