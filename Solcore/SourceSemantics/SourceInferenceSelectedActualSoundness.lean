import Solcore.SourceSemantics.SourceInferenceSelectedMatchSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedStatementDispatch
import Solcore.SourceSemantics.SourceInferenceSelectedForItemDispatch
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedRootedStatementSequencing
import Solcore.SourceSemantics.SourceInferenceActualRecursiveSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

structure SelectedActualInferenceFamily (fuel : Nat) : Prop where
  expression : ActualInferExprFuelRetainedSoundness fuel
  statement : ActualInferStatementFuelRootedSoundness fuel
  forItem : ActualInferForItemFuelRootedSoundness fuel

theorem selectedActualInferenceFamily :
    ∀ fuel, SelectedActualInferenceFamily fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel recursive =>
    cases fuel with
    | zero =>
      exact ⟨actualInferExprFuelRetainedSoundness_zero,
        actualInferStatementFuelRootedSoundness_zero,
        actualInferForItemFuelRootedSoundness_zero⟩
    | succ fuel =>
      have expressionStrong : ∀ smaller, smaller < fuel + 1 →
          ActualInferExprFuelRetainedSoundness smaller :=
        fun smaller bound => (recursive smaller bound).expression
      have expressionRootedStrong : ∀ smaller, smaller < fuel + 1 →
          ActualInferExprFuelRootedSoundness smaller :=
        fun smaller bound => actualInferExprFuelRootedSoundness_of_retainedSoundness
          (expressionStrong smaller bound)
      have bodiesStrong : ∀ smaller, smaller < fuel + 1 →
          ActualInferStatementsFuelRootedSoundness smaller := by
        intro smaller smallerBound
        apply actualInferStatementsFuelRootedSoundness_of_selected_statementSoundness
        intro child childBound
        exact (recursive child (Nat.lt_trans childBound smallerBound)).statement
      have expressionSound : ActualInferExprFuelRootedSoundness fuel := expressionRootedStrong fuel (Nat.lt_succ_self fuel)
      have placeSound : ActualInferPlaceFuelRootedSoundness fuel := actualInferPlaceFuelRootedSoundness fuel
        (fun smaller bound => expressionRootedStrong smaller (Nat.lt_trans bound (Nat.lt_succ_self fuel)))
      have bodySound : ActualInferStatementsFuelRootedSoundness fuel := bodiesStrong fuel (Nat.lt_succ_self fuel)
      have itemsSound : ActualInferForItemsFuelRootedSoundness fuel := actualInferForItemsFuelRootedSoundness_of_itemSoundness
        (recursive fuel (Nat.lt_succ_self fuel)).forItem
      have matchSound : ActualInferMatchStatementFuelRootedSoundness (fuel + 1) := by
        intro wholeContext inferenceContext wholeReturn expectedReturn statement initial result evidenceState roots
          finalized semanticSource frames semanticContext form
        obtain ⟨scrutinees, arms, form⟩ := form
        exact actualInferStatementFuelRootedSoundness_match expressionStrong bodiesStrong form
      exact ⟨actualInferExprFuelRetainedSoundness_step expressionStrong bodySound,
        actualInferStatementFuelRootedSoundness_step expressionSound placeSound bodySound
          itemsSound matchSound,
        actualInferForItemFuelRootedSoundness_step expressionSound placeSound⟩

/-- Actual selected-source inference is sound for every successful expression. -/
theorem actualInferExprFuelRetainedSoundness_selected (fuel : Nat) :
    ActualInferExprFuelRetainedSoundness fuel :=
  (selectedActualInferenceFamily fuel).expression

theorem actualInferExprFuelRootedSoundness_selected (fuel : Nat) :
    ActualInferExprFuelRootedSoundness fuel :=
  actualInferExprFuelRootedSoundness_of_retainedSoundness
    (actualInferExprFuelRetainedSoundness_selected fuel)

theorem actualInferStatementFuelRootedSoundness_selected (fuel : Nat) :
    ActualInferStatementFuelRootedSoundness fuel :=
  (selectedActualInferenceFamily fuel).statement

theorem actualInferForItemFuelRootedSoundness_selected (fuel : Nat) :
    ActualInferForItemFuelRootedSoundness fuel :=
  (selectedActualInferenceFamily fuel).forItem

theorem actualInferForItemsFuelRootedSoundness_selected (fuel : Nat) :
    ActualInferForItemsFuelRootedSoundness fuel :=
  actualInferForItemsFuelRootedSoundness_of_itemSoundness
    (actualInferForItemFuelRootedSoundness_selected fuel)

theorem actualInferStatementsFuelRootedSoundness_selected (fuel : Nat) :
    ActualInferStatementsFuelRootedSoundness fuel :=
  actualInferStatementsFuelRootedSoundness_of_selected_statementSoundness
    (fun childFuel _ => actualInferStatementFuelRootedSoundness_selected childFuel)

/-- The actual body-checking endpoint closes all mutually recursive source
judgments internally. Its selected-source invariants are supplied by the
original checker and accepted compiler receipts at the body boundary. -/
theorem actualInferStatementsFuelSoundness_selected (fuel : Nat) :
    ActualInferStatementsFuelSoundness fuel :=
  actualInferStatementsFuelSoundness_of_scopedSoundness
    (actualInferStatementsFuelScopedSoundness_of_rootedSoundness
      (actualInferStatementsFuelRootedSoundness_selected fuel))

end Solcore.SourceSemantics.SourceInferenceSoundness
