import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
import Solcore.SourceSemantics.SourceCompiledProvenanceCompatibility
import Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotatedInitializer
import Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForBitNot
import Solcore.SourceSemantics.SourceCompiledGeneralizedForExpression
import Solcore.SourceSemantics.SourceCompiledGeneralizedForValueAssignment

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}

theorem forItemRooted_zero_for : ForItemRootedSoundnessFor callProvenance selected 0 := by
  intro inferenceContext item expectedReturn initial final inferred frames target here boundary
  have success := boundary.accepted
  simp only [Detail.inferForItemFuel] at success
  cases success

theorem forItemRooted_step_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected)
    (expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    (placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel) :
    ForItemRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext item expectedReturn initial final inferred frames target here boundary
  cases form : item.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | some sourceType =>
      cases initializer with
      | none => exact forItem_annotatedUninitialized checked form boundary
      | some source => exact forItem_annotatedInitialized_for checked descend expressionSound here form boundary
    | none =>
      cases initializer with
      | none =>
        have success := boundary.accepted
        simp [Detail.inferForItemFuel, form, bind, Except.bind, throw] at success
      | some source =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_accepted form boundary.accepted
        exact forItem_initialized_of_receipt_for checked descend expressionSound here boundary receipt
          (barriers.header here boundary receipt)
  | expression source => exact forItem_expression_for checked descend expressionSound here form boundary
  | assignValue target operator value =>
    exact forItem_assignValue_for checked descend placeSound expressionSound here form boundary
  | assignBitNot target span => exact forItem_assignBitNot_for checked descend placeSound here form boundary

theorem forItemRooted_zero : ForItemRootedSoundness selected 0 :=
  forItemRootedSoundness_of_true (forItemRooted_zero_for (selected := selected) (callProvenance := fun _ => True))

theorem forItemRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    (placeSound : PlaceRootedSoundness selected childFuel) :
    ForItemRootedSoundness selected (childFuel + 1) := by
  apply forItemRootedSoundness_of_true
  exact forItemRooted_step_for checked true_childClosed barriers.with_true
    (fun _ boundary => expressionSound boundary) (placeRootedSoundnessFor_true placeSound)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
