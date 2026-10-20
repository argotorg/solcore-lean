import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotatedInitializer
import Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForBitNot
import Solcore.SourceSemantics.SourceCompiledGeneralizedForExpression
import Solcore.SourceSemantics.SourceCompiledGeneralizedForValueAssignment

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem forItemRooted_zero : ForItemRootedSoundness selected 0 := by
  intro inferenceContext item expectedReturn initial final inferred frames target boundary
  have success := boundary.accepted
  simp only [Detail.inferForItemFuel] at success
  cases success

theorem forItemRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    (placeSound : PlaceRootedSoundness selected childFuel) :
    ForItemRootedSoundness selected (childFuel + 1) := by
  intro inferenceContext item expectedReturn initial final inferred frames target boundary
  cases form : item.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | some sourceType =>
      cases initializer with
      | none => exact forItem_annotatedUninitialized checked form boundary
      | some source => exact forItem_annotatedInitialized checked expressionSound form boundary
    | none =>
      cases initializer with
      | none =>
        have success := boundary.accepted
        simp [Detail.inferForItemFuel, form, bind, Except.bind, throw] at success
      | some source =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_accepted form boundary.accepted
        exact forItem_initialized_of_receipt checked expressionSound boundary receipt (barriers.header boundary receipt)
  | expression source => exact forItem_expression checked expressionSound form boundary
  | assignValue target operator value =>
    exact forItem_assignValue checked placeSound expressionSound form boundary
  | assignBitNot target span => exact forItem_assignBitNot checked placeSound form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
