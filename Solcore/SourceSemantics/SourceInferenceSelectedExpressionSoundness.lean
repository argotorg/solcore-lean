import Solcore.SourceSemantics.SourceInferenceSelectedConstructorSoundness
import Solcore.SourceSemantics.SourceInferenceActualRootedSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedAtomicSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedGroupSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedTupleSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedConditionalSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedIndexSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedLambdaSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedUnarySoundness
import Solcore.SourceSemantics.SourceInferenceSelectedBinarySoundness
import Solcore.SourceSemantics.SourceInferenceSelectedNonConstructorCall
import Solcore.SourceSemantics.SourceInferenceSelectedCallDiscovery

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_zero : ActualInferExprFuelRetainedSoundness 0 := by
  intro wholeContext inferenceContext wholeReturn expression expected initial resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext success
  simp only [Detail.inferExprFuel] at success
  cases success

theorem actualInferExprFuelRetainedSoundness_step {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
    ActualInferExprFuelRetainedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expression expected initial resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext success resources interfaces extension
    signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
    operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
    retained coercions operators children covered semanticPreserved actualCovered
  have predecessor : ActualInferExprFuelRetainedSoundness fuel := recursive fuel (Nat.lt_succ_self fuel)
  cases expressionEq : expression.value with
  | literal literal =>
      exact actualInferExprFuelRetainedSoundness_literal expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | identifier name =>
      exact actualInferExprFuelRetainedSoundness_identifier expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | proxy marker type =>
      exact actualInferExprFuelRetainedSoundness_proxy expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | group inner =>
      exact actualInferExprFuelRetainedSoundness_group predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | tuple elements =>
      exact actualInferExprFuelRetainedSoundness_tuple recursive expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | unary operator operand =>
      exact actualInferExprFuelRetainedSoundness_unary recursive expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | binary left operator right =>
      exact actualInferExprFuelRetainedSoundness_binary predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | conditional condition question thenBranch colon elseBranch =>
      exact actualInferExprFuelRetainedSoundness_conditional predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | index base brackets index =>
      exact actualInferExprFuelRetainedSoundness_index predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | lambda keyword parameters returnAnnotation body =>
      exact actualInferExprFuelRetainedSoundness_lambda bodySound expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | call callee arguments =>
      rcases inferExprFuel_call_constructorDiscovery expressionEq success with absent | ⟨dataType, constructor, discovery⟩
      · exact actualInferExprFuelRetainedSoundness_call_nonConstructor recursive expressionEq absent success resources interfaces extension
          signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
          operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
          retained coercions operators children covered semanticPreserved actualCovered
      · exact actualInferExprFuelRetainedSoundness_call_constructor predecessor expressionEq discovery success resources interfaces extension
          signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
          operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
          retained coercions operators children covered semanticPreserved actualCovered
  | dotConstructor dot name arguments =>
      exact actualInferExprFuelRetainedSoundness_dotConstructor predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | field base dot name =>
      exact actualInferExprFuelRetainedSoundness_field_constructor predecessor expressionEq success resources interfaces extension
        signaturesEq ownerEq typeParametersEq assumptionsEq formation functions catalog canonical invariant actual
        operational expectedBelow expectedAdmissible finalPreserved rawProper patterns literals requirements
        retained coercions operators children covered semanticPreserved actualCovered
  | array elements =>
      simp only [Detail.inferExprFuel, expressionEq] at success
      cases success
  | error =>
      simp only [Detail.inferExprFuel, expressionEq] at success
      cases success

theorem actualInferExprFuelRootedSoundness_zero : ActualInferExprFuelRootedSoundness 0 :=
  actualInferExprFuelRootedSoundness_of_retainedSoundness actualInferExprFuelRetainedSoundness_zero

theorem actualInferExprFuelRootedSoundness_step {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
    ActualInferExprFuelRootedSoundness (fuel + 1) :=
  actualInferExprFuelRootedSoundness_of_retainedSoundness
    (actualInferExprFuelRetainedSoundness_step recursive bodySound)

end Solcore.SourceSemantics.SourceInferenceSoundness
