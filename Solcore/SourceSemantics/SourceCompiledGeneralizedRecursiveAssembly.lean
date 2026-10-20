import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementDispatch
import Solcore.SourceSemantics.SourceCompiledGeneralizedForDispatch
import Solcore.SourceSemantics.SourceCompiledGeneralizedForSequence
import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedForReturnConnection
import Solcore.SourceSemantics.SourceCompiledGeneralizedSequenceReturnConnection

/-! Actual expressions, statements and header items are assembled together by
fuel. Generalization barriers remain indexed by the concrete selected
initializer boundaries, ready for the compiler-scope producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem recursiveSoundness_of_barriers_for
    {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected) :
    ∀ childFuel,
      ExpressionRetainedSoundnessFor callProvenance selected childFuel ∧
      StatementRootedSoundnessFor callProvenance selected childFuel ∧
      StatementsRootedSoundnessFor callProvenance selected childFuel ∧
      ForItemRootedSoundnessFor callProvenance selected childFuel ∧
      ForItemsRootedSoundnessFor callProvenance selected childFuel := by
  intro childFuel
  induction childFuel using Nat.strongRecOn with
  | ind childFuel induction =>
    cases childFuel with
    | zero =>
      exact ⟨expressionRetained_zero_for, statementRooted_zero_for,
        (fun _ safe admissible boundary => statementsRooted_zero safe admissible boundary), forItemRooted_zero_for,
        forItemsRooted_of_item_for checked descend forItemRooted_zero_for⟩
    | succ childFuel =>
      have expressions : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller :=
        fun smaller below => (induction smaller below).1
      have rooted : ∀ smaller, smaller < childFuel + 1 → ExpressionRootedSoundnessFor callProvenance selected smaller :=
        fun smaller below => expressionRooted_of_retained_for checked (expressions smaller below)
      have bodies : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundnessFor callProvenance selected smaller :=
        fun smaller below => (induction smaller below).2.2.1
      have previous := induction childFuel (Nat.lt_succ_self childFuel)
      have expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel :=
        rooted childFuel (Nat.lt_succ_self childFuel)
      have placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel :=
        placeRootedSoundness_for checked descend childFuel
          (fun smaller below => rooted smaller (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
      have items : ForItemRootedSoundnessFor callProvenance selected (childFuel + 1) :=
        forItemRooted_step_for checked descend barriers expressionSound placeSound
      have statementSound : StatementRootedSoundnessFor callProvenance selected (childFuel + 1) := by
        apply statementRooted_step_of_for_for checked descend barriers expressions bodies placeSound
        intro inferenceContext statement headerSpan initializer post condition body expectedReturn initial result frames target
          here form boundary returnSafe returnAdmissible
        exact statement_for_for checked descend previous.2.2.2.2 expressionSound here form boundary returnSafe returnAdmissible
          (fun bodyHere safe admissible bodyBoundary => previous.2.2.1 bodyHere safe admissible bodyBoundary)
      exact ⟨expressionRetained_step_for checked descend expressions previous.2.2.1,
        statementSound, statementsRooted_step_for checked descend previous.2.1 previous.2.2.1,
        items, forItemsRooted_of_item_for checked descend items⟩

theorem recursiveSoundness_of_barriers
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected) :
    ∀ childFuel,
      ExpressionRetainedSoundness selected childFuel ∧
      StatementRootedSoundness selected childFuel ∧
      StatementsRootedSoundness selected childFuel ∧
      ForItemRootedSoundness selected childFuel ∧
      ForItemsRootedSoundness selected childFuel := by
  intro childFuel
  have result := recursiveSoundness_of_barriers_for checked true_childClosed barriers.with_true childFuel
  exact ⟨expressionRetainedSoundness_of_true result.1,
    statementRootedSoundness_of_true result.2.1,
    statementsRootedSoundness_of_true result.2.2.1,
    forItemRootedSoundness_of_true result.2.2.2.1,
    forItemsRootedSoundness_of_true result.2.2.2.2⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
