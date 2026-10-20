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
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}

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
  induction childFuel using Nat.strongRecOn with
  | ind childFuel induction =>
    cases childFuel with
    | zero =>
      exact ⟨expressionRetained_zero, statementRooted_zero, statementsRooted_zero, forItemRooted_zero,
        forItemsRooted_of_item checked forItemRooted_zero⟩
    | succ childFuel =>
      have expressions : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller :=
        fun smaller below => (induction smaller below).1
      have rooted : ∀ smaller, smaller < childFuel + 1 → ExpressionRootedSoundness selected smaller :=
        fun smaller below => expressionRooted_of_retained checked (expressions smaller below)
      have bodies : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundness selected smaller :=
        fun smaller below => (induction smaller below).2.2.1
      have previous := induction childFuel (Nat.lt_succ_self childFuel)
      have expressionSound : ExpressionRootedSoundness selected childFuel :=
        rooted childFuel (Nat.lt_succ_self childFuel)
      have placeSound : PlaceRootedSoundness selected childFuel :=
        placeRootedSoundness checked childFuel
          (fun smaller below => rooted smaller (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
      have items : ForItemRootedSoundness selected (childFuel + 1) :=
        forItemRooted_step checked barriers expressionSound placeSound
      have statementSound : StatementRootedSoundness selected (childFuel + 1) := by
        apply statementRooted_step_of_for checked barriers expressions bodies placeSound
        intro inferenceContext statement headerSpan initializer post condition body expectedReturn initial result frames target
          form boundary returnSafe returnAdmissible
        exact statement_for checked previous.2.2.2.2 expressionSound form boundary returnSafe returnAdmissible
          (fun safe admissible bodyBoundary => previous.2.2.1 safe admissible bodyBoundary)
      exact ⟨expressionRetained_step checked expressions previous.2.2.1,
        statementSound, statementsRooted_step checked previous.2.1 previous.2.2.1,
        items, forItemsRooted_of_item checked items⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
