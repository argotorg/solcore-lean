import Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package import-terminator semicolon/recovery success and exact rejection. -/
theorem importTerminator_ordinaryOutcome_sound (lastSpan : SourceSpan) :
    (∀ {input output : State} {endSpan : SourceSpan},
      ImportInternals.terminator lastSpan input = .ok endSpan output →
        DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
          input.declarativeRemainder endSpan output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.terminator lastSpan input = .reject failure rejected →
        DeclarativeGrammar.ImportTerminatorRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨importTerminator_success_ordinaryOutcome_sound lastSpan,
    importTerminator_reject_ordinaryOutcome_sound lastSpan⟩

/-- Re-export deterministic and exclusive import-terminator outcomes. -/
theorem importTerminator_ordinaryOutcomeSpec (lastSpan : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan)
      DeclarativeGrammar.ImportTerminatorRejects :=
  DeclarativeGrammar.importTerminatorDeterministicOutcomeSpec lastSpan


/-- Exact values and endpoints for the independent importTerminator grammar. -/
theorem importTerminator_exactOutcomeSpec (lastSpan : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan) DeclarativeGrammar.ImportTerminatorRejects :=
  DeclarativeGrammar.importTerminatorExactOutcomeSpec lastSpan

/-- Executable successes agree on their complete value and remainder. -/
theorem importTerminator_success_result_unique (lastSpan : SourceSpan)
    {input leftOutput rightOutput : State} {left right : SourceSpan}
    (leftResult : ImportInternals.terminator lastSpan input = .ok left leftOutput)
    (rightResult : ImportInternals.terminator lastSpan input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importTerminator_exactOutcomeSpec lastSpan).successResultUnique
    (importTerminator_success_ordinaryOutcome_sound lastSpan leftResult)
    (importTerminator_success_ordinaryOutcome_sound lastSpan rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem importTerminator_reject_output_unique (lastSpan : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.terminator lastSpan input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.terminator lastSpan input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importTerminator_exactOutcomeSpec lastSpan).rejectOutputUnique
    (importTerminator_reject_ordinaryOutcome_sound lastSpan leftResult)
    (importTerminator_reject_ordinaryOutcome_sound lastSpan rightResult)

end Solcore.Syntax.Parser
