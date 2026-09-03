import Solcore.Syntax.DeclarativeLocalExportExactnessProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.LocalExportSoundnessProperties

/-! Complete executable broad ordinary outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export local-export success as a broad ordinary outcome. -/
theorem localExport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.localExport start input =
      .ok declaration output) :
    DeclarativeGrammar.LocalExportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder :=
  localExport_success_sound start result

/-- Package local-export success and exact prioritized rejection. -/
theorem localExport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.localExport start input = .ok declaration output →
        DeclarativeGrammar.LocalExportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.localExport start input = .reject failure rejected →
        DeclarativeGrammar.LocalExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨localExport_success_ordinaryOutcome_sound start,
    localExport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive local-export outcomes. -/
theorem localExport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LocalExportOrdinaryParses start)
      DeclarativeGrammar.LocalExportRejects :=
  DeclarativeGrammar.localExportDeterministicOutcomeSpec start

/-- Re-export exact localExport outcomes with all supplied span data fixed. -/
theorem localExport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.LocalExportOrdinaryParses start)
      DeclarativeGrammar.LocalExportRejects :=
  DeclarativeGrammar.localExportExactOutcomeSpec start

/-- Two localExport successes fix the complete AST and declarative remainder. -/
theorem localExport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.localExport start input = .ok left leftOutput)
    (rightResult : ExportInternals.localExport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (localExport_exactOutcomeSpec start).successResultUnique
    (localExport_success_ordinaryOutcome_sound start leftResult)
    (localExport_success_ordinaryOutcome_sound start rightResult)

/-- Two localExport rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem localExport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.localExport start input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.localExport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (localExport_exactOutcomeSpec start).rejectOutputUnique
    (localExport_reject_ordinaryOutcome_sound start leftResult)
    (localExport_reject_ordinaryOutcome_sound start rightResult)

end Solcore.Syntax.Parser
