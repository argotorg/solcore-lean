import Solcore.Syntax.DeclarativeExportDeclExactnessProperties
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportDeclSoundnessProperties

/-! Complete executable broad ordinary outcomes for export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export complete-export success as a broad ordinary outcome. -/
theorem exportDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ExportDecl}
    (result : exportDecl input = .ok declaration output) :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder :=
  exportDecl_success_sound result

/-- Package complete-export success and exact prioritized rejection. -/
theorem exportDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ExportDecl},
      exportDecl input = .ok declaration output →
        DeclarativeGrammar.ExportDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      exportDecl input = .reject failure rejected →
        DeclarativeGrammar.ExportDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportDecl_success_ordinaryOutcome_sound,
    exportDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive complete-export outcomes. -/
theorem exportDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportDeclOrdinaryParses
      DeclarativeGrammar.ExportDeclRejects :=
  DeclarativeGrammar.exportDeclDeterministicOutcomeSpec

/-- Re-export exact exportDecl outcomes with all supplied span data fixed. -/
theorem exportDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportDeclOrdinaryParses
      DeclarativeGrammar.ExportDeclRejects :=
  DeclarativeGrammar.exportDeclExactOutcomeSpec

/-- Two exportDecl successes fix the complete AST and declarative remainder. -/
theorem exportDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : exportDecl input = .ok left leftOutput)
    (rightResult : exportDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportDecl_exactOutcomeSpec.successResultUnique
    (exportDecl_success_ordinaryOutcome_sound leftResult)
    (exportDecl_success_ordinaryOutcome_sound rightResult)

/-- Two exportDecl rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : exportDecl input = .reject leftFailure leftOutput)
    (rightResult : exportDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportDecl_exactOutcomeSpec.rejectOutputUnique
    (exportDecl_reject_ordinaryOutcome_sound leftResult)
    (exportDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
