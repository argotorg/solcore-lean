import Solcore.Syntax.DeclarativeSelectedImportsOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.SelectedImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportOrdinarySuccessSoundnessProperties

/-! Exact executable rejection reflection for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import-list rejection comes from its required
nonempty, allow-trailing delimited stage; the nonempty refinement cannot
reject. -/
theorem selectedImports_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectedImports input =
      .reject failure rejected) :
    DeclarativeGrammar.SelectedImportsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectedImports at result
  cases valuesResult : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      exact delimited_reject_sound .leftBrace .rightBrace false selectedImport
        DeclarativeGrammar.SelectedImportOrdinaryParses
        DeclarativeGrammar.SelectedImportRejects .importDecl .topLevel
        selectedImport_success_ordinaryOutcome_sound
        selectedImport_reject_ordinaryOutcome_sound valuesResult
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      unfold ImportInternals.requireSelected at result
      cases elements : values.elements with
      | nil => simp [elements] at result
      | cons head tail => simp [elements, pure] at result

end Solcore.Syntax.Parser
