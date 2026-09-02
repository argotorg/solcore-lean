import Solcore.Syntax.DeclarativeSelectedImportOutcomeGrammar
import Solcore.Syntax.Parser.SelectedAliasOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedAliasOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinarySuccessSoundnessProperties

/-! Exact executable rejection reflection for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import rejection occurs first in its source, or
after an exact source success in its optional alias. -/
theorem selectedImport_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : selectedImport input = .reject failure rejected) :
    DeclarativeGrammar.SelectedImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold selectedImport at result
  cases sourceResult : selectorName .importDecl input with
  | invariant error => simp [bind, sourceResult] at result
  | reject sourceFailure sourceRejected =>
      simp only [bind, sourceResult] at result
      cases result
      exact .sourceRejected
        (selectorName_reject_ordinaryOutcome_sound .importDecl sourceResult)
  | ok source afterSource =>
      simp only [bind, sourceResult] at result
      have sourceParsed := selectorName_success_ordinaryOutcome_sound
        .importDecl sourceResult
      cases aliasResult : ImportInternals.selectedAlias afterSource with
      | invariant error => simp [aliasResult] at result
      | reject aliasFailure aliasRejected =>
          simp only [aliasResult] at result
          cases result
          exact .aliasRejected sourceParsed
            (selectedAlias_reject_ordinaryOutcome_sound aliasResult)
      | ok alias output => simp [aliasResult, pure] at result

end Solcore.Syntax.Parser
