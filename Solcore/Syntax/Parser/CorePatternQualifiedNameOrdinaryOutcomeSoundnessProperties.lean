import Solcore.Syntax.DeclarativeCorePatternQualifiedNameOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeQualifiedNameRejectionSoundnessProperties
import Solcore.Syntax.Parser.QualifiedNameSoundnessProperties

/-! Exact executable ordinary outcomes for qualified Core pattern paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every qualified pattern-path success follows the maximal ordinary
qualified-name relation. -/
theorem patternQualifiedName_success_ordinary_sound
    {input output : State} {path : QualifiedName}
    (result : qualifiedName .pattern .pattern input = .ok path output) :
    DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
      input.declarativeRemainder path output.declarativeRemainder :=
  qualifiedName_success_sound .pattern .pattern result

/-- Every qualified pattern-path rejection follows the exact first-or-dotted
identifier rejection trace. -/
theorem patternQualifiedName_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : qualifiedName .pattern .pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.PatternQualifiedNameRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  qualifiedName_reject_type_sound .pattern .pattern result

/-- Package both executable qualified pattern-path outcomes. -/
theorem patternQualifiedName_ordinaryOutcome_sound :
    (∀ {input output : State} {path : QualifiedName},
      qualifiedName .pattern .pattern input = .ok path output →
        DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      qualifiedName .pattern .pattern input = .reject failure rejected →
        DeclarativeGrammar.PatternQualifiedNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨patternQualifiedName_success_ordinary_sound,
    patternQualifiedName_reject_ordinary_sound⟩

/-- Re-export deterministic qualified pattern-path outcomes. -/
theorem patternQualifiedName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
      DeclarativeGrammar.PatternQualifiedNameRejects :=
  DeclarativeGrammar.patternQualifiedNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser.PatternInternals
