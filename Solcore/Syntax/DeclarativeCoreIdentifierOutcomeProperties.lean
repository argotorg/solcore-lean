import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Deterministic ordinary outcomes for one checked Core identifier. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Checked identifiers have a unique output remainder. -/
theorem IdentifierParses.output_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftToken, leftTokens, leftEndIndex, leftCursor⟩
  rcases rightParsed with ⟨rightToken, rightTokens, rightEndIndex,
    rightCursor⟩
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Checked-identifier rejection excludes checked-identifier success. -/
theorem IdentifierRejects.disjoint {input rejected : Remainder}
    (rejection : IdentifierRejects input rejected) :
    ¬ ∃ name output, IdentifierParses input name output := by
  cases rejection with
  | absent identifierAbsent =>
      rintro ⟨name, output, parsed⟩
      exact identifierAbsent ⟨name.span, name.value, parsed.1⟩

/-- Checked identifiers form a deterministic ordinary outcome. -/
theorem identifierDeterministicOutcomeSpec :
    DeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  successOutputUnique := IdentifierParses.output_unique
  successRejectDisjoint := IdentifierRejects.disjoint

end Solcore.Syntax.DeclarativeGrammar
