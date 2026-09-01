import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.TypeAlias

/-! Success soundness for optional transparent type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parameters follow their prioritized parenthesized grammar. -/
theorem parseTypeAliasParameters_success_sound
    {input next : State}
    {parameters : Option (DelimitedList Identifier)}
    (result : parseTypeAliasParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalTypeAliasParametersParses
      input.declarativeRemainder parameters next.declarativeRemainder := by
  unfold parseTypeAliasParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases valuesResult : delimited .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias input with
    | invariant error =>
        simp [valuesResult] at result
    | reject failure rejected =>
        simp [valuesResult] at result
    | ok values afterValues =>
        have valuesGrammar := delimited_allowEmpty_trailing_success_sound
          .leftParen .rightParen (identifier .parameter)
          DeclarativeGrammar.IdentifierParses .typeAlias .typeAlias
          (identifier_success_sound .parameter)
          (identifier_preservesTokenWindow .parameter) valuesResult
        simp only [valuesResult, pure] at result
        cases result
        exact .present valuesGrammar
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

end Solcore.Syntax.Parser
