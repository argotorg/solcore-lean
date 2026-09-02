import Solcore.Syntax.DeclarativeTypeAliasParametersExactnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.TypeAliasParameterSoundnessProperties

/-! Exact executable outcomes for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful optional alias-parameter attempt follows its exact
prioritized ordinary grammar. -/
theorem parseTypeAliasParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : Option (DelimitedList Identifier)}
    (result : parseTypeAliasParameters input = .ok parameters output) :
    DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder :=
  parseTypeAliasParameters_success_sound result

/-- A rejected optional alias-parameter attempt has a present opening
parenthesis and the exact nested allow-empty, allow-trailing rejection. -/
theorem parseTypeAliasParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : parseTypeAliasParameters input = .reject failure rejected) :
    DeclarativeGrammar.OptionalTypeAliasParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseTypeAliasParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeAlias present with
      ⟨opening, openingResult⟩
    simp only [present, if_true] at result
    cases parametersResult : delimited .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias input with
    | invariant error => simp [parametersResult] at result
    | ok parameters output => simp [parametersResult, pure] at result
    | reject parametersFailure parametersRejected =>
        simp only [parametersResult] at result
        cases result
        exact .present
          ⟨opening.span,
            (symbol_ok_tokenAt .leftParen .typeAlias openingResult).1⟩
          (delimited_reject_sound .leftParen .rightParen true
            (identifier .parameter) DeclarativeGrammar.IdentifierParses
            DeclarativeGrammar.IdentifierRejects .typeAlias .typeAlias
            (identifier_success_sound .parameter)
            (identifier_reject_sound .parameter) parametersResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package optional alias-parameter success and exact rejection. -/
theorem parseTypeAliasParameters_ordinaryOutcome_sound :
    (∀ {input output : State}
      {parameters : Option (DelimitedList Identifier)},
      parseTypeAliasParameters input = .ok parameters output →
        DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
          input.declarativeRemainder parameters
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseTypeAliasParameters input = .reject failure rejected →
        DeclarativeGrammar.OptionalTypeAliasParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨parseTypeAliasParameters_success_ordinaryOutcome_sound,
    parseTypeAliasParameters_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional alias-parameter outcomes. -/
theorem parseTypeAliasParameters_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      DeclarativeGrammar.OptionalTypeAliasParametersRejects :=
  DeclarativeGrammar.optionalTypeAliasParametersDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for optional
type-alias parameters at the executable reflection boundary. -/
theorem parseTypeAliasParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      DeclarativeGrammar.OptionalTypeAliasParametersRejects :=
  DeclarativeGrammar.optionalTypeAliasParametersExactOutcomeSpec

/-- Two successful executable reflections have the same optional parameters
and final declarative remainder. -/
theorem parseTypeAliasParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option (DelimitedList Identifier)}
    (leftResult : parseTypeAliasParameters input = .ok left leftOutput)
    (rightResult : parseTypeAliasParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses.result_unique
    (parseTypeAliasParameters_success_ordinaryOutcome_sound leftResult)
    (parseTypeAliasParameters_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact declarative
endpoint. -/
theorem parseTypeAliasParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : parseTypeAliasParameters input =
      .reject leftFailure leftOutput)
    (rightResult : parseTypeAliasParameters input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalTypeAliasParametersRejects.output_unique
    (parseTypeAliasParameters_reject_ordinaryOutcome_sound leftResult)
    (parseTypeAliasParameters_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
