import Solcore.Syntax.DeclarativeYulExpressionOrdinaryGrammar
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedFallbackRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLookaheadProperties
import Solcore.Syntax.Parser.YulNameOutcomeProperties

/-!
Executable ordinary-success reflection for the non-recovering inline-Yul
expression core.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful optional-call outcome records ordinary success or the
exact transactional rejection that caused `orElse` to rewind. -/
theorem optionalYulCallArguments_success_ordinary_sound
    (nested : Parser YulExpr)
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {arguments : Option (DelimitedList YulExpr)}
    (result : optionalYulCallArguments nested input = .ok arguments next) :
    DeclarativeGrammar.OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input.declarativeRemainder arguments
        next.declarativeRemainder := by
  unfold optionalYulCallArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : delimited .leftParen .rightParen true nested
        .yulExpression .yul input with
    | invariant error => simp [bind, argumentsResult] at result
    | reject failure failed =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .yulExpression
            present with ⟨openingToken, openingResult⟩
        exact .rewound openingToken.span
          (symbol_ok_tokenAt .leftParen .yulExpression openingResult).1
          ⟨failed.declarativeRemainder,
            yulCallArguments_reject_sound nested ordinaryParses nestedRejects
              nestedSuccessSound nestedRejectSound argumentsResult⟩
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present
          (delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
            nested ordinaryParses .yulExpression .yul nestedSuccessSound
              nestedShape argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

private theorem yulNamedExpression_success_ordinary_sound
    (nested : Parser YulExpr)
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input afterName next : State} {name : YulIdentifier}
    {arguments : Option (DelimitedList YulExpr)}
    (nameResult : yulName input = .ok name afterName)
    (argumentsResult : optionalYulCallArguments nested afterName =
      .ok arguments next) :
    ∃ expression,
      (match arguments with
        | none => expression = {
            span := name.span
            value := .identifier name
          }
        | some values => expression = {
            span := SourceSpan.cover name.span values.span
            value := .call name values
          }) ∧
      DeclarativeGrammar.YulNamedExpressionOrdinaryParses ordinaryParses
        nestedRejects input.declarativeRemainder expression
          next.declarativeRemainder := by
  have nameParsed := yulName_success_ordinary_sound nameResult
  have argumentsParsed := optionalYulCallArguments_success_ordinary_sound
    nested ordinaryParses nestedRejects nestedSuccessSound nestedRejectSound
      nestedShape argumentsResult
  cases arguments with
  | none => exact ⟨_, rfl, .identifier nameParsed argumentsParsed⟩
  | some values => exact ⟨_, rfl, .call nameParsed argumentsParsed⟩

private theorem rejectedMeta_success_ordinary_sound
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input next : State} {expression : YulExpr}
    (literalAbsent : ¬ DeclarativeGrammar.YulLiteralStartsAt
      input.declarativeRemainder)
    (nameAbsent : ¬ DeclarativeGrammar.YulNameStartsAt
      input.declarativeRemainder)
    (result : rejectedMeta input = .ok expression next) :
    DeclarativeGrammar.YulExpressionCoreOrdinaryParses ordinaryParses
      nestedRejects input.declarativeRemainder expression
        next.declarativeRemainder := by
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case yulMetaBacktick text =>
        cases result
        exact .metaBacktick literalAbsent nameAbsent
          (tokenAt_of_peek?_eq_some found)
      case yulMetaInterpolation text =>
        cases result
        exact .metaInterpolation literalAbsent nameAbsent
          (tokenAt_of_peek?_eq_some found)

/-- Every executable core success follows the ordinary literal-before-name
grammar, including diagnosed names and forbidden source meta tokens. -/
theorem yulExpressionCore_success_ordinary_sound
    (nested : Parser YulExpr)
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {expression : YulExpr}
    (result : yulExpressionCore nested input = .ok expression next) :
    DeclarativeGrammar.YulExpressionCoreOrdinaryParses ordinaryParses
      nestedRejects input.declarativeRemainder expression
        next.declarativeRemainder := by
  unfold yulExpressionCore at result
  split at result
  next literalPresent =>
    cases literalResult : yulLiteral input with
    | invariant error => simp [literalResult] at result
    | reject failure rejected => simp [literalResult] at result
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        cases result
        exact .literal (yulLiteral_success_sound literalResult)
  next literalAbsent =>
    have noLiteral := not_yulLiteralStartsAt_of_startsYulLiteral_eq_false
      (Bool.eq_false_iff.mpr literalAbsent)
    split at result
    next namePresent =>
      cases nameResult : yulName input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              rcases yulNamedExpression_success_ordinary_sound nested
                  ordinaryParses nestedRejects nestedSuccessSound
                    nestedRejectSound nestedShape nameResult argumentsResult with
                ⟨named, namedEq, namedParsed⟩
              cases arguments <;> cases result <;> cases namedEq
              all_goals exact .named noLiteral namedParsed
    next nameAbsent =>
      have noName := not_yulNameStartsAt_of_startsYulName_eq_false
        (Bool.eq_false_iff.mpr nameAbsent)
      split at result <;> try {
        exact rejectedMeta_success_ordinary_sound ordinaryParses nestedRejects
          noLiteral noName result }
      unfold rejectAt at result
      contradiction

end Solcore.Syntax.Parser
