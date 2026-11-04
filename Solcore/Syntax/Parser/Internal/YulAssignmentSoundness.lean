import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.YulTotality
import Solcore.Syntax.Grammar.YulOrdinary
import Solcore.Syntax.Parser.Internal.PatternStepSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.YulBlockSoundness
import Solcore.Syntax.Internal.YulStatementOutcomes
import Solcore.Syntax.Parser.Internal.YulStatementSoundness
import Solcore.Syntax.Parser.Internal.YulSwitchSoundness
import Solcore.Syntax.Grammar.YulFuel

/-!
Soundness of the parsers of Yul assignments and expressions at fuel: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionRejectionSoundnessProperties
/-!
Exact executable rejection bridges for inline-Yul expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulLiteral_ne_reject_of_startsYulLiteral
    {input rejected : State} {failure : Failure}
    (starts : startsYulLiteral input = true)
    (result : yulLiteral input = .reject failure rejected) : False := by
  unfold startsYulLiteral State.peekKind? at starts
  unfold yulLiteral at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals contradiction

private theorem yulName_ne_reject_of_startsYulName
    {input rejected : State} {failure : Failure}
    (starts : startsYulName input = true)
    (result : yulName input = .reject failure rejected) : False := by
  unfold startsYulName State.peekKind? at starts
  unfold yulName at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case identifier text =>
        unfold identifier rawIdentifier at result
        simp only [found] at result
        split at result <;> contradiction
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { contradiction }
      case symbol symbol =>
        cases symbol <;> simp only at starts result
        all_goals try { contradiction }

private theorem optionalYulCallArguments_ne_reject
    (nested : Parser YulExpr) {input rejected : State} {failure : Failure}
    (result : optionalYulCallArguments nested input =
      .reject failure rejected) : False := by
  unfold optionalYulCallArguments at result
  split at result
  · unfold orElse at result
    cases argumentsResult :
        (do pure (some (← delimited .leftParen .rightParen true nested
          .yulExpression .yul))) input with
    | ok arguments next =>
        rw [argumentsResult] at result
        contradiction
    | reject innerFailure failed =>
        rw [argumentsResult] at result
        contradiction
    | invariant error =>
        rw [argumentsResult] at result
        contradiction
  · contradiction

private theorem rejectedMeta_ne_reject_of_meta_start
    {input rejected : State} {failure : Failure} {kind : TokenKind}
    (metaStart : (∃ text, kind = .yulMetaBacktick text) ∨
      (∃ text, kind = .yulMetaInterpolation text))
    (found : input.peekKind? = some kind)
    (result : rejectedMeta input = .reject failure rejected) : False := by
  rcases metaStart with ⟨text, rfl⟩ | ⟨text, rfl⟩
  · unfold State.peekKind? at found
    cases tokenFound : input.peek? with
    | none => simp [tokenFound] at found
    | some token =>
        have tokenKind : token.value = .yulMetaBacktick text := by
          simpa [tokenFound] using found
        unfold rejectedMeta at result
        simp only [tokenFound] at result
        rcases token with ⟨span, value⟩
        simp only at tokenKind
        subst value
        contradiction
  ·
    unfold State.peekKind? at found
    cases tokenFound : input.peek? with
    | none => simp [tokenFound] at found
    | some token =>
        have tokenKind : token.value = .yulMetaInterpolation text := by
          simpa [tokenFound] using found
        unfold rejectedMeta at result
        simp only [tokenFound] at result
        rcases token with ⟨span, value⟩
        simp only at tokenKind
        subst value
        contradiction

/-- Core rejection can only be the unchanged final `rejectAt`; guarded leaf
and transactional argument branches cannot reject. -/
theorem yulExpressionCore_reject_state_eq
    (nested : Parser YulExpr) {input rejected : State} {failure : Failure}
    (result : yulExpressionCore nested input = .reject failure rejected) :
    rejected = input := by
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | ok literal next => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
    | reject literalFailure failed =>
        exact False.elim
          (yulLiteral_ne_reject_of_startsYulLiteral ‹_› literalResult)
  · split at result
    · cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments next =>
              cases arguments <;> simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
          | reject argumentsFailure failed =>
              exact False.elim
                (optionalYulCallArguments_ne_reject nested argumentsResult)
      | reject nameFailure failed =>
          exact False.elim
            (yulName_ne_reject_of_startsYulName ‹_› nameResult)
      | invariant error => simp [nameResult] at result
    · cases found : input.peekKind? with
      | none =>
          simp only [found] at result
          unfold rejectAt at result
          cases result
          rfl
      | some kind =>
          cases kind <;> simp only [found] at result
          all_goals try {
            unfold rejectAt at result
            cases result
            rfl
          }
          case yulMetaBacktick text =>
            exact False.elim (rejectedMeta_ne_reject_of_meta_start
              (kind := .yulMetaBacktick text) (Or.inl ⟨text, rfl⟩)
              found result)
          case yulMetaInterpolation text =>
            exact False.elim (rejectedMeta_ne_reject_of_meta_start
              (kind := .yulMetaInterpolation text) (Or.inr ⟨text, rfl⟩)
              found result)

private theorem yulExpressionRejects_of_symbol
    (value : Symbol) {input : State}
    (allowed : value = .comma ∨ value = .rightParen ∨ value = .rightBrace)
    (present : isSymbol input value = true) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .yulExpression present with
    ⟨token, parsed⟩
  have exactToken := (symbol_ok_tokenAt value .yulExpression parsed).1
  rcases allowed with rfl | rfl | rfl
  · exact .comma exactToken
  · exact .rightParen exactToken
  · exact .rightBrace exactToken

private theorem yulExpressionRejects_of_isBoundary
    (input : State) (boundary : YulExpressionInternals.isBoundary input = true) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · by_cases comma : isSymbol input .comma = true
    · exact yulExpressionRejects_of_symbol .comma (Or.inl rfl) comma
    · by_cases rightParen : isSymbol input .rightParen = true
      · exact yulExpressionRejects_of_symbol .rightParen
          (Or.inr (Or.inl rfl)) rightParen
      · by_cases rightBrace : isSymbol input .rightBrace = true
        · exact yulExpressionRejects_of_symbol .rightBrace
            (Or.inr (Or.inr rfl)) rightBrace
        · have notAtEnd : input.atEnd = false := by
            unfold State.atEnd
            exact decide_eq_false atEnd
          have commaFalse : isSymbol input .comma = false :=
            Bool.eq_false_iff.mpr comma
          have rightParenFalse : isSymbol input .rightParen = false :=
            Bool.eq_false_iff.mpr rightParen
          have rightBraceFalse : isSymbol input .rightBrace = false :=
            Bool.eq_false_iff.mpr rightBrace
          simp [YulExpressionInternals.isBoundary, notAtEnd, commaFalse,
            rightParenFalse, rightBraceFalse] at boundary

private theorem yulExpressionRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.YulExpressionRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

namespace YulExpressionInternals

/-- Every recovering-layer rejection follows the exact non-consuming binary
Yul-expression rejection grammar. -/
theorem layer_reject_sound (nested : Parser YulExpr)
    {input rejected : State} {failure : Failure}
    (result : layer nested input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok expression next => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failedState =>
      simp only [coreResult] at result
      have failedEq := yulExpressionCore_reject_state_eq nested coreResult
      subst failedState
      change (if isBoundary input then .reject coreFailure input else
        match input.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit coreFailure.toDiagnostic)
        | none => .reject coreFailure input) =
          .reject failure rejected at result
      by_cases boundary : isBoundary input = true
      · simp only [boundary, ↓reduceIte] at result
        cases result
        exact yulExpressionRejects_of_isBoundary input boundary
      · have boundaryFalse : isBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, ↓reduceIte] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            cases result
            exact yulExpressionRejects_of_advance?_eq_none input advanced
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases recoverAux_production_exists_ok token.span token.span
                (afterToken.emit coreFailure.toDiagnostic) with
              ⟨expression, final, recovered⟩
            have sameRemaining :
                (afterToken.emit coreFailure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [sameRemaining] at recovered
            rw [recovered] at result
            contradiction

/-- Positive recursive fuel preserves the exact rejection relation. -/
theorem withFuel_succ_reject_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : withFuel (fuel + 1) input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  exact layer_reject_sound (withFuel fuel) result

end YulExpressionInternals

/-- The public recursive inline-Yul parser exposes the same exact binary
rejection relation. -/
theorem yulExpression_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulExpression input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_succ_reject_sound
    input.remainingCount result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionCoreOrdinarySoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionCoreFinalRejectionProperties
/-! Exact reflection of the final `rejectAt` branch in the Yul core parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem optionalYulCallArguments_ne_reject_variant
    (nested : Parser YulExpr) {input rejected : State} {failure : Failure}
    (result : optionalYulCallArguments nested input =
      .reject failure rejected) : False := by
  unfold optionalYulCallArguments at result
  split at result
  · unfold orElse at result
    cases argumentsResult :
        (do pure (some (← delimited .leftParen .rightParen true nested
          .yulExpression .yul))) input with
    | ok arguments next => rw [argumentsResult] at result; contradiction
    | reject innerFailure failed =>
        rw [argumentsResult] at result
        contradiction
    | invariant error => rw [argumentsResult] at result; contradiction
  · contradiction

private theorem peekKind?_eq_some_of_tokenAt {input : State} {token : Token}
    (present : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor token) : input.peekKind? = some token.value := by
  unfold State.peekKind? State.peek?
  simp only [present.1, ↓reduceIte, present.2, Option.map_some]

private theorem not_yulMetaStartsAt_of_peekKind?_eq
    {input : State} {foundKind : Option TokenKind}
    (found : input.peekKind? = foundKind)
    (backtickAbsent : ∀ text, foundKind ≠ some (.yulMetaBacktick text))
    (interpolationAbsent :
      ∀ text, foundKind ≠ some (.yulMetaInterpolation text)) :
    ¬ DeclarativeGrammar.YulMetaStartsAt input.declarativeRemainder := by
  rintro (⟨span, text, token⟩ | ⟨span, text, token⟩)
  · have executable := peekKind?_eq_some_of_tokenAt token
    rw [found] at executable
    exact backtickAbsent text executable
  · have executable := peekKind?_eq_some_of_tokenAt token
    rw [found] at executable
    exact interpolationAbsent text executable

/-- Every core rejection selects the literal/name/meta-absent final branch. -/
theorem yulExpressionCore_reject_final_sound
    (nested : Parser YulExpr) {input rejected : State} {failure : Failure}
    (result : yulExpressionCore nested input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionCoreFinalRejects
      input.declarativeRemainder := by
  unfold yulExpressionCore at result
  split at result
  next literalPresent =>
    cases literalResult : yulLiteral input with
    | ok literal next => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
    | reject literalFailure failed =>
        exact False.elim
          (yulLiteral_ne_reject_of_startsYulLiteral literalPresent
            literalResult)
  next literalAbsent =>
    have noLiteral := not_yulLiteralStartsAt_of_startsYulLiteral_eq_false
      (Bool.eq_false_iff.mpr literalAbsent)
    split at result
    next namePresent =>
      cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments next =>
              cases arguments <;> simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
          | reject argumentsFailure failed =>
              exact False.elim
                (optionalYulCallArguments_ne_reject_variant nested argumentsResult)
      | reject nameFailure failed =>
          exact False.elim
            (yulName_ne_reject_of_startsYulName namePresent nameResult)
      | invariant error => simp [nameResult] at result
    next nameAbsent =>
      have noName := not_yulNameStartsAt_of_startsYulName_eq_false
        (Bool.eq_false_iff.mpr nameAbsent)
      cases found : input.peekKind? with
      | none =>
          simp only [found] at result
          unfold rejectAt at result
          cases result
          exact .final noLiteral noName
            (not_yulMetaStartsAt_of_peekKind?_eq found (by simp) (by simp))
      | some kind =>
          cases kind <;> simp only [found] at result
          all_goals try {
            unfold rejectAt at result
            cases result
            exact .final noLiteral noName
              (not_yulMetaStartsAt_of_peekKind?_eq found (by simp) (by simp)) }
          case yulMetaBacktick text =>
            exact False.elim (rejectedMeta_ne_reject_of_meta_start
              (kind := .yulMetaBacktick text) (Or.inl ⟨text, rfl⟩)
              found result)
          case yulMetaInterpolation text =>
            exact False.elim (rejectedMeta_ne_reject_of_meta_start
              (kind := .yulMetaInterpolation text) (Or.inr ⟨text, rfl⟩)
              found result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionRecoveryOrdinarySoundnessProperties
/-! Exact ordinary-success reflection for inline-Yul expression recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

/-- A present non-boundary token selects recovery continuation rather than a
stop constructor. -/
theorem no_yulExpressionRejects_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : YulExpressionInternals.isBoundary input = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  intro rejected
  have current := tokenAt_of_peek?_eq_some found
  cases rejected with
  | windowEnd atEnd =>
      change input.window.endIndex ≤ input.cursor at atEnd
      have inside := State.cursor_lt_endIndex_of_peek?_eq_some found
      omega
  | comma commaToken =>
      have present := isSymbol_eq_true_of_tokenAt .comma commaToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | rightParen rightParenToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightParen rightParenToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | rightBrace rightBraceToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightBrace rightBraceToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

namespace YulExpressionInternals

/-- Every successful recovery execution follows the exact boundary-prioritized
scan relation. -/
theorem recoverAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input expression output,
      recoverAux first last fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionRecoveryScanParses first last
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input expression output result
      simp [recoverAux] at result
  | succ fuel inductionHypothesis =>
      intro last input expression output result
      unfold recoverAux at result
      by_cases boundary : isBoundary input = true
      · simp only [boundary, if_true] at result
        unfold finishRecovered at result
        cases result
        exact .stop (yulExpressionRejects_of_isBoundary input boundary)
      · have boundaryFalse : isBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecovered at result
            cases result
            exact .stop (yulExpressionRejects_of_advance?_eq_none input
              advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next expression output
              result
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulExpressionRejects_of_nonBoundary_token
              boundaryFalse found
            rw [nextEq] at tail
            exact .next continues current tail

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionLayerOrdinarySoundnessProperties
/-! Ordinary-success reflection for one recovering inline-Yul layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every successful recovering layer follows either an ordinary core success
or the exact final-reject, first-token, recovery-scan branch. -/
theorem layer_success_ordinary_sound
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
    {input output : State} {expression : YulExpr}
    (result : layer nested input = .ok expression output) :
    DeclarativeGrammar.YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok coreExpression afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core (yulExpressionCore_success_ordinary_sound nested
        ordinaryParses nestedRejects nestedSuccessSound nestedRejectSound
          nestedShape coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      have failedEq := yulExpressionCore_reject_state_eq nested coreResult
      have coreRejected := yulExpressionCore_reject_final_sound nested
        coreResult
      subst failedState
      change (if isBoundary input then .reject failure input else
        match input.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => .reject failure input) = .ok expression output at result
      by_cases boundary : isBoundary input = true
      · simp only [boundary, if_true] at result
        contradiction
      · have boundaryFalse : isBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, afterEq⟩
            have current := tokenAt_of_peek?_eq_some found
            have continues :=
              no_yulExpressionRejects_of_nonBoundary_token boundaryFalse found
            have scan := recoverAux_success_ordinary_sound token.span
              (afterToken.remainingCount + 1) token.span
                (afterToken.emit failure.toDiagnostic) expression output result
            rw [afterEq] at scan
            exact .recovered coreRejected continues current scan

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionFuelOrdinarySoundnessProperties
/-!
Fuel-indexed executable reflection for ordinary inline-Yul expression
successes, rejections, and diagnostic preservation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every executable fuel-level rejection follows that level's exact binary
rejection relation.  Fuel zero cannot reject because it returns an invariant. -/
theorem withFuel_reject_fuel_sound : ∀ fuel,
    ∀ {input rejected : State} {failure : Failure},
      withFuel fuel input = .reject failure rejected →
      DeclarativeGrammar.YulExpressionRejectsWithFuel fuel
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  cases fuel with
  | zero =>
      intro input rejected failure result
      simp [withFuel] at result
  | succ fuel =>
      intro input rejected failure result
      apply DeclarativeGrammar.YulExpressionRejectsWithFuel.succ_iff.mpr
      exact withFuel_succ_reject_sound fuel result

/-- Every successful executable fuel level follows the corresponding broad
ordinary-success relation. -/
theorem withFuel_success_ordinary_fuel_sound : ∀ fuel,
    ∀ {input output : State} {expression : YulExpr},
      withFuel fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output expression result
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output expression result
      apply
        DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.succ_iff.mpr
      exact layer_success_ordinary_sound (withFuel fuel)
        (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel)
        inductionHypothesis (withFuel_reject_fuel_sound fuel)
        (withFuel_preservesTokenWindow fuel) result

/-- Recursive diagnostic reflection used by the clean fuel-indexed proof.
This theorem is kept distinct from the statement-layer compatibility export. -/
theorem withFuel_reflectsDiagnosticFreeForDeclarativeSoundness : ∀ fuel,
    Parser.ReflectsDiagnosticFreeOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression output result diagnosticFree
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
        (withFuel fuel) inductionHypothesis

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionFuelCleanSoundnessProperties
/-! Diagnostic-free soundness for the fuel-indexed inline-Yul expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every diagnostic-free executable success follows the clean grammar at the
same fuel.  Transactional argument rejection is instantiated from the exact
ordinary success/rejection pair at the preceding level. -/
theorem withFuel_success_clean_fuel_sound : ∀ fuel,
    ∀ {input output : State} {expression : YulExpr},
      output.diagnosticsRev = [] →
      withFuel fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output expression diagnosticFree result
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output expression diagnosticFree result
      apply DeclarativeGrammar.YulExpressionCleanParsesWithFuel.succ_iff.mpr
      apply yulExpressionLayer_success_sound
        (withFuel fuel)
        (DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel)
        (DeclarativeGrammar.yulExpressionCallArgumentsFallbackWithFuel fuel)
        (withFuel_reflectsDiagnosticFreeForDeclarativeSoundness fuel)
        inductionHypothesis
        (withFuel_preservesTokenWindow fuel)
      · intro argumentsInput argumentsFailed argumentsFailure
          argumentsResult
        exact yulCallArguments_fallback_reject_sound
          (withFuel fuel)
          (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulExpressionCleanParsesWithFuel fuel)
          (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel)
          (DeclarativeGrammar.yulExpressionOutcomeSpecWithFuel fuel)
          (fun parsed => parsed.toOrdinary)
          (withFuel_success_ordinary_fuel_sound fuel)
          (withFuel_reject_fuel_sound fuel) argumentsResult
      · exact diagnosticFree
      · exact result

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
/-! Public executable bridges for the concrete recursive Yul-expression grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public parser success follows the concrete ordinary recursive
grammar selected from the input token remainder. -/
theorem yulExpression_success_ordinary_sound
    {input output : State} {expression : YulExpr}
    (result : yulExpression input = .ok expression output) :
    DeclarativeGrammar.YulExpressionOrdinaryParses
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionOrdinaryParses,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_success_ordinary_fuel_sound
        (input.remainingCount + 1) result

/-- Every public ordinary rejection follows the concrete public fuel-indexed
rejection relation. -/
theorem yulExpression_reject_public_sound
    {input rejected : State} {failure : Failure}
    (result : yulExpression input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionPublicRejects,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_reject_fuel_sound
        (input.remainingCount + 1) result

/-- Every diagnostic-free public parser success follows the concrete clean
recursive grammar. -/
theorem yulExpression_success_clean_sound
    {input output : State} {expression : YulExpr}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulExpression input = .ok expression output) :
    DeclarativeGrammar.YulExpressionParses input.declarativeRemainder
      expression output.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionParses,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_success_clean_fuel_sound
        (input.remainingCount + 1) diagnosticFree result

/-- Public diagnostic reflection used by the concrete declarative bridge. -/
theorem yulExpression_public_reflectsDiagnosticFreeForDeclarativeSoundness :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpression := by
  intro input expression output result diagnosticFree
  unfold yulExpression at result
  exact
    YulExpressionInternals.withFuel_reflectsDiagnosticFreeForDeclarativeSoundness
      (input.remainingCount + 1) input expression output result diagnosticFree

/-- Deterministic ordinary outcomes of the public grammar, stated with its
fuel-indexed public rejection relation. -/
theorem yulExpression_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionPublicRejects :=
  DeclarativeGrammar.yulExpressionPublicOutcomeSpec

/-- The same public outcome contract against the concrete boundary rejection
relation consumed by recursive transactional parsers. -/
theorem yulExpression_publicConcreteOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionRejects :=
  DeclarativeGrammar.yulExpressionPublicDeterministicOutcomeSpec

namespace YulExpressionInternals

/-- Re-export exact outcomes at each fixed recursive expression fuel. -/
theorem withFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel) :=
  DeclarativeGrammar.yulExpressionExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel executable successes agree on their complete declarative result. -/
theorem withFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : withFuel fuel input = .ok left leftOutput)
    (rightResult : withFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.result_unique
    (withFuel_success_ordinary_fuel_sound fuel leftResult)
    (withFuel_success_ordinary_fuel_sound fuel rightResult)

/-- Fixed-fuel executable rejections agree on their exact declarative endpoint. -/
theorem withFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : withFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : withFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionRejectsWithFuel.output_unique
    (withFuel_reject_fuel_sound fuel leftResult)
    (withFuel_reject_fuel_sound fuel rightResult)

end YulExpressionInternals

/-- Re-export exact public ordinary outcomes with input-selected fuel. -/
theorem yulExpression_publicExactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionPublicRejects :=
  DeclarativeGrammar.yulExpressionPublicExactOutcomeSpec

/-- Exact public expression outcomes against the concrete boundary rejection. -/
theorem yulExpression_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionRejects :=
  DeclarativeGrammar.yulExpressionExactOutcomeSpec

/-- Public executable expression successes agree on their AST and remainder. -/
theorem yulExpression_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : yulExpression input = .ok left leftOutput)
    (rightResult : yulExpression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionOrdinaryParses.result_unique
    (yulExpression_success_ordinary_sound leftResult)
    (yulExpression_success_ordinary_sound rightResult)

/-- Public executable expression rejections agree on their complete endpoint. -/
theorem yulExpression_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulExpression input = .reject leftFailure leftOutput)
    (rightResult : yulExpression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionPublicRejects.output_unique
    (yulExpression_reject_public_sound leftResult)
    (yulExpression_reject_public_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementBasicOrdinaryOutcomeSoundnessProperties
/-!
Unconditional executable ordinary-success and exact-rejection bridges for the
nonrecursive basic inline-Yul statement primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_eq_ok_of_isKeyword_eq_true_variant (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, if_true]

private theorem keyword_reject_tokenKindAbsentAt_variant (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true_variant value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq_variant (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input := by
  unfold keyword at result
  exact acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

/-- Every executable expression-statement success follows the public ordinary
expression relation, independently of diagnostics. -/
theorem yulExpressionStatement_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulExpressionStatement input = .ok statement output) :
    DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulExpressionStatement at result
  cases expressionResult : yulExpression input with
  | invariant error => simp [bind, expressionResult] at result
  | reject failure rejected => simp [bind, expressionResult] at result
  | ok expression afterExpression =>
      simp only [bind, expressionResult, pure] at result
      cases result
      exact .parsed (yulExpression_success_ordinary_sound expressionResult)

/-- Every executable expression-statement rejection retains the exact public
expression rejection remainder. -/
theorem yulExpressionStatement_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulExpressionStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionStatementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulExpressionStatement at result
  cases expressionResult : yulExpression input with
  | invariant error => simp [bind, expressionResult] at result
  | ok expression afterExpression =>
      simp [bind, expressionResult, pure] at result
  | reject expressionFailure expressionRejected =>
      simp only [bind, expressionResult] at result
      cases result
      exact .expressionRejected (yulExpression_reject_sound expressionResult)

/-- Every executable source-level `return(...)` success preserves the exact
synthesized call, span, and allow-empty/trailing ordinary arguments. -/
theorem yulReturnBuiltin_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulReturnBuiltin input = .ok statement output) :
    DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  cases markerResult : keyword .returnKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases argumentsResult : delimited .leftParen .rightParen true yulExpression
          .yulExpression .yul afterMarker with
      | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp only [argumentsResult, pure] at result
          cases result
          exact .parsed marker.span
            (keyword_success_exactTokenParses .returnKw .yulStatement
              markerResult)
            (delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
              yulExpression DeclarativeGrammar.YulExpressionOrdinaryParses
              .yulExpression .yul yulExpression_success_ordinary_sound
              yulExpression_preservesTokenWindow argumentsResult)

/-- Every executable source-level `return(...)` rejection records the exact
missing keyword or rejected allow-empty/trailing argument remainder. -/
theorem yulReturnBuiltin_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulReturnBuiltin input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnBuiltinRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  cases markerResult : keyword .returnKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq_variant .returnKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt_variant .returnKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases argumentsResult : delimited .leftParen .rightParen true yulExpression
          .yulExpression .yul afterMarker with
      | invariant error => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp [argumentsResult, pure] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected marker.span
            (keyword_success_exactTokenParses .returnKw .yulStatement
              markerResult)
            (delimited_reject_sound .leftParen .rightParen true yulExpression
              DeclarativeGrammar.YulExpressionOrdinaryParses
              DeclarativeGrammar.YulExpressionRejects .yulExpression .yul
              yulExpression_success_ordinary_sound yulExpression_reject_sound
              argumentsResult)

/-- Every executable keyword-only control success is one exact ordinary token
transition. -/
theorem yulControlToken_success_ordinary_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input output : State} {statement : YulStmt}
    (result : yulControlToken keywordValue statementValue input =
      .ok statement output) :
    DeclarativeGrammar.YulControlTokenOrdinaryParses keywordValue statementValue
      input.declarativeRemainder statement output.declarativeRemainder :=
  yulControlToken_success_sound keywordValue statementValue result

/-- Every executable keyword-only control rejection is nonconsuming exact
evidence that its keyword is absent. -/
theorem yulControlToken_reject_ordinaryOutcome_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input rejected : State} {failure : Failure}
    (result : yulControlToken keywordValue statementValue input =
      .reject failure rejected) :
    DeclarativeGrammar.YulControlTokenRejects keywordValue
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulControlToken at result
  cases markerResult : keyword keywordValue .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | ok marker afterMarker => simp [bind, markerResult, pure] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq_variant keywordValue
        .yulStatement markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt_variant keywordValue .yulStatement
          markerResult)

/-- Executable expression-statement outcomes expose their declarative contract. -/
theorem yulExpressionStatement_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      DeclarativeGrammar.YulExpressionStatementRejects :=
  DeclarativeGrammar.yulExpressionStatementDeterministicOutcomeSpec

/-- Executable source-level return outcomes expose their declarative contract. -/
theorem yulReturnBuiltin_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
      DeclarativeGrammar.YulReturnBuiltinRejects :=
  DeclarativeGrammar.yulReturnBuiltinDeterministicOutcomeSpec

/-- Executable keyword-only controls expose their declarative contract. -/
theorem yulControlToken_publicOutcomeSpec
    (keywordValue : HardKeyword) (statementValue : YulStmtValue) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.YulControlTokenOrdinaryParses keywordValue
        statementValue)
      (DeclarativeGrammar.YulControlTokenRejects keywordValue) :=
  DeclarativeGrammar.yulControlTokenDeterministicOutcomeSpec keywordValue
    statementValue

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulAssignmentRejectionSoundnessProperties
/-!
Exact executable rejection bridges for transactional inline-Yul assignment
attempts.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment rejection records the exact names, operator,
or expression stage that rejected. -/
theorem yulAssignment_reject_sound
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulExpression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulAssignment at result
  cases namesResult : yulNames input with
  | invariant error => simp [bind, namesResult] at result
  | reject namesFailure namesRejected =>
      simp only [bind, namesResult] at result
      cases result
      exact .namesRejected (yulNames_reject_sound namesResult)
  | ok names afterNames =>
      simp only [bind, namesResult] at result
      have namesParsed := yulNames_success_ordinary_sound namesResult
      cases operatorResult : symbol .colonEqual .yulStatement afterNames with
      | invariant error => simp [operatorResult] at result
      | reject operatorFailure operatorRejected =>
          have operatorRejectedEq := symbol_reject_state_eq .colonEqual
            .yulStatement operatorResult
          subst operatorRejected
          simp only [operatorResult] at result
          cases result
          exact .operatorAbsent namesParsed
            (symbol_reject_tokenKindAbsentAt .colonEqual .yulStatement
              operatorResult)
      | ok operator afterOperator =>
          simp only [operatorResult] at result
          have operatorParsed := symbol_success_exactTokenParses .colonEqual
            .yulStatement operatorResult
          cases valueResult : yulExpression afterOperator with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp only [valueResult] at result
              cases result
              exact .expressionRejected operator.span namesParsed
                operatorParsed (expressionRejectSound valueResult)
          | ok value afterValue => simp [valueResult, pure] at result

/-- Public inline-Yul expressions instantiate the abstract assignment
rejection bridge with their exact recovery-boundary rejection relation. -/
theorem yulAssignment_public_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects
      DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  yulAssignment_reject_sound DeclarativeGrammar.YulExpressionRejects
    yulExpression_reject_sound result

/-- A transactional rejection supplies the unary rejection predicate of the
fallback built from any compatible deterministic expression outcomes. -/
theorem yulAssignment_fallback_reject_sound
    (ordinaryExpression cleanExpression :
      DeclarativeGrammar.Remainder → YulExpr →
        DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      ordinaryExpression expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulExpression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    (DeclarativeGrammar.YulAssignmentFallbackSpec.ofOutcomes
      ordinaryExpression cleanExpression expressionRejects outcomes
        cleanToOrdinary).rejects input.declarativeRemainder :=
  ⟨rejected.declarativeRemainder,
    yulAssignment_reject_sound expressionRejects expressionRejectSound
      result⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulAssignmentOrdinarySoundnessProperties
/-!
Executable ordinary-success and rejection bridges for public inline-Yul
assignment outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment success follows the exact ordinary public
assignment grammar, without a diagnostic-freedom premise. -/
theorem yulAssignment_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulAssignment input = .ok statement output) :
    DeclarativeGrammar.YulAssignmentOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulAssignment at result
  cases namesResult : yulNames input with
  | invariant error => simp [bind, namesResult] at result
  | reject namesFailure namesRejected =>
      simp [bind, namesResult] at result
  | ok names afterNames =>
      simp only [bind, namesResult] at result
      cases operatorResult : symbol .colonEqual .yulStatement afterNames with
      | invariant error => simp [operatorResult] at result
      | reject operatorFailure operatorRejected =>
          simp [operatorResult] at result
      | ok operator afterOperator =>
          simp only [operatorResult] at result
          cases valueResult : yulExpression afterOperator with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp [valueResult] at result
          | ok value afterValue =>
              simp only [valueResult, pure] at result
              cases result
              exact .parsed operator.span
                (yulNames_success_ordinary_sound namesResult)
                (symbol_success_exactTokenParses .colonEqual .yulStatement
                  operatorResult)
                (yulExpression_success_ordinary_sound valueResult)

/-- Every executable assignment rejection follows the rejection half of the
same public deterministic outcome contract. -/
theorem yulAssignment_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.YulAssignmentRejects
      DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  yulAssignment_public_reject_sound result

/-- Deterministic ordinary outcome contract exposed beside the executable
success and rejection bridges. -/
theorem yulAssignment_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulAssignmentOrdinaryParses
      (DeclarativeGrammar.YulAssignmentRejects
        DeclarativeGrammar.YulExpressionRejects) :=
  DeclarativeGrammar.yulAssignmentDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreSoundnessProperties
/-! Exact diagnostic-free soundness for `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every clean core-dispatch success follows its exact prioritized branch. -/
theorem yulStatementCore_success_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementCore nested input = .ok value next) :
    DeclarativeGrammar.YulStatementCoreParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    have primary :=
      recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
        (yulBlockStatement nested) yulExpressionStatement result diagnosticFree
    exact .block .start (yulBlockStatement_success_sound nested
      statementParses nestedReflects nestedSound diagnosticFree primary)
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard :=
      .afterBlock .start
        (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      have primary :=
        recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
          yulLetStatement yulExpressionStatement result diagnosticFree
      exact .letDecl beforeLet (yulLetStatement_success_sound expressionParses
        expressionSound diagnosticFree primary)
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard :=
        .afterLet beforeLet
          (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        have primary :=
          recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
            (yulIfStatement nested) yulExpressionStatement result
              diagnosticFree
        exact .ifThen beforeIf (yulIfStatement_success_sound nested
          statementParses expressionParses nestedReflects nestedSound
            expressionSound diagnosticFree primary)
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard :=
          .afterIf beforeIf
            (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have primary :=
            recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
              (yulForStatement nested) yulExpressionStatement result
                diagnosticFree
          exact .forLoop beforeFor (yulForStatement_success_sound nested
            statementParses expressionParses nestedReflects nestedSound
              expressionSound diagnosticFree primary)
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard :=
            .afterFor beforeFor
              (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            have primary :=
              recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                (yulSwitchStatement nested) yulExpressionStatement result
                  diagnosticFree
            exact .switch beforeSwitch (yulSwitchStatement_success_sound
              nested statementParses expressionParses nestedReflects
                nestedSound expressionSound diagnosticFree primary)
          · have switchFalse : isKeyword input .switchKw = false :=
              Bool.eq_false_iff.mpr switchPresent
            simp only [switchFalse, Bool.false_eq_true, if_false] at result
            have beforeFunction :
                DeclarativeGrammar.YulStatementCorePrefixAbsent
                  input.declarativeRemainder .functionGuard :=
              .afterSwitch beforeSwitch
                (keywordAbsentAt_of_isKeyword_eq_false .switchKw switchFalse)
            by_cases functionPresent : isKeyword input .functionKw
            · simp only [functionPresent, if_true] at result
              have primary :=
                recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                  (yulFunctionStatement nested) yulExpressionStatement result
                    diagnosticFree
              exact .functionDef beforeFunction
                (yulFunctionStatement_success_sound nested statementParses
                  nestedReflects nestedSound diagnosticFree primary)
            · have functionFalse : isKeyword input .functionKw = false :=
                Bool.eq_false_iff.mpr functionPresent
              simp only [functionFalse, Bool.false_eq_true, if_false]
                at result
              have beforeReturn :
                  DeclarativeGrammar.YulStatementCorePrefixAbsent
                    input.declarativeRemainder .returnGuard :=
                .afterFunction beforeFunction
                  (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                    functionFalse)
              by_cases returnPresent : isKeyword input .returnKw
              · simp only [returnPresent, if_true] at result
                have primary :=
                  recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                    yulReturnBuiltin yulExpressionStatement result
                      diagnosticFree
                exact .returnBuiltin beforeReturn
                  (yulReturnBuiltin_success_sound expressionParses
                    expressionSound diagnosticFree primary)
              · have returnFalse : isKeyword input .returnKw = false :=
                  Bool.eq_false_iff.mpr returnPresent
                simp only [returnFalse, Bool.false_eq_true, if_false] at result
                have beforeLeave :
                    DeclarativeGrammar.YulStatementCorePrefixAbsent
                      input.declarativeRemainder .leaveGuard :=
                  .afterReturn beforeReturn
                    (keywordAbsentAt_of_isKeyword_eq_false .returnKw
                      returnFalse)
                by_cases leavePresent : isKeyword input .leaveKw
                · simp only [leavePresent, if_true] at result
                  have primary :=
                    recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                        result diagnosticFree
                  exact .leave beforeLeave
                    (yulControlToken_success_sound .leaveKw .leave primary)
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.YulStatementCorePrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterLeave beforeLeave
                      (keywordAbsentAt_of_isKeyword_eq_false .leaveKw
                        leaveFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    have primary :=
                      recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                        (yulControlToken .breakKw .break) yulExpressionStatement
                          result diagnosticFree
                    exact .break beforeBreak
                      (yulControlToken_success_sound .breakKw .break primary)
                  · have breakFalse : isKeyword input .breakKw = false :=
                      Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.YulStatementCorePrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      have primary :=
                        recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                          (yulControlToken .continueKw .continue)
                            yulExpressionStatement result diagnosticFree
                      exact .continue beforeContinue
                        (yulControlToken_success_sound .continueKw .continue
                          primary)
                    · have continueFalse :
                          isKeyword input .continueKw = false :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeName :
                          DeclarativeGrammar.YulStatementCorePrefixAbsent
                            input.declarativeRemainder .nameGuard :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      by_cases namePresent : startsYulName input
                      · simp only [namePresent, if_true] at result
                        have nameStart :=
                          yulNameStartAt_of_startsYulName_eq_true namePresent
                        unfold orElse at result
                        cases assignmentResult : yulAssignment input with
                        | invariant error => simp [assignmentResult] at result
                        | ok assignment afterAssignment =>
                            simp only [assignmentResult] at result
                            cases result
                            exact .nameChoice beforeName (.assignment nameStart
                              (yulAssignment_success_sound expressionParses
                                expressionSound diagnosticFree
                                  assignmentResult))
                        | reject failure rejected =>
                            simp only [assignmentResult] at result
                            exact .nameChoice beforeName (.rewound nameStart
                              (assignmentRejectionSound assignmentResult)
                              (yulExpressionStatement_success_sound
                                expressionParses expressionSound diagnosticFree
                                  result))
                      · have nameFalse : startsYulName input = false :=
                          Bool.eq_false_iff.mpr namePresent
                        simp only [nameFalse, Bool.false_eq_true, if_false]
                          at result
                        have beforeFallback :
                            DeclarativeGrammar.YulStatementCorePrefixAbsent
                              input.declarativeRemainder .fallback :=
                          .afterName beforeName
                            (yulNameStartAbsentAt_of_startsYulName_eq_false
                              nameFalse)
                        exact .expressionFallback beforeFallback
                          (yulExpressionStatement_success_sound expressionParses
                            expressionSound diagnosticFree result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementLayerSoundnessProperties
/-! Exact soundness for Yul semicolon and recovery statement layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Clean concrete terminated success is exact core plus optional semicolon. -/
theorem yulStatementTerminated_success_sound_of_core
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementTerminated nested input = .ok value next) :
    DeclarativeGrammar.YulStatementTerminatedLayerParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold yulStatementTerminated at result
  exact yulStatementTerminated_success_sound (yulStatementCore nested)
    (DeclarativeGrammar.YulStatementCoreParses statementParses
      expressionParses fallback)
    (fun outputFree coreResult => yulStatementCore_success_sound nested
      statementParses expressionParses fallback assignmentRejectionSound
        nestedReflects nestedSound expressionSound outputFree coreResult)
    diagnosticFree result

/-- A clean recovering-layer success is the unchanged terminated derivation. -/
theorem yulStatementLayer_success_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementLayer nested input = .ok value next) :
    DeclarativeGrammar.YulStatementLayerParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder :=
  yulStatementTerminated_success_sound_of_core nested statementParses
    expressionParses fallback assignmentRejectionSound nestedReflects
      nestedSound expressionSound diagnosticFree
        (yulStatementTerminated_of_diagnosticFree_layer_success nested result
          diagnosticFree)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulAssignmentPublicFallbackSoundnessProperties
/-!
Executable bridges for the concrete public inline-Yul assignment fallback.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assignment rejection supplies the concrete unary
fallback consumed by the public Yul statement dispatcher. -/
theorem yulAssignment_publicFallback_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulAssignment input = .reject failure rejected) :
    DeclarativeGrammar.yulAssignmentPublicFallbackSpec.rejects
      input.declarativeRemainder := by
  simpa only [DeclarativeGrammar.yulAssignmentPublicFallbackSpec] using
    yulAssignment_fallback_reject_sound
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionParses
      DeclarativeGrammar.YulExpressionRejects
      DeclarativeGrammar.yulExpressionPublicDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionParses.toOrdinary
      yulExpression_reject_sound result

/-- Every diagnostic-free executable assignment success follows the concrete
public recursive expression grammar. -/
theorem yulAssignment_success_public_sound
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulAssignment input = .ok statement output) :
    DeclarativeGrammar.YulAssignmentParses
      DeclarativeGrammar.YulExpressionParses input.declarativeRemainder
        statement output.declarativeRemainder :=
  yulAssignment_success_sound DeclarativeGrammar.YulExpressionParses
    yulExpression_success_clean_sound diagnosticFree result

/-- Specialize the clean core statement dispatcher to the complete public
expression grammar and its concrete transactional assignment fallback. -/
theorem yulStatementCore_success_publicExpression_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input output : State} {statement : YulStmt},
      output.diagnosticsRev = [] →
        nested input = .ok statement output →
        statementParses input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatementCore nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreParses statementParses
      DeclarativeGrammar.YulExpressionParses
      DeclarativeGrammar.yulAssignmentPublicFallbackSpec
      input.declarativeRemainder statement output.declarativeRemainder :=
  yulStatementCore_success_sound nested statementParses
    DeclarativeGrammar.YulExpressionParses
    DeclarativeGrammar.yulAssignmentPublicFallbackSpec
    yulAssignment_publicFallback_reject_sound nestedReflects nestedSound
    yulExpression_success_clean_sound diagnosticFree result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementFuelCleanSoundnessProperties
/-! Diagnostic-free reflection for recursive fuel-indexed Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free executable success at explicit fuel follows the
clean declarative relation at that same fuel. -/
theorem yulStatementWithFuel_success_clean_sound : ∀ fuel,
    ∀ {input output : State} {statement : YulStmt},
      output.diagnosticsRev = [] →
      yulStatementWithFuel fuel input = .ok statement output →
        DeclarativeGrammar.YulStatementCleanParsesWithFuel fuel
          input.declarativeRemainder statement output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input output statement diagnosticFree result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input output statement diagnosticFree result
      apply (DeclarativeGrammar.YulStatementCleanParsesWithFuel.succ_iff).2
      exact yulStatementLayer_success_sound
        (yulStatementWithFuel fuel)
        (DeclarativeGrammar.YulStatementCleanParsesWithFuel fuel)
        DeclarativeGrammar.YulExpressionParses
        DeclarativeGrammar.yulAssignmentPublicFallbackSpec
        yulAssignment_publicFallback_reject_sound
        (yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess fuel)
        inductionHypothesis yulExpression_success_clean_sound diagnosticFree
        result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementLayerOrdinarySoundnessProperties
/-! Ordinary-success reflection for one outer recovering Yul-statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reject_state_eq {α : Type} {leftFailure rightFailure : Failure}
    {leftState rightState : State}
    (result : (Reply.reject leftFailure leftState : Reply α) =
      .reject rightFailure rightState) : leftState = rightState := by
  injection result

/-- Every successful recovering statement layer is either an ordinary
terminated success or the exact rewind/first-token/recovery-scan outcome. -/
theorem yulStatementLayer_success_ordinary_sound
    (nested : Parser YulStmt)
    (terminatedOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (terminatedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (terminatedSuccessSound : ∀ {input output : State}
      {statement : YulStmt},
      yulStatementTerminated nested input = .ok statement output →
        terminatedOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (terminatedRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulStatementTerminated nested input = .reject failure rejected →
        terminatedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (terminatedShape :
      Parser.PreservesTokenWindow (yulStatementTerminated nested))
    {input output : State} {statement : YulStmt}
    (result : yulStatementLayer nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | ok parsed afterTerminated =>
      simp only [terminatedResult] at result
      cases result
      exact .terminated (terminatedSuccessSound terminatedResult)
  | invariant error => simp [terminatedResult] at result
  | reject failure failedState =>
      simp only [terminatedResult] at result
      have rejectedGrammar := terminatedRejectSound terminatedResult
      have shape := terminatedShape input
      rw [terminatedResult] at shape
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using shape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => .reject failure rewound) = .ok statement output at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .rightBrace) = true
      · simp only [boundary, if_true] at result
        contradiction
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, afterEq⟩
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulStatementRejects_of_nonBoundary_token
              boundaryFalse found
            have scan := recoverYulStatementAux_success_ordinary_sound
              token.span (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) statement output result
            rw [afterEq] at scan
            exact .recovered rejectedGrammar
              (by
                simpa [rewound, State.declarativeRemainder, failedShape.1,
                  failedShape.2] using continues)
              (by
                simpa [rewound, State.declarativeRemainder, failedShape.1,
                  failedShape.2] using current)
              (by
                simpa [rewound, State.declarativeRemainder, State.emit,
                  failedShape.1, failedShape.2] using scan)

/-- Every executable outer-layer rejection is the exact non-consuming Yul
statement recovery boundary. -/
theorem yulStatementLayer_reject_sound
    (nested : Parser YulStmt)
    (terminatedShape :
      Parser.PreservesTokenWindow (yulStatementTerminated nested))
    {input rejected : State} {failure : Failure}
    (result : yulStatementLayer nested input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | ok statement output => simp [terminatedResult] at result
  | invariant error => simp [terminatedResult] at result
  | reject primaryFailure failedState =>
      simp only [terminatedResult] at result
      have shape := terminatedShape input
      rw [terminatedResult] at shape
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using shape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject primaryFailure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit primaryFailure.toDiagnostic)
        | none => .reject primaryFailure rewound) =
          .reject failure rejected at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .rightBrace) = true
      · simp only [boundary, if_true] at result
        have stateEq := reject_state_eq result
        rw [← stateEq]
        simpa [rewound, State.declarativeRemainder, failedShape.1,
          failedShape.2] using
            yulStatementRejects_of_boundary rewound boundary
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : rewound.advance? with
        | none =>
            simp only [advanced] at result
            have stateEq := reject_state_eq result
            rw [← stateEq]
            simpa [rewound, State.declarativeRemainder, failedShape.1,
              failedShape.2] using
                yulStatementRejects_of_advance?_eq_none rewound advanced
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases recoverYulStatementAux_production_exists_ok token.span
                token.span (afterToken.emit primaryFailure.toDiagnostic) with
              ⟨statement, final, recovered⟩
            have sameRemaining :
                (afterToken.emit primaryFailure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [sameRemaining] at recovered
            rw [recovered] at result
            contradiction

end Solcore.Syntax.Parser
end
