import Solcore.Syntax.DeclarativeYulExpressionRejectionGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Yul.ExpressionFuelTotalityProperties

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
