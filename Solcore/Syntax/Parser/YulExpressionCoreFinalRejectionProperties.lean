import Solcore.Syntax.Parser.YulExpressionCoreOrdinarySoundnessProperties

/-! Exact reflection of the final `rejectAt` branch in the Yul core parser. -/

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
    | ok arguments next => rw [argumentsResult] at result; contradiction
    | reject innerFailure failed =>
        rw [argumentsResult] at result
        contradiction
    | invariant error => rw [argumentsResult] at result; contradiction
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
  · unfold State.peekKind? at found
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
                (optionalYulCallArguments_ne_reject nested argumentsResult)
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
