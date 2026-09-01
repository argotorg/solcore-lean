import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeProperties
import Solcore.Syntax.Parser.CoreLiteralOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternBasicSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Exact executable ordinary outcomes of the three `patternCore` leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem rejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

private theorem bind_pure_reject_first {alpha beta : Type}
    {first : Parser alpha} {finish : alpha → beta}
    {input rejected : State} {failure : Failure}
    (result : (first >>= fun value => pure (finish value)) input =
      .reject failure rejected) :
    first input = .reject failure rejected := by
  change (match first input with
    | .ok value afterFirst => (pure (finish value) : Parser beta) afterFirst
    | .reject firstFailure firstRejected =>
        .reject firstFailure firstRejected
    | .invariant error => .invariant error) = .reject failure rejected at result
  cases firstResult : first input with
  | ok value afterFirst => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction
  | reject firstFailure firstRejected =>
      rw [firstResult] at result
      cases result
      rfl

/-- Wildcard rejection is exact and non-consuming. -/
theorem wildcardPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : wildcardPattern input = .reject failure rejected) :
    DeclarativeGrammar.WildcardPatternRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold wildcardPattern at result
  have markerResult : symbol .underscore .pattern input =
      .reject failure rejected := bind_pure_reject_first result
  have rejectedEq := symbol_reject_state_eq .underscore .pattern markerResult
  subst rejected
  exact .absent
    (symbol_reject_tokenKindAbsentAt .underscore .pattern markerResult)

/-- A positive wildcard guard cannot reject. -/
theorem wildcardPattern_ne_reject_of_isSymbol_eq_true
    {input rejected : State} {failure : Failure}
    (present : isSymbol input .underscore = true)
    (result : wildcardPattern input = .reject failure rejected) : False := by
  unfold wildcardPattern at result
  have markerResult : symbol .underscore .pattern input =
      .reject failure rejected := bind_pure_reject_first result
  rcases symbol_eq_ok_of_isSymbol_eq_true .underscore .pattern present with
    ⟨token, parsed⟩
  rw [parsed] at markerResult
  contradiction

/-- Literal-pattern rejection is the exact literal primitive rejection. -/
theorem literalPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : literalPattern input = .reject failure rejected) :
    DeclarativeGrammar.LiteralPatternRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold literalPattern at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := coreLiteral_reject_state_eq literalResult
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt literalResult)

/-- A positive literal guard cannot reject. -/
theorem literalPattern_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (present : isCoreLiteral input = true)
    (result : literalPattern input = .reject failure rejected) : False := by
  unfold literalPattern at result
  exact coreLiteral_ne_reject_of_isCoreLiteral_eq_true present
    (bind_pure_reject_first result)

private theorem booleanIdentifier_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    rejected = input := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_rejected_state_eq result }
        all_goals try { contradiction }

private theorem booleanIdentifier_reject_booleanPatternAbsentAt
    {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.keyword .trueKw
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.keyword .trueKw
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold booleanIdentifier at result
    simp [found] at result
  · rintro ⟨span, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.keyword .falseKw
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.keyword .falseKw
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold booleanIdentifier at result
    simp [found] at result

/-- Boolean-binder rejection is exact and non-consuming. -/
theorem booleanBinderPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : booleanBinderPattern input = .reject failure rejected) :
    DeclarativeGrammar.BooleanBinderPatternRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold booleanBinderPattern at result
  have nameResult : booleanIdentifier input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := booleanIdentifier_reject_state_eq nameResult
  subst rejected
  exact .absent (booleanIdentifier_reject_booleanPatternAbsentAt nameResult)

/-- A positive Boolean guard cannot reject. -/
theorem booleanBinderPattern_ne_reject_of_isBooleanValue_eq_true
    {input rejected : State} {failure : Failure}
    (present : isBooleanValue input = true)
    (result : booleanBinderPattern input = .reject failure rejected) : False := by
  unfold booleanBinderPattern at result
  have nameResult : booleanIdentifier input = .reject failure rejected :=
    bind_pure_reject_first result
  unfold isBooleanValue isKeyword State.peekKind? at present
  unfold booleanIdentifier at nameResult
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present nameResult
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at present nameResult
        all_goals try { contradiction }

/-- Package executable wildcard success and exact rejection. -/
theorem wildcardPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      wildcardPattern input = .ok pattern output →
        DeclarativeGrammar.WildcardPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      wildcardPattern input = .reject failure rejected →
        DeclarativeGrammar.WildcardPatternRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨wildcardPattern_success_sound, wildcardPattern_reject_ordinary_sound⟩

/-- Package executable literal-pattern success and exact rejection. -/
theorem literalPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      literalPattern input = .ok pattern output →
        DeclarativeGrammar.LiteralPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      literalPattern input = .reject failure rejected →
        DeclarativeGrammar.LiteralPatternRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨literalPattern_success_sound, literalPattern_reject_ordinary_sound⟩

/-- Package executable Boolean-binder success and exact rejection. -/
theorem booleanBinderPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      booleanBinderPattern input = .ok pattern output →
        DeclarativeGrammar.BooleanBinderPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      booleanBinderPattern input = .reject failure rejected →
        DeclarativeGrammar.BooleanBinderPatternRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨booleanBinderPattern_success_sound,
    booleanBinderPattern_reject_ordinary_sound⟩

/-- Package all three leaf deterministic outcome specifications. -/
theorem patternCoreLeaf_ordinaryOutcomeSpec :
    (DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.WildcardPatternOrdinaryParses
      DeclarativeGrammar.WildcardPatternRejects) ∧
    (DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LiteralPatternOrdinaryParses
      DeclarativeGrammar.LiteralPatternRejects) ∧
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.BooleanBinderPatternOrdinaryParses
      DeclarativeGrammar.BooleanBinderPatternRejects :=
  ⟨DeclarativeGrammar.wildcardPatternDeterministicOutcomeSpec,
    DeclarativeGrammar.literalPatternDeterministicOutcomeSpec,
    DeclarativeGrammar.booleanBinderPatternDeterministicOutcomeSpec⟩

end Solcore.Syntax.Parser.PatternInternals
