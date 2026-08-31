import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.PatternValidity

/-! Provenance and carrier contracts for canonical pattern parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PatternInternals

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

private theorem patternBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Wildcard parsing retains both the outer and marker source ranges. -/
theorem wildcardPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    wildcardPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold wildcardPattern
  apply Parser.bind_validFor_of_value
    (symbol_validFor .underscore .pattern)
  intro marker input inputValid markerValid
  exact ⟨Pattern.ValidFor.wildcard markerValid markerValid,
    inputValid, rfl⟩

/-- Wildcard parsing preserves every ordinary token window. -/
theorem wildcardPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .underscore .pattern)
  intro marker
  exact Parser.pure_preservesTokenWindow _

theorem wildcardPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess wildcardPattern :=
  wildcardPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Wildcard parsing advances without rewinding the cursor. -/
theorem wildcardPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .underscore .pattern)
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A wildcard pattern starts at its underscore token. -/
theorem wildcardPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess wildcardPattern (·.span) := by
  unfold wildcardPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .underscore .pattern)
  intro marker input value final parsed
  cases parsed
  rfl

/-- Literal-pattern parsing retains both equal literal ranges. -/
theorem literalPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    literalPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold literalPattern
  apply Parser.bind_validFor_of_value coreLiteral_validFor
  intro literal input inputValid literalValid
  exact ⟨Pattern.ValidFor.literal literalValid literalValid,
    inputValid, rfl⟩

/-- Literal patterns preserve every ordinary token window. -/
theorem literalPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow literalPattern := by
  unfold literalPattern
  apply Parser.bind_preservesTokenWindow coreLiteral_preservesTokenWindow
  intro literal
  exact Parser.pure_preservesTokenWindow _

theorem literalPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess literalPattern :=
  literalPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Literal-pattern parsing never rewinds the cursor. -/
theorem literalPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess literalPattern := by
  unfold literalPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    coreLiteral_cursorMonotoneOnSuccess
  intro literal
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A literal pattern starts at its literal token. -/
theorem literalPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess literalPattern (·.span) := by
  unfold literalPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    coreLiteral_startsAtCurrentTokenOnSuccess
  intro literal input value final parsed
  cases parsed
  rfl

/-- Boolean binder patterns retain both equal builtin-name ranges. -/
theorem booleanBinderPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    booleanBinderPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold booleanBinderPattern
  apply Parser.bind_validFor_of_value booleanIdentifier_validFor
  intro name input inputValid nameValid
  exact ⟨Pattern.ValidFor.binder nameValid nameValid, inputValid, rfl⟩

/-- Boolean binder patterns preserve every ordinary token window. -/
theorem booleanBinderPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_preservesTokenWindow
    booleanIdentifier_preservesTokenWindow
  intro name
  exact Parser.pure_preservesTokenWindow _

theorem booleanBinderPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess booleanBinderPattern :=
  booleanBinderPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Boolean binder parsing never rewinds the cursor. -/
theorem booleanBinderPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    booleanIdentifier_cursorMonotoneOnSuccess
  intro name
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A Boolean binder pattern starts at its keyword token. -/
theorem booleanBinderPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess booleanBinderPattern (·.span) := by
  unfold booleanBinderPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    booleanIdentifier_startsAtCurrentTokenOnSuccess
  intro name input value final parsed
  cases parsed
  rfl

/-- Pattern names preserve their ordinary or Boolean builtin range. -/
theorem patternName_validFor :
    patternName.ValidFor Located.ValidFor := by
  intro input inputValid
  unfold patternName
  split
  · exact booleanIdentifier_validFor input inputValid
  · exact identifier_validFor .pattern input inputValid

/-- Pattern-name parsing preserves every ordinary token window. -/
theorem patternName_preservesTokenWindow :
    Parser.PreservesTokenWindow patternName := by
  intro input
  unfold patternName
  split
  · exact booleanIdentifier_preservesTokenWindow input
  · exact identifier_preservesTokenWindow .pattern input

theorem patternName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess patternName :=
  patternName_preservesTokenWindow.preservesTokensOnSuccess

theorem patternName_ok_state_shape {input next : State}
    {name : Identifier} (parsed : patternName input = .ok name next) :
    ∃ token, input.peek? = some token ∧ token.span = name.span ∧
      next.tokens = input.tokens ∧ next.cursor = input.cursor + 1 := by
  unfold patternName at parsed
  split at parsed
  · unfold booleanIdentifier at parsed
    cases found : input.peek? with
    | none => simp [found, rejectAt] at parsed
    | some token =>
        rcases token with ⟨span, kind⟩
        cases kind <;> simp only [found] at parsed
        all_goals try { unfold rejectAt at parsed; contradiction }
        case keyword keyword =>
          cases keyword <;> simp only at parsed
          all_goals try { unfold rejectAt at parsed; contradiction }
          all_goals cases parsed
          all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact identifier_ok_state_shape .pattern parsed

/-- Successful pattern-name parsing never rewinds the cursor. -/
theorem patternName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess patternName := by
  intro input name next parsed
  unfold patternName at parsed
  split at parsed
  · exact booleanIdentifier_cursorMonotoneOnSuccess
      input name next parsed
  · exact identifier_cursorMonotoneOnSuccess .pattern
      input name next parsed

theorem patternName_cursor_lt_onSuccess {input next : State}
    {name : Identifier} (parsed : patternName input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(patternName_ok_state_shape parsed).choose_spec.2.2.2]
  simp

/-- A pattern name starts at the ordinary or Boolean name token. -/
theorem patternName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess patternName (·.span) := by
  intro input name next parsed
  unfold patternName at parsed
  split at parsed
  · exact booleanIdentifier_startsAtCurrentTokenOnSuccess
      input name next parsed
  · rcases identifier_ok_state_shape .pattern parsed with
      ⟨token, found, span, _tokens, _cursor⟩
    exact ⟨token, found, congrArg SourceSpan.startByte span⟩

theorem requirePatternArguments_validFor
    (expressionValid : SourceFile → Expr → Prop)
    (values : DelimitedList Pattern) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : DelimitedList.ValidFor
      (Pattern.ValidFor expressionValid) input.file values) :
    (requirePatternArguments values input).ValidFor input
      (NonemptyDelimitedList.ValidFor
        (Pattern.ValidFor expressionValid)) := by
  unfold requirePatternArguments
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [pure, Reply.ValidFor,
        NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, trivial⟩
      intro pattern member
      exact valuesValid.2 pattern (by
        simpa [NonemptyList.toList, elements] using member)

private theorem requirePatternArguments_preservesTokenWindow
    (values : DelimitedList Pattern) :
    Parser.PreservesTokenWindow (requirePatternArguments values) := by
  intro input
  unfold requirePatternArguments
  cases values.elements <;> trivial

private theorem requirePatternArguments_cursorMonotoneOnSuccess
    (values : DelimitedList Pattern) :
    Parser.CursorMonotoneOnSuccess (requirePatternArguments values) := by
  intro input arguments next parsed
  unfold requirePatternArguments at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- Constructor arguments preserve delimiters and nested pattern ranges. -/
theorem constructorArguments_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (constructorArguments nested).ValidFor
      (NonemptyDelimitedList.ValidFor
        (Pattern.ValidFor expressionValid)) := by
  unfold constructorArguments
  apply Parser.bind_validFor_of_value
    (delimitedNoTrailing_validFor (Pattern.ValidFor expressionValid)
      .leftParen .rightParen false nested .pattern .pattern
      nestedValid nestedPreserves)
  intro values input inputValid valuesValid
  exact requirePatternArguments_validFor expressionValid values
    input inputValid valuesValid

/-- Constructor arguments preserve every ordinary token window. -/
theorem constructorArguments_preservesTokenWindow (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (constructorArguments nested) := by
  unfold constructorArguments
  apply Parser.bind_preservesTokenWindow
    (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen false
      false nested .pattern .pattern nestedPreserves)
  intro values
  exact requirePatternArguments_preservesTokenWindow values

theorem constructorArguments_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (constructorArguments nested) :=
  (constructorArguments_preservesTokenWindow nested
    nestedPreserves).preservesTokensOnSuccess

/-- Successful constructor arguments never rewind the cursor. -/
theorem constructorArguments_cursorMonotoneOnSuccess
    (nested : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess (constructorArguments nested) := by
  unfold constructorArguments
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen .rightParen
      false nested .pattern .pattern)
  intro values
  exact requirePatternArguments_cursorMonotoneOnSuccess values

/-- Constructor arguments start at their opening parenthesis. -/
theorem constructorArguments_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (constructorArguments nested) (·.span) := by
  unfold constructorArguments
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimitedNoTrailing_startsAtCurrentTokenOnSuccess .leftParen
      .rightParen false nested .pattern .pattern)
  intro values input arguments final parsed
  unfold requirePatternArguments at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      rfl

/-- Optional constructor arguments preserve present nested pattern ranges. -/
theorem optionalConstructorArguments_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (optionalConstructorArguments nested).ValidFor
      (Option.ValidFor (NonemptyDelimitedList.ValidFor
        (Pattern.ValidFor expressionValid))) := by
  intro input inputValid
  unfold optionalConstructorArguments
  split
  · apply Parser.orElse_validFor
      (second := pure none)
    · apply Parser.bind_validFor_of_value
        (constructorArguments_validFor nested expressionValid
          nestedValid nestedPreserves)
      intro values state stateValid valuesValid
      exact ⟨by simpa only [Option.ValidFor] using valuesValid,
        stateValid, rfl⟩
    · exact Parser.pure_validFor none _ (fun _ => trivial)
    · exact inputValid
  · exact ⟨trivial, inputValid, rfl⟩

/-- Optional constructor arguments preserve every ordinary token window. -/
theorem optionalConstructorArguments_preservesTokenWindow
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow
      (optionalConstructorArguments nested) := by
  intro input
  unfold optionalConstructorArguments
  split
  · apply Parser.orElse_preservesTokenWindow
    · apply Parser.bind_preservesTokenWindow
        (constructorArguments_preservesTokenWindow nested nestedPreserves)
      intro values
      exact Parser.pure_preservesTokenWindow _
    · exact Parser.pure_preservesTokenWindow none
  · exact ⟨rfl, rfl⟩

theorem optionalConstructorArguments_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess
      (optionalConstructorArguments nested) :=
  (optionalConstructorArguments_preservesTokenWindow
    nested nestedPreserves).preservesTokensOnSuccess

theorem optionalConstructorArguments_some_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) {input next : State}
    {values : NonemptyDelimitedList Pattern}
    (parsed : optionalConstructorArguments nested input =
      .ok (some values) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = values.span.startByte := by
  unfold optionalConstructorArguments at parsed
  split at parsed
  · unfold orElse at parsed
    cases firstResult : (do
        pure (some (← constructorArguments nested))) input with
    | ok result afterFirst =>
        simp only [firstResult] at parsed
        cases parsed
        rcases patternBind_ok_components firstResult with
          ⟨arguments, afterArguments, argumentsResult, finished⟩
        have starts := constructorArguments_startsAtCurrentTokenOnSuccess
          nested input arguments afterArguments argumentsResult
        cases finished
        exact starts
    | reject failure rejected =>
        rw [firstResult] at parsed
        simp [pure] at parsed
    | invariant error =>
        rw [firstResult] at parsed
        simp at parsed
  · simp at parsed

/-- Optional constructor arguments never rewind the cursor. -/
theorem optionalConstructorArguments_cursorMonotoneOnSuccess
    (nested : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess
      (optionalConstructorArguments nested) := by
  intro input values next parsed
  unfold optionalConstructorArguments at parsed
  split at parsed
  · exact Parser.orElse_cursorMonotoneOnSuccess
      (Parser.bind_cursorMonotoneOnSuccess
        (constructorArguments_cursorMonotoneOnSuccess nested)
        (fun _ => Parser.pure_cursorMonotoneOnSuccess _))
      (Parser.pure_cursorMonotoneOnSuccess none)
      input values next parsed
  · cases parsed
    exact Nat.le_refl _

/-- Closing a tuple retains its opening token and accumulated patterns. -/
theorem closePatternTuple_validFor
    (expressionValid : SourceFile → Expr → Prop)
    (opening : Token) (elementsRev : List Pattern) {input : State}
    {openingIndex : Nat} (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (elementsValid : List.ValidFor (Pattern.ValidFor expressionValid)
      input.file elementsRev) :
    (closePatternTuple opening elementsRev input).ValidFor input
      (Pattern.ValidFor expressionValid) := by
  unfold closePatternTuple
  simp only [bind]
  cases closingResult : symbol .rightParen .pattern input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .rightParen .pattern input inputValid
      rw [closingResult] at valid
      exact valid
  | ok closing afterClosing =>
      have closingValid := symbol_validFor .rightParen .pattern
        input inputValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape .rightParen .pattern
        closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingValid.1
      have openingBeforeClosing :=
        inputValid.token_end_le_token_start_of_getElem?_lt openingFound
          closingFound openingBefore
      have outerValid := SourceSpan.cover_validFor openingValid
        closingSpanValid (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1))
      cases elementsRev with
      | nil =>
          exact ⟨Pattern.ValidFor.tuple outerValid outerValid
            (by simp), closingValid.2.1, closingValid.2.2⟩
      | cons only tail =>
          cases tail with
          | nil =>
              exact ⟨Pattern.ValidFor.group outerValid
                (elementsValid only (by simp)), closingValid.2.1,
                closingValid.2.2⟩
          | cons second rest =>
              exact ⟨Pattern.ValidFor.tuple outerValid outerValid
                (by
                  intro element member
                  exact elementsValid element (by
                    simpa only [List.mem_reverse] using member)),
                closingValid.2.1, closingValid.2.2⟩

/-- Closing a pattern tuple preserves every ordinary token window. -/
theorem closePatternTuple_preservesTokenWindow (opening : Token)
    (elementsRev : List Pattern) :
    Parser.PreservesTokenWindow
      (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .pattern)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_preservesTokenWindow _
  | cons only tail =>
      cases tail <;> exact Parser.pure_preservesTokenWindow _

theorem closePatternTuple_preservesTokensOnSuccess (opening : Token)
    (elementsRev : List Pattern) :
    Parser.PreservesTokensOnSuccess
      (closePatternTuple opening elementsRev) :=
  (closePatternTuple_preservesTokenWindow opening elementsRev).preservesTokensOnSuccess

/-- Closing a pattern tuple never rewinds the cursor. -/
theorem closePatternTuple_cursorMonotoneOnSuccess (opening : Token)
    (elementsRev : List Pattern) :
    Parser.CursorMonotoneOnSuccess
      (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .pattern)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_cursorMonotoneOnSuccess _
  | cons only tail =>
      cases tail <;> exact Parser.pure_cursorMonotoneOnSuccess _

/-- Closing retains the opening parenthesis as the result start. -/
theorem closePatternTuple_preservesOpeningStartOnSuccess
    (opening : Token) (elementsRev : List Pattern)
    {input final : State} {pattern : Pattern}
    (parsed : closePatternTuple opening elementsRev input =
      .ok pattern final) :
    pattern.span.startByte = opening.span.startByte := by
  unfold closePatternTuple at parsed
  rcases patternBind_ok_components parsed with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases elementsRev with
  | nil => cases finished; rfl
  | cons only tail =>
      cases tail with
      | nil => cases finished; rfl
      | cons second rest => cases finished; rfl

/-- The result ends at the current closing-parenthesis token. -/
theorem closePatternTuple_endsAtCurrentTokenOnSuccess
    (opening : Token) (elementsRev : List Pattern)
    {input final : State} {pattern : Pattern}
    (parsed : closePatternTuple opening elementsRev input =
      .ok pattern final) :
    ∃ closing, input.peek? = some closing ∧
      closing.span.endByte = pattern.span.endByte := by
  unfold closePatternTuple at parsed
  rcases patternBind_ok_components parsed with
    ⟨closing, afterClosing, closingResult, finished⟩
  have found :=
    (symbol_ok_state_shape .rightParen .pattern closingResult).1
  cases elementsRev with
  | nil => cases finished; exact ⟨closing, found, rfl⟩
  | cons only tail =>
      cases tail with
      | nil => cases finished; exact ⟨closing, found, rfl⟩
      | cons second rest =>
          cases finished
          exact ⟨closing, found, rfl⟩

/-- The tuple-tail loop retains its opening and accumulated pattern ranges. -/
theorem patternTupleTail_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev input openingIndex,
    input.ValidFor →
    input.tokens[openingIndex]? = some opening →
    openingIndex < input.cursor →
    List.ValidFor (Pattern.ValidFor expressionValid) input.file elementsRev →
    (patternTupleTail nested opening fuel elementsRev input).ValidFor input
      (Pattern.ValidFor expressionValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev input openingIndex inputValid openingFound
        openingBefore elementsValid
      unfold patternTupleTail
      cases commaResult : symbol .comma .pattern input with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := symbol_validFor .comma .pattern input inputValid
          rw [commaResult] at valid
          exact valid
      | ok comma afterComma =>
          have commaValid := symbol_validFor .comma .pattern input inputValid
          rw [commaResult] at commaValid
          have commaShape := symbol_ok_state_shape .comma .pattern commaResult
          have openingFoundAfter :
              afterComma.tokens[openingIndex]? = some opening := by
            simpa [commaShape.2] using openingFound
          have openingBeforeAfter : openingIndex < afterComma.cursor := by
            simpa [commaShape.2] using Nat.lt_succ_of_lt openingBefore
          have elementsValidAfter : List.ValidFor
              (Pattern.ValidFor expressionValid) afterComma.file
              elementsRev := by
            simpa [commaValid.2.2] using elementsValid
          simp only
          split
          · exact (closePatternTuple_validFor expressionValid opening
                elementsRev commaValid.2.1 openingFoundAfter
                openingBeforeAfter elementsValidAfter).of_file_eq
                  commaValid.2.2
          · cases nestedResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                have valid := nestedValid afterComma commaValid.2.1
                rw [nestedResult] at valid
                exact valid.of_file_eq commaValid.2.2
            | ok value next =>
                have valueValid := nestedValid afterComma commaValid.2.1
                rw [nestedResult] at valueValid
                simp only
                split
                · trivial
                · have tokensEq := nestedPreserves afterComma value next
                      nestedResult
                  have openingFoundNext :
                      next.tokens[openingIndex]? = some opening := by
                    simpa [tokensEq] using openingFoundAfter
                  have openingBeforeNext : openingIndex < next.cursor :=
                    Nat.lt_trans openingBeforeAfter (by omega)
                  have accumulatedValid : List.ValidFor
                      (Pattern.ValidFor expressionValid) next.file
                      (value :: elementsRev) := by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | member
                    · simpa [valueValid.2.2] using valueValid.1
                    · simpa [valueValid.2.2] using
                        elementsValidAfter retained member
                  split
                  · exact (inductionHypothesis (value :: elementsRev) next
                        openingIndex valueValid.2.1 openingFoundNext
                        openingBeforeNext accumulatedValid).of_file_eq
                          (valueValid.2.2.trans commaValid.2.2)
                  · exact (closePatternTuple_validFor expressionValid opening
                        (value :: elementsRev) valueValid.2.1
                        openingFoundNext openingBeforeNext
                        accumulatedValid).of_file_eq
                          (valueValid.2.2.trans commaValid.2.2)

/-- The tuple-tail loop preserves the nested parser's ordinary token window. -/
theorem patternTupleTail_preservesTokenWindow (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (opening : Token) : ∀ fuel elementsRev,
    Parser.PreservesTokenWindow
      (patternTupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev input
      unfold patternTupleTail
      have commaShape := symbol_preservesTokenWindow .comma .pattern input
      cases commaResult : symbol .comma .pattern input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [commaResult] at commaShape
          exact commaShape
      | ok comma afterComma =>
          rw [commaResult] at commaShape
          simp only
          split
          · exact (closePatternTuple_preservesTokenWindow opening
                elementsRev afterComma).trans commaShape
          · have nestedShape := nestedPreserves afterComma
            cases nestedResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                rw [nestedResult] at nestedShape
                exact nestedShape.trans commaShape
            | ok value next =>
                rw [nestedResult] at nestedShape
                simp only
                split
                · trivial
                · split
                  · exact (inductionHypothesis (value :: elementsRev)
                        next).trans (nestedShape.trans commaShape)
                  · exact (closePatternTuple_preservesTokenWindow opening
                        (value :: elementsRev) next).trans
                          (nestedShape.trans commaShape)

theorem patternTupleTail_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (opening : Token) (fuel : Nat) (elementsRev : List Pattern) :
    Parser.PreservesTokensOnSuccess
      (patternTupleTail nested opening fuel elementsRev) :=
  (patternTupleTail_preservesTokenWindow nested nestedPreserves opening
    fuel elementsRev).preservesTokensOnSuccess

/-- The tuple-tail loop never rewinds the parser cursor. -/
theorem patternTupleTail_cursorMonotoneOnSuccess
    (nested : Parser Pattern)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
    Parser.CursorMonotoneOnSuccess
      (patternTupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input pattern final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input pattern final parsed
      unfold patternTupleTail at parsed
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at parsed
      | reject failure rejected => simp [commaResult] at parsed
      | ok comma afterComma =>
          simp only [commaResult] at parsed
          have commaMonotone := symbol_cursorMonotoneOnSuccess .comma
            .pattern input comma afterComma commaResult
          split at parsed
          · exact Nat.le_trans commaMonotone
              (closePatternTuple_cursorMonotoneOnSuccess opening elementsRev
                afterComma pattern final parsed)
          · cases nestedResult : nested afterComma with
            | invariant error => simp [nestedResult] at parsed
            | reject failure rejected => simp [nestedResult] at parsed
            | ok value next =>
                simp only [nestedResult] at parsed
                have valueMonotone := nestedMonotone afterComma value next
                  nestedResult
                split at parsed
                · contradiction
                · split at parsed
                  · exact Nat.le_trans commaMonotone
                      (Nat.le_trans valueMonotone
                        (inductionHypothesis (value :: elementsRev)
                          next pattern final parsed))
                  · exact Nat.le_trans commaMonotone
                      (Nat.le_trans valueMonotone
                        (closePatternTuple_cursorMonotoneOnSuccess opening
                          (value :: elementsRev) next pattern final parsed))

/-- Every successful tuple-tail result keeps its opening-parenthesis start. -/
theorem patternTupleTail_preservesOpeningStartOnSuccess
    (nested : Parser Pattern) (opening : Token) :
    ∀ fuel elementsRev input pattern final,
      patternTupleTail nested opening fuel elementsRev input =
        .ok pattern final →
      pattern.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input pattern final parsed
      unfold patternTupleTail at parsed
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at parsed
      | reject failure rejected => simp [commaResult] at parsed
      | ok comma afterComma =>
          simp only [commaResult] at parsed
          split at parsed
          · exact closePatternTuple_preservesOpeningStartOnSuccess opening
              elementsRev parsed
          · cases nestedResult : nested afterComma with
            | invariant error => simp [nestedResult] at parsed
            | reject failure rejected => simp [nestedResult] at parsed
            | ok value next =>
                simp only [nestedResult] at parsed
                split at parsed
                · contradiction
                · split at parsed
                  · exact inductionHypothesis (value :: elementsRev)
                      next pattern final parsed
                  · exact closePatternTuple_preservesOpeningStartOnSuccess
                      opening (value :: elementsRev) parsed

/-- Parenthesized patterns retain delimiters and every nested pattern range. -/
theorem parenthesizedPattern_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parenthesizedPattern nested).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold parenthesizedPattern
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftParen .pattern input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen .pattern input inputValid
      rw [openingResult] at openingValid
      have openingShape := symbol_ok_state_shape .leftParen .pattern
        openingResult
      have openingFound :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingFoundAfter :
          afterOpening.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingFound
      have openingBeforeAfter : input.cursor < afterOpening.cursor := by
        rw [openingShape.2]
        simp
      simp only
      split
      · exact (closePatternTuple_validFor expressionValid opening []
            openingValid.2.1 openingFoundAfter openingBeforeAfter
            (by simp [List.ValidFor])).of_file_eq openingValid.2.2
      · cases nestedResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := nestedValid afterOpening openingValid.2.1
            rw [nestedResult] at valid
            exact valid.of_file_eq openingValid.2.2
        | ok first next =>
            have firstValid := nestedValid afterOpening openingValid.2.1
            rw [nestedResult] at firstValid
            simp only
            split
            · trivial
            · have tokensEq := nestedPreserves afterOpening first next
                  nestedResult
              have openingFoundNext :
                  next.tokens[input.cursor]? = some opening := by
                simpa [tokensEq] using openingFoundAfter
              have openingBeforeNext : input.cursor < next.cursor :=
                Nat.lt_trans openingBeforeAfter (by omega)
              have accumulatedValid : List.ValidFor
                  (Pattern.ValidFor expressionValid) next.file [first] := by
                intro retained member
                simp only [List.mem_singleton] at member
                subst retained
                simpa [firstValid.2.2] using firstValid.1
              split
              · exact (patternTupleTail_validFor nested expressionValid
                    nestedValid nestedPreserves opening
                    (next.remainingCount + 1) [first] next input.cursor
                    firstValid.2.1 openingFoundNext openingBeforeNext
                    accumulatedValid).of_file_eq
                      (firstValid.2.2.trans openingValid.2.2)
              · exact (closePatternTuple_validFor expressionValid opening
                    [first] firstValid.2.1 openingFoundNext
                    openingBeforeNext accumulatedValid).of_file_eq
                      (firstValid.2.2.trans openingValid.2.2)

/-- Parenthesized parsing preserves every ordinary token window. -/
theorem parenthesizedPattern_preservesTokenWindow
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parenthesizedPattern nested) := by
  intro input
  unfold parenthesizedPattern
  have openingShape := symbol_preservesTokenWindow .leftParen .pattern input
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      simp only
      split
      · exact (closePatternTuple_preservesTokenWindow opening []
            afterOpening).trans openingShape
      · have nestedShape := nestedPreserves afterOpening
        cases nestedResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            rw [nestedResult] at nestedShape
            exact nestedShape.trans openingShape
        | ok first next =>
            rw [nestedResult] at nestedShape
            simp only
            split
            · trivial
            · split
              · exact (patternTupleTail_preservesTokenWindow nested
                    nestedPreserves opening (next.remainingCount + 1)
                    [first] next).trans (nestedShape.trans openingShape)
              · exact (closePatternTuple_preservesTokenWindow opening
                    [first] next).trans (nestedShape.trans openingShape)

theorem parenthesizedPattern_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (parenthesizedPattern nested) :=
  (parenthesizedPattern_preservesTokenWindow nested
    nestedPreserves).preservesTokensOnSuccess

/-- Parenthesized parsing never rewinds the parser cursor. -/
theorem parenthesizedPattern_cursorMonotoneOnSuccess
    (nested : Parser Pattern)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parenthesizedPattern nested) := by
  intro input pattern final parsed
  unfold parenthesizedPattern at parsed
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingMonotone := symbol_cursorMonotoneOnSuccess .leftParen
        .pattern input opening afterOpening openingResult
      split at parsed
      · exact Nat.le_trans openingMonotone
          (closePatternTuple_cursorMonotoneOnSuccess opening []
            afterOpening pattern final parsed)
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first next =>
            simp only [nestedResult] at parsed
            have firstMonotone := nestedMonotone afterOpening first next
              nestedResult
            split at parsed
            · contradiction
            · split at parsed
              · exact Nat.le_trans openingMonotone
                  (Nat.le_trans firstMonotone
                    (patternTupleTail_cursorMonotoneOnSuccess nested
                      nestedMonotone opening (next.remainingCount + 1)
                      [first] next pattern final parsed))
              · exact Nat.le_trans openingMonotone
                  (Nat.le_trans firstMonotone
                    (closePatternTuple_cursorMonotoneOnSuccess opening
                      [first] next pattern final parsed))

/-- A parenthesized pattern starts at its opening parenthesis. -/
theorem parenthesizedPattern_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parenthesizedPattern nested) (fun pattern => pattern.span) := by
  intro input pattern final parsed
  unfold parenthesizedPattern at parsed
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have found :=
        (symbol_ok_state_shape .leftParen .pattern openingResult).1
      split at parsed
      · have start := closePatternTuple_preservesOpeningStartOnSuccess
            opening [] parsed
        exact ⟨opening, found, start.symm⟩
      · cases nestedResult : nested afterOpening with
        | invariant error => simp [nestedResult] at parsed
        | reject failure rejected => simp [nestedResult] at parsed
        | ok first next =>
            simp only [nestedResult] at parsed
            split at parsed
            · contradiction
            · split at parsed
              · have start :=
                    patternTupleTail_preservesOpeningStartOnSuccess nested
                      opening (next.remainingCount + 1) [first]
                      next pattern final parsed
                exact ⟨opening, found, start.symm⟩
              · have start :=
                    closePatternTuple_preservesOpeningStartOnSuccess opening
                      [first] parsed
                exact ⟨opening, found, start.symm⟩

private theorem dotConstructorPattern_weakValidFor
    (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (dotConstructorPattern nested).ValidFor (fun _ _ => True) := by
  have argumentsWeak : (optionalConstructorArguments nested).ValidFor
      (fun _ _ => True) :=
    (optionalConstructorArguments_validFor nested expressionValid
      nestedValid nestedPreserves).mono (fun _ _ _ => trivial)
  unfold dotConstructorPattern
  apply Parser.bind_validFor (symbol_validFor .dot .pattern)
  intro dot
  apply Parser.bind_validFor patternName_validFor
  intro name
  apply Parser.bind_validFor argumentsWeak
  intro arguments
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- Leading-dot constructors retain their marker, name, and nested ranges. -/
theorem dotConstructorPattern_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (dotConstructorPattern nested).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  have weak := dotConstructorPattern_weakValidFor nested expressionValid
    nestedValid nestedPreserves input inputValid
  cases parsed : dotConstructorPattern nested input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold dotConstructorPattern at stages
      rcases patternBind_ok_components stages with
        ⟨dot, afterDot, dotResult, rest⟩
      rcases patternBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases patternBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, finished⟩
      have dotReply := symbol_validFor .dot .pattern input inputValid
      rw [dotResult] at dotReply
      have nameReply := patternName_validFor afterDot dotReply.2.1
      rw [nameResult] at nameReply
      have argumentsReply := optionalConstructorArguments_validFor nested
        expressionValid nestedValid nestedPreserves afterName nameReply.2.1
      rw [argumentsResult] at argumentsReply
      have dotSpanValid : dot.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using dotReply.1
      have nameSpanValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, dotReply.2.2] using nameReply.1
      have argumentsValid : Option.ValidFor
          (NonemptyDelimitedList.ValidFor
            (Pattern.ValidFor expressionValid)) input.file arguments := by
        simpa [nameReply.2.2, dotReply.2.2] using argumentsReply.1
      have dotShape := symbol_ok_state_shape .dot .pattern dotResult
      rcases patternName_ok_state_shape nameResult with
        ⟨nameToken, nameFound, nameTokenSpan, nameTokens, nameCursor⟩
      have dotAdvanced : input.advance? = some (dot, afterDot) := by
        unfold State.advance?
        rw [dotShape.1, dotShape.2]
        rfl
      have dotBeforeName :=
        inputValid.consumed_end_le_peek_start_after_advance
          dotAdvanced nameFound
      have orderedName : dot.span.startByte ≤ name.span.endByte :=
        Nat.le_trans dotSpanValid.2.1 (Nat.le_trans
          (by simpa [nameTokenSpan] using dotBeforeName)
          nameSpanValid.2.1)
      cases arguments with
      | none =>
          cases finished
          refine ⟨Pattern.ValidFor.constructor
            (SourceSpan.cover_validFor dotSpanValid nameSpanValid orderedName)
            ?_ ?_ nameSpanValid ?_ ?_, weak.2.1, weak.2.2⟩
          · intro marker member
            simp at member
            subst marker
            exact dotSpanValid
          · simp
          · simp
          · simp
      | some values =>
          have valuesValid : NonemptyDelimitedList.ValidFor
              (Pattern.ValidFor expressionValid) input.file values := by
            simpa only [Option.ValidFor] using argumentsValid
          rcases optionalConstructorArguments_some_startsAtCurrentTokenOnSuccess
              nested argumentsResult with ⟨opening, openingFound, valuesStart⟩
          have nameAtAfterName :
              afterName.tokens[afterDot.cursor]? = some nameToken := by
            rw [nameTokens]
            exact State.getElem?_eq_some_of_peek?_eq_some nameFound
          have openingAt :=
            State.getElem?_eq_some_of_peek?_eq_some openingFound
          have nameBeforeValues :=
            nameReply.2.1.token_end_le_token_start_of_getElem?_lt
              nameAtAfterName openingAt (by rw [nameCursor]; simp)
          have orderedValues : dot.span.startByte ≤ values.span.endByte :=
            Nat.le_trans orderedName (Nat.le_trans
              (by simpa [nameTokenSpan, valuesStart] using nameBeforeValues)
              valuesValid.1.2.1)
          cases finished
          refine ⟨Pattern.ValidFor.constructor
            (SourceSpan.cover_validFor dotSpanValid valuesValid.1
              orderedValues) ?_ ?_ nameSpanValid ?_ ?_,
            weak.2.1, weak.2.2⟩
          · intro marker member
            simp at member
            subst marker
            exact dotSpanValid
          · simp
          · intro retained member
            simp at member
            subst retained
            exact valuesValid.1
          · intro retained retainedMember pattern patternMember
            simp at retainedMember
            subst retained
            exact valuesValid.2 pattern patternMember

/-- Leading-dot constructors preserve every ordinary token window. -/
theorem dotConstructorPattern_preservesTokenWindow (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (dotConstructorPattern nested) := by
  unfold dotConstructorPattern
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .dot .pattern)
  intro dot
  apply Parser.bind_preservesTokenWindow patternName_preservesTokenWindow
  intro name
  apply Parser.bind_preservesTokenWindow
    (optionalConstructorArguments_preservesTokenWindow nested nestedPreserves)
  intro arguments
  exact Parser.pure_preservesTokenWindow _

theorem dotConstructorPattern_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (dotConstructorPattern nested) :=
  (dotConstructorPattern_preservesTokenWindow
    nested nestedPreserves).preservesTokensOnSuccess

/-- Leading-dot constructors never rewind the cursor. -/
theorem dotConstructorPattern_cursorMonotoneOnSuccess
    (nested : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess (dotConstructorPattern nested) := by
  unfold dotConstructorPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .dot .pattern)
  intro dot
  apply Parser.bind_cursorMonotoneOnSuccess
    patternName_cursorMonotoneOnSuccess
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalConstructorArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A leading-dot constructor starts at its dot token. -/
theorem dotConstructorPattern_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (dotConstructorPattern nested) (·.span) := by
  unfold dotConstructorPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .dot .pattern)
  intro dot input value final parsed
  rcases patternBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases patternBind_ok_components rest with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  cases finished
  rfl

private theorem qualifiedPattern_weakValidFor
    (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (qualifiedPattern nested).ValidFor (fun _ _ => True) := by
  have argumentsWeak : (optionalConstructorArguments nested).ValidFor
      (fun _ _ => True) :=
    (optionalConstructorArguments_validFor nested expressionValid
      nestedValid nestedPreserves).mono (fun _ _ _ => trivial)
  unfold qualifiedPattern
  apply Parser.bind_validFor
    (qualifiedName_validFor .pattern .pattern)
  intro path
  apply Parser.bind_validFor argumentsWeak
  intro arguments
  let components := path.value.components.toList
  cases reversed : components.reverse with
  | nil =>
      simp only [components, reversed]
      intro input inputValid
      trivial
  | cons name qualifiersRev =>
      simp only [components, reversed]
      split
      · exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
      · exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- Qualified patterns retain binder or constructor component provenance. -/
theorem qualifiedPattern_validFor (nested : Parser Pattern)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (qualifiedPattern nested).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  have weak := qualifiedPattern_weakValidFor nested expressionValid
    nestedValid nestedPreserves input inputValid
  cases parsed : qualifiedPattern nested input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold qualifiedPattern at stages
      rcases patternBind_ok_components stages with
        ⟨path, afterPath, pathResult, rest⟩
      rcases patternBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, finished⟩
      have pathReply := qualifiedName_validFor .pattern .pattern
        input inputValid
      rw [pathResult] at pathReply
      have argumentsReply := optionalConstructorArguments_validFor nested
        expressionValid nestedValid nestedPreserves afterPath pathReply.2.1
      rw [argumentsResult] at argumentsReply
      have pathValid : QualifiedName.ValidFor input.file path := pathReply.1
      have argumentsValid : Option.ValidFor
          (NonemptyDelimitedList.ValidFor
            (Pattern.ValidFor expressionValid)) input.file arguments := by
        simpa [pathReply.2.2] using argumentsReply.1
      let components := path.value.components.toList
      cases reversed : components.reverse with
      | nil =>
          simp [components, reversed] at finished
      | cons name qualifiersRev =>
          have nameMember : name ∈ components := by
            have : name ∈ components.reverse := by rw [reversed]; simp
            simpa using this
          have nameValid : name.span.ValidFor input.file :=
            pathValid.2 name (by simpa [components] using nameMember)
          have qualifiersValid : ∀ qualifier ∈ qualifiersRev.reverse,
              qualifier.span.ValidFor input.file := by
            intro qualifier member
            have tailMember : qualifier ∈ qualifiersRev := by
              simpa using member
            have reverseMember : qualifier ∈ components.reverse := by
              rw [reversed]
              exact List.mem_cons_of_mem name tailMember
            exact pathValid.2 qualifier (by
              simpa [components] using reverseMember)
          simp only [components, reversed] at finished
          split at finished
          · cases finished
            exact ⟨Pattern.ValidFor.binder pathValid.1 nameValid,
              weak.2.1, weak.2.2⟩
          · cases arguments with
            | none =>
                cases finished
                refine ⟨Pattern.ValidFor.constructor
                  (SourceSpan.cover_validFor pathValid.1 pathValid.1
                    pathValid.1.2.1) ?_ qualifiersValid nameValid ?_ ?_,
                  weak.2.1, weak.2.2⟩
                · simp
                · simp
                · simp
            | some values =>
                have valuesValid : NonemptyDelimitedList.ValidFor
                    (Pattern.ValidFor expressionValid) input.file values := by
                  simpa only [Option.ValidFor] using argumentsValid
                rcases qualifiedName_startsAtCurrentTokenOnSuccess .pattern
                    .pattern input path afterPath pathResult with
                  ⟨first, firstFound, pathStart⟩
                rcases optionalConstructorArguments_some_startsAtCurrentTokenOnSuccess
                    nested argumentsResult with
                  ⟨opening, openingFound, argumentsStart⟩
                have firstAtAfter :
                    afterPath.tokens[input.cursor]? = some first := by
                  rw [qualifiedName_preservesTokensOnSuccess .pattern .pattern
                    input path afterPath pathResult]
                  exact State.getElem?_eq_some_of_peek?_eq_some firstFound
                have openingAt :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have firstBeforeArguments :=
                  pathReply.2.1.token_end_le_token_start_of_getElem?_lt
                    firstAtAfter openingAt
                    (qualifiedName_cursor_lt_onSuccess .pattern .pattern
                      pathResult)
                have firstValid :=
                  pathReply.2.1.token_span_validFor_of_getElem?_eq_some
                    firstAtAfter
                have ordered : path.span.startByte ≤ values.span.endByte := by
                  rw [← pathStart]
                  exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstBeforeArguments (by
                      rw [argumentsStart]
                      exact valuesValid.1.2.1))
                cases finished
                refine ⟨Pattern.ValidFor.constructor
                  (SourceSpan.cover_validFor pathValid.1 valuesValid.1 ordered)
                  ?_ qualifiersValid nameValid ?_ ?_, weak.2.1, weak.2.2⟩
                · simp
                · intro retained member
                  simp at member
                  subst retained
                  exact valuesValid.1
                · intro retained retainedMember pattern patternMember
                  simp at retainedMember
                  subst retained
                  exact valuesValid.2 pattern patternMember

/-- Qualified patterns preserve every ordinary token window. -/
theorem qualifiedPattern_preservesTokenWindow (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (qualifiedPattern nested) := by
  unfold qualifiedPattern
  apply Parser.bind_preservesTokenWindow
    (qualifiedName_preservesTokenWindow .pattern .pattern)
  intro path
  apply Parser.bind_preservesTokenWindow
    (optionalConstructorArguments_preservesTokenWindow nested nestedPreserves)
  intro arguments
  let components := path.value.components.toList
  cases reversed : components.reverse with
  | nil =>
      simp only [components, reversed]
      intro input
      trivial
  | cons name qualifiersRev =>
      simp only [components, reversed]
      split <;> exact Parser.pure_preservesTokenWindow _

theorem qualifiedPattern_preservesTokensOnSuccess
    (nested : Parser Pattern)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokensOnSuccess (qualifiedPattern nested) :=
  (qualifiedPattern_preservesTokenWindow
    nested nestedPreserves).preservesTokensOnSuccess

/-- Qualified patterns never rewind the cursor. -/
theorem qualifiedPattern_cursorMonotoneOnSuccess (nested : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess (qualifiedPattern nested) := by
  unfold qualifiedPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (qualifiedName_cursorMonotoneOnSuccess .pattern .pattern)
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalConstructorArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  let components := path.value.components.toList
  cases reversed : components.reverse with
  | nil =>
      intro input value final parsed
      simp only [components, reversed] at parsed
      contradiction
  | cons name qualifiersRev =>
      simp only [components, reversed]
      split <;> exact Parser.pure_cursorMonotoneOnSuccess _

/-- A qualified pattern starts at its first path component. -/
theorem qualifiedPattern_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (qualifiedPattern nested) (·.span) := by
  unfold qualifiedPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (qualifiedName_startsAtCurrentTokenOnSuccess .pattern .pattern)
  intro path input value final parsed
  rcases patternBind_ok_components parsed with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  let components := path.value.components.toList
  cases reversed : components.reverse with
  | nil => simp [components, reversed] at finished
  | cons name qualifiersRev =>
      simp only [components, reversed] at finished
      split at finished
      · cases finished
        rfl
      · cases arguments <;> cases finished <;> rfl

/-- Comptime patterns retain their marker, expression, and covering range. -/
theorem comptimePattern_validFor (expression : Parser Expr)
    (expressionValid : SourceFile → Expr → Prop)
    (parserValid : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (starts : Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (comptimePattern expression).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold comptimePattern
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := contextual_validFor .comptime .pattern input inputValid
      rw [markerResult] at valid
      exact valid
  | ok marker afterMarker =>
      have markerValid := contextual_validFor .comptime .pattern input
        inputValid
      rw [markerResult] at markerValid
      simp only
      cases expressionResult : expression afterMarker with
      | invariant error =>
          simp only [Reply.ValidFor]
      | reject failure rejected =>
          have valid := parserValid afterMarker markerValid.2.1
          rw [expressionResult] at valid
          simpa only [expressionResult, Reply.ValidFor] using
            valid.of_file_eq markerValid.2.2
      | ok value next =>
          have valid := parserValid afterMarker markerValid.2.1
          rw [expressionResult] at valid
          rcases starts afterMarker value next expressionResult with
            ⟨first, firstFound, valueStart⟩
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .pattern
            (·.isContextual .comptime) markerResult
          have advanced : input.advance? = some (marker, afterMarker) := by
            unfold State.advance?
            rw [markerShape.1, markerShape.2]
            rfl
          have separated :=
            inputValid.consumed_end_le_peek_start_after_advance
              advanced firstFound
          have markerSpanValid : marker.span.ValidFor input.file := by
            simpa only [Located.ValidFor] using markerValid.1
          have valueValidInput : expressionValid input.file value := by
            simpa [markerValid.2.2] using valid.1
          have valueSpanValid := spanValid valueValidInput
          have ordered : marker.span.startByte ≤ value.span.endByte :=
            Nat.le_trans markerSpanValid.2.1 (Nat.le_trans
              (by simpa [valueStart] using separated)
              valueSpanValid.2.1)
          simp only [Reply.ValidFor]
          exact ⟨Pattern.ValidFor.comptime
              (SourceSpan.cover_validFor markerSpanValid valueSpanValid ordered)
              markerSpanValid valueValidInput,
            valid.2.1, valid.2.2.trans markerValid.2.2⟩

/-- Comptime-pattern parsing preserves every ordinary token window. -/
theorem comptimePattern_preservesTokenWindow (expression : Parser Expr)
    (preserves : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (comptimePattern expression) := by
  intro input
  unfold comptimePattern
  have markerShape :=
    contextual_preservesTokenWindow .comptime .pattern input
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [markerResult] at markerShape
      exact markerShape
  | ok marker afterMarker =>
      rw [markerResult] at markerShape
      simp only
      have valueShape := preserves afterMarker
      cases expressionResult : expression afterMarker with
      | invariant error =>
          simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          rw [expressionResult] at valueShape
          simpa only [expressionResult, Reply.PreservesTokenWindow] using
            valueShape.trans markerShape
      | ok value next =>
          rw [expressionResult] at valueShape
          simpa only [expressionResult, Reply.PreservesTokenWindow] using
            valueShape.trans markerShape

/-- Comptime-pattern success preserves the immutable token carrier. -/
theorem comptimePattern_preservesTokensOnSuccess (expression : Parser Expr)
    (preserves : Parser.PreservesTokensOnSuccess expression) :
    Parser.PreservesTokensOnSuccess (comptimePattern expression) := by
  intro input value next result
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok inner final =>
          simp only [expressionResult] at result
          have innerTokens :=
            preserves afterMarker inner final expressionResult
          have markerTokens := contextual_preservesTokensOnSuccess
            .comptime .pattern input marker afterMarker markerResult
          cases result
          exact innerTokens.trans markerTokens

/-- Comptime-pattern parsing is cursor-monotone with its expression parser. -/
theorem comptimePattern_cursorMonotoneOnSuccess (expression : Parser Expr)
    (monotone : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (comptimePattern expression) := by
  intro input value next result
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok inner final =>
          simp only [expressionResult] at result
          have markerMonotone := contextual_cursorMonotoneOnSuccess
            .comptime .pattern input marker afterMarker markerResult
          have innerMonotone :=
            monotone afterMarker inner final expressionResult
          cases result
          exact Nat.le_trans markerMonotone innerMonotone

/-- A comptime pattern starts at the current `comptime` token. -/
theorem comptimePattern_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (comptimePattern expression) (·.span) := by
  intro input value next result
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok inner final =>
          simp only [expressionResult] at result
          cases result
          rcases contextual_startsAtCurrentTokenOnSuccess
              .comptime .pattern input marker afterMarker markerResult with
            ⟨token, found, start⟩
          exact ⟨token, found, start⟩

/-- Non-recovering pattern dispatch preserves source and state validity. -/
theorem patternCore_validFor (nested : Parser Pattern)
    (expression : Parser Expr)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (parserValid : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (starts : Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (patternCore nested expression).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold patternCore
  split
  · exact wildcardPattern_validFor expressionValid input inputValid
  · split
    · exact literalPattern_validFor expressionValid input inputValid
    · split
      · exact booleanBinderPattern_validFor expressionValid input inputValid
      · split
        · exact parenthesizedPattern_validFor nested expressionValid
            nestedValid nestedPreserves input inputValid
        · split
          · exact dotConstructorPattern_validFor nested expressionValid
              nestedValid nestedPreserves input inputValid
          · split
            · exact comptimePattern_validFor expression expressionValid
                parserValid spanValid starts input inputValid
            · split
              · exact qualifiedPattern_validFor nested expressionValid
                  nestedValid nestedPreserves input inputValid
              · unfold rejectAt Reply.ValidFor
                exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- Non-recovering pattern dispatch preserves every ordinary token window. -/
theorem patternCore_preservesTokenWindow (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionPreserves : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (patternCore nested expression) := by
  intro input
  unfold patternCore
  split
  · exact wildcardPattern_preservesTokenWindow input
  · split
    · exact literalPattern_preservesTokenWindow input
    · split
      · exact booleanBinderPattern_preservesTokenWindow input
      · split
        · exact parenthesizedPattern_preservesTokenWindow nested
            nestedPreserves input
        · split
          · exact dotConstructorPattern_preservesTokenWindow nested
              nestedPreserves input
          · split
            · exact comptimePattern_preservesTokenWindow expression
                expressionPreserves input
            · split
              · exact qualifiedPattern_preservesTokenWindow nested
                  nestedPreserves input
              · exact rejectAt_preservesTokenWindow input _ _

/-- Non-recovering pattern success preserves the immutable token carrier. -/
theorem patternCore_preservesTokensOnSuccess (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionPreserves : Parser.PreservesTokensOnSuccess expression) :
    Parser.PreservesTokensOnSuccess (patternCore nested expression) := by
  intro input pattern next parsed
  unfold patternCore at parsed
  split at parsed
  · exact wildcardPattern_preservesTokensOnSuccess input pattern next parsed
  · split at parsed
    · exact literalPattern_preservesTokensOnSuccess input pattern next parsed
    · split at parsed
      · exact booleanBinderPattern_preservesTokensOnSuccess
          input pattern next parsed
      · split at parsed
        · exact parenthesizedPattern_preservesTokensOnSuccess nested
            nestedPreserves input pattern next parsed
        · split at parsed
          · exact dotConstructorPattern_preservesTokensOnSuccess nested
              nestedPreserves input pattern next parsed
          · split at parsed
            · exact comptimePattern_preservesTokensOnSuccess expression
                expressionPreserves input pattern next parsed
            · split at parsed
              · exact qualifiedPattern_preservesTokensOnSuccess nested
                  nestedPreserves input pattern next parsed
              · unfold rejectAt at parsed
                contradiction

/-- Non-recovering pattern dispatch never rewinds the parser cursor. -/
theorem patternCore_cursorMonotoneOnSuccess (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (patternCore nested expression) := by
  intro input pattern next parsed
  unfold patternCore at parsed
  split at parsed
  · exact wildcardPattern_cursorMonotoneOnSuccess input pattern next parsed
  · split at parsed
    · exact literalPattern_cursorMonotoneOnSuccess input pattern next parsed
    · split at parsed
      · exact booleanBinderPattern_cursorMonotoneOnSuccess
          input pattern next parsed
      · split at parsed
        · exact parenthesizedPattern_cursorMonotoneOnSuccess nested
            nestedMonotone input pattern next parsed
        · split at parsed
          · exact dotConstructorPattern_cursorMonotoneOnSuccess nested
              input pattern next parsed
          · split at parsed
            · exact comptimePattern_cursorMonotoneOnSuccess expression
                expressionMonotone input pattern next parsed
            · split at parsed
              · exact qualifiedPattern_cursorMonotoneOnSuccess nested
                  input pattern next parsed
              · unfold rejectAt at parsed
                contradiction

/-- Non-recovering pattern success starts at the selected leading token. -/
theorem patternCore_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (patternCore nested expression) (·.span) := by
  intro input pattern next parsed
  unfold patternCore at parsed
  split at parsed
  · exact wildcardPattern_startsAtCurrentTokenOnSuccess
      input pattern next parsed
  · split at parsed
    · exact literalPattern_startsAtCurrentTokenOnSuccess
        input pattern next parsed
    · split at parsed
      · exact booleanBinderPattern_startsAtCurrentTokenOnSuccess
          input pattern next parsed
      · split at parsed
        · exact parenthesizedPattern_startsAtCurrentTokenOnSuccess nested
            input pattern next parsed
        · split at parsed
          · exact dotConstructorPattern_startsAtCurrentTokenOnSuccess nested
              input pattern next parsed
          · split at parsed
            · exact comptimePattern_startsAtCurrentTokenOnSuccess expression
                input pattern next parsed
            · split at parsed
              · exact qualifiedPattern_startsAtCurrentTokenOnSuccess nested
                  input pattern next parsed
              · unfold rejectAt at parsed
                contradiction

/-- Finishing pattern recovery retains one source-valid error range. -/
theorem finishRecoveredPattern_validFor
    (expressionValid : SourceFile → Expr → Prop)
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredPattern first last state).ValidFor state
      (Pattern.ValidFor expressionValid) := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredPattern Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩

/-- Pattern recovery preserves provenance while consuming malformed tokens. -/
theorem recoverPatternAux_validFor
    (expressionValid : SourceFile → Expr → Prop) (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverPatternAux first last fuel state).ValidFor state
        (Pattern.ValidFor expressionValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverPatternAux
      split
      · exact finishRecoveredPattern_validFor expressionValid first last state
          stateValid firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredPattern_validFor expressionValid first last
              state stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Finishing recovery leaves the immutable token window unchanged. -/
theorem finishRecoveredPattern_preservesTokenWindow
    (first last : SourceSpan) :
    Parser.PreservesTokenWindow (finishRecoveredPattern first last) := by
  intro input
  unfold finishRecoveredPattern Reply.PreservesTokenWindow State.emit
  exact ⟨rfl, rfl⟩

/-- Pattern recovery preserves the complete immutable token window. -/
theorem recoverPatternAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverPatternAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverPatternAux
      split
      · exact finishRecoveredPattern_preservesTokenWindow first last input
      · cases advanced : input.advance? with
        | none =>
            exact finishRecoveredPattern_preservesTokenWindow first last input
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])

/-- Successful pattern recovery retains the immutable token carrier. -/
theorem recoverPatternAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (recoverPatternAux first last fuel) :=
  (recoverPatternAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

/-- Pattern recovery never rewinds the cursor on success. -/
theorem recoverPatternAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (recoverPatternAux first last fuel) := by
  intro input value next result
  induction fuel generalizing last input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold recoverPatternAux at result
      split at result
      · unfold finishRecoveredPattern at result
        cases result
        exact Nat.le_refl _
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredPattern at result
            cases result
            exact Nat.le_refl _
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceCursor : input.cursor ≤ afterToken.cursor := by
              rw [(advance?_state_shape advanced).2]
              exact Nat.le_add_right _ 1
            exact Nat.le_trans advanceCursor
              (inductionHypothesis token.span afterToken result)

/-- Every recovered error pattern starts at the first consumed token span. -/
theorem recoverPatternAux_startsAtFirstSpanOnSuccess
    (first last : SourceSpan) (fuel : Nat) {input next : State}
    {pattern : Pattern}
    (parsed : recoverPatternAux first last fuel input = .ok pattern next) :
    pattern.span.startByte = first.startByte := by
  induction fuel generalizing last input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold recoverPatternAux at parsed
      split at parsed
      · unfold finishRecoveredPattern at parsed
        cases parsed
        rfl
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredPattern at parsed
            cases parsed
            rfl
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at parsed
            exact inductionHypothesis token.span parsed

/-- Recovery entered by advancing starts at the caller's current token. -/
theorem recoverPatternAux_startsAtAdvancedCurrentTokenOnSuccess
    {input afterToken next : State} {token : Token} {pattern : Pattern}
    (last : SourceSpan) (fuel : Nat)
    (advanced : input.advance? = some (token, afterToken))
    (parsed : recoverPatternAux token.span last fuel afterToken =
      .ok pattern next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = pattern.span.startByte := by
  refine ⟨token, (advance?_state_shape advanced).1, ?_⟩
  exact (recoverPatternAux_startsAtFirstSpanOnSuccess token.span last fuel
    parsed).symm

/-- One recovering pattern layer preserves recursive source provenance. -/
theorem patternLayer_validFor (nested : Parser Pattern)
    (expression : Parser Expr)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionParserValid : expression.ValidFor expressionValid)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span))
    (expressionPreserves : Parser.PreservesTokenWindow expression) :
    (patternLayer nested expression).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold patternLayer
  cases coreResult : patternCore nested expression input with
  | ok pattern next =>
      have coreValid := patternCore_validFor nested expression expressionValid
        nestedValid nestedPreserves.preservesTokensOnSuccess
        expressionParserValid expressionSpanValid expressionStarts
        input inputValid
      rw [coreResult] at coreValid
      exact coreValid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := patternCore_validFor nested expression expressionValid
        nestedValid nestedPreserves.preservesTokensOnSuccess
        expressionParserValid expressionSpanValid expressionStarts
        input inputValid
      rw [coreResult] at coreValid
      have coreShape := patternCore_preservesTokenWindow nested expression
        nestedPreserves expressionPreserves input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, coreValid.2.2] using coreValid.1
      change (if isPatternBoundary rewound then
          Reply.reject failure rewound
        else match rewound.advance? with
        | some (token, next) =>
            recoverPatternAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).ValidFor input
          (Pattern.ValidFor expressionValid)
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · cases advanced : rewound.advance? with
        | none => exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            have advanceShape := advance?_state_shape advanced
            have nextValid := rewoundValid.advance?_validFor advanced
            have tokenValid : token.span.ValidFor next.file := by
              rw [advanceShape.2]
              exact rewoundValid.peek?_span_validFor advanceShape.1
            have emittedValid := nextValid.emit_validFor failure.toDiagnostic
              (by simpa [advanceShape.2] using
                failure.toDiagnostic_span_validFor failureValid)
            have currentFound :
                (next.emit failure.toDiagnostic).tokens[rewound.cursor]? =
                  some token := by
              simpa [advanceShape.2, State.emit] using
                State.getElem?_eq_some_of_peek?_eq_some advanceShape.1
            have recovered := recoverPatternAux_validFor expressionValid
              token.span (next.remainingCount + 1) token.span
              (next.emit failure.toDiagnostic) rewound.cursor token
              emittedValid (by simpa [State.emit] using tokenValid)
              (by simpa [State.emit] using tokenValid) tokenValid.2.1
              currentFound rfl (by simp [advanceShape.2, State.emit])
            exact recovered.of_file_eq (by
              simpa [advanceShape.2, State.emit] using rewoundFile)

/-- A recovering pattern layer preserves every ordinary token window. -/
theorem patternLayer_preservesTokenWindow (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionPreserves : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (patternLayer nested expression) := by
  intro input
  unfold patternLayer
  cases coreResult : patternCore nested expression input with
  | invariant error => trivial
  | ok pattern next =>
      have coreShape := patternCore_preservesTokenWindow nested expression
        nestedPreserves expressionPreserves input
      rw [coreResult] at coreShape
      exact coreShape
  | reject failure failedState =>
      have coreShape := patternCore_preservesTokenWindow nested expression
        nestedPreserves expressionPreserves input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using coreShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        simpa [rewound] using failedShape
      change (if isPatternBoundary rewound then
          Reply.reject failure rewound
        else match rewound.advance? with
        | some (token, next) =>
            recoverPatternAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).PreservesTokenWindow input
      split
      · exact rewoundShape
      · cases advanced : rewound.advance? with
        | none => exact rewoundShape
        | some pair =>
            rcases pair with ⟨token, next⟩
            have recovered := recoverPatternAux_preservesTokenWindow
              token.span token.span (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
            exact recovered.trans (by
              simpa [State.emit, (advance?_state_shape advanced).2] using
                rewoundShape)

/-- Successful recovering pattern parsing retains the token carrier. -/
theorem patternLayer_preservesTokensOnSuccess (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionPreserves : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (patternLayer nested expression) :=
  (patternLayer_preservesTokenWindow nested expression nestedPreserves
    expressionPreserves).preservesTokensOnSuccess

/-- A recovering pattern layer never rewinds its caller's cursor. -/
theorem patternLayer_cursorMonotoneOnSuccess (nested : Parser Pattern)
    (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (patternLayer nested expression) := by
  intro input pattern next result
  unfold patternLayer at result
  cases coreResult : patternCore nested expression input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have monotone := patternCore_cursorMonotoneOnSuccess nested expression
        nestedMonotone expressionMonotone input value afterCore coreResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isPatternBoundary rewound then
          Reply.reject failure rewound
        else match rewound.advance? with
        | some (token, afterToken) =>
            recoverPatternAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok pattern next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverPatternAux_cursorMonotoneOnSuccess
              token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) pattern next result
            exact Nat.le_trans
              (by simp [(advance?_state_shape advanced).2,
                State.emit, rewound]) recovered

/-- A successful recovering layer starts at its caller's current token. -/
theorem patternLayer_startsAtCurrentTokenOnSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedPreserves : Parser.PreservesTokenWindow nested)
    (expressionPreserves : Parser.PreservesTokenWindow expression) :
    Parser.StartsAtCurrentTokenOnSuccess
      (patternLayer nested expression) (·.span) := by
  intro input pattern next result
  unfold patternLayer at result
  cases coreResult : patternCore nested expression input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have starts := patternCore_startsAtCurrentTokenOnSuccess
        nested expression input value afterCore coreResult
      cases result
      simpa using starts
  | reject failure failedState =>
      simp only [coreResult] at result
      have coreShape := patternCore_preservesTokenWindow nested expression
        nestedPreserves expressionPreserves input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isPatternBoundary rewound then
          Reply.reject failure rewound
        else match rewound.advance? with
        | some (token, afterToken) =>
            recoverPatternAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok pattern next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceShape := advance?_state_shape advanced
            have found : input.peek? = some token := by
              have rewoundFound := advanceShape.1
              unfold State.peek? at rewoundFound ⊢
              simpa [rewound, coreShape.1, coreShape.2] using rewoundFound
            have recovered := recoverPatternAux_startsAtFirstSpanOnSuccess
              token.span token.span (afterToken.remainingCount + 1) result
            exact ⟨token, found, recovered.symm⟩

end PatternInternals
end Solcore.Syntax.Parser
