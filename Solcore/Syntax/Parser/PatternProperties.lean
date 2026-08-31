import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.PatternValidity

/-! Provenance and carrier contracts for canonical pattern parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PatternInternals

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

end PatternInternals
end Solcore.Syntax.Parser
