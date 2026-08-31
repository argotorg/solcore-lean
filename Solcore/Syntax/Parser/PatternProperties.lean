import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.PatternValidity

/-! Provenance and carrier contracts for canonical pattern parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PatternInternals

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

end PatternInternals
end Solcore.Syntax.Parser
