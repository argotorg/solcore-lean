import Solcore.Syntax.Parser.Expression
import Solcore.Syntax.Unicode.Lowercase
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.PatternValidity
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.LiteralTotalityProperties
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.QualifiedNameTotalityProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace PatternInternals

/-- Parse the canonical wildcard pattern leaf. -/
def wildcardPattern : Parser Pattern := do
  let marker ← symbol .underscore .pattern
  pure {
    span := marker.span
    value := .wildcard marker.span
  }

/-- Parse one canonical literal pattern leaf. -/
def literalPattern : Parser Pattern := do
  let literal ← coreLiteral
  pure {
    span := literal.span
    value := .literal literal
  }

/-- Parse `true` or `false` as a binder-shaped builtin pattern. -/
def booleanBinderPattern : Parser Pattern := do
  let name ← booleanIdentifier
  pure {
    span := name.span
    value := .binder name
  }

end PatternInternals

namespace PatternInternals

/-- Parse an ordinary or Boolean builtin constructor-pattern name. -/
def patternName : Parser Identifier := fun state =>
  if isBooleanValue state then booleanIdentifier state
  else identifier .pattern state

/-- Refine a parsed constructor argument list to its nonempty carrier. -/
def requirePatternArguments (values : DelimitedList Pattern) :
    Parser (NonemptyDelimitedList Pattern) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .pattern values.span)

/-- Parse a required nonempty constructor-pattern argument list. -/
def constructorArguments
    (nested : Parser Pattern) : Parser (NonemptyDelimitedList Pattern) := do
  let values ← delimitedNoTrailing .leftParen .rightParen false nested
    .pattern .pattern
  requirePatternArguments values

/-- Parse constructor arguments when an opening parenthesis is present. -/
def optionalConstructorArguments
    (nested : Parser Pattern) : Parser (Option (NonemptyDelimitedList Pattern)) :=
    fun state =>
  if isSymbol state .leftParen then
    orElse
      (do pure (some (← constructorArguments nested)))
      (pure none) state
  else
    .ok none state

end PatternInternals

namespace PatternInternals

/-- Close a parenthesized pattern after its elements have been accumulated. -/
def closePatternTuple (opening : Token)
    (elementsRev : List Pattern) : Parser Pattern := do
  let closing ← symbol .rightParen .pattern
  let span := SourceSpan.cover opening.span closing.span
  match elementsRev with
  | [only] => pure { span, value := .group only }
  | _ => pure {
      span
      value := .tuple { span, elements := elementsRev.reverse }
    }

end PatternInternals

namespace PatternInternals

/-- Continue a parenthesized tuple after its first comma. -/
def patternTupleTail (nested : Parser Pattern) (opening : Token) :
    Nat → List Pattern → State → Reply Pattern
  | 0, _, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, elementsRev, state =>
      match symbol .comma .pattern state with
      | .ok _ afterComma =>
          if isSymbol afterComma .rightParen then
            PatternInternals.closePatternTuple opening elementsRev afterComma
          else
            let before := afterComma.cursor
            match nested afterComma with
            | .ok value next =>
                if next.cursor ≤ before then
                  .invariant (.noProgress .pattern next.currentSpan)
                else if isSymbol next .comma then
                  patternTupleTail nested opening fuel
                    (value :: elementsRev) next
                else
                  PatternInternals.closePatternTuple opening
                    (value :: elementsRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Parse an empty tuple, grouped pattern, or comma-separated tuple. -/
def parenthesizedPattern (nested : Parser Pattern) : Parser Pattern :=
    fun state =>
  match symbol .leftParen .pattern state with
  | .ok opening afterOpening =>
      if isSymbol afterOpening .rightParen then
        PatternInternals.closePatternTuple opening [] afterOpening
      else
        let before := afterOpening.cursor
        match nested afterOpening with
        | .ok first next =>
            if next.cursor ≤ before then
              .invariant (.noProgress .pattern next.currentSpan)
            else if isSymbol next .comma then
              patternTupleTail nested opening
                (next.remainingCount + 1)
                [first] next
            else
              closePatternTuple opening [first] next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Parse a leading-dot constructor pattern. -/
def dotConstructorPattern
    (nested : Parser Pattern) : Parser Pattern := do
  let dot ← symbol .dot .pattern
  let name ← PatternInternals.patternName
  let arguments ← PatternInternals.optionalConstructorArguments nested
  let endSpan := arguments.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover dot.span endSpan
    value := .constructor (some dot.span) [] name arguments
  }

end PatternInternals

private def startsWithLowercase (name : Identifier) : Bool :=
  match name.value.toList with
  | first :: _ => Unicode.isLowercase first
  | [] => true

namespace PatternInternals

/-- Parse a binder or constructor pattern beginning with a qualified name. -/
def qualifiedPattern (nested : Parser Pattern) : Parser Pattern := do
  let path ← qualifiedName .pattern .pattern
  let arguments ← PatternInternals.optionalConstructorArguments nested
  let components := path.value.components.toList
  match components.reverse with
  | [] => fun _ => .invariant (.noProgress .pattern path.span)
  | name :: qualifiersRev =>
      if qualifiersRev.isEmpty && arguments.isNone &&
          startsWithLowercase name then
        pure { span := path.span, value := .binder name }
      else
        let endSpan := arguments.map (fun values => values.span) |>.getD path.span
        pure {
          span := SourceSpan.cover path.span endSpan
          value := .constructor none qualifiersRev.reverse name arguments
        }

end PatternInternals

namespace PatternInternals

/-- Parse a comptime pattern using the supplied expression parser. -/
def comptimePattern (expression : Parser Expr) : Parser Pattern := fun state =>
  match contextual .comptime .pattern state with
  | .ok marker afterMarker =>
      match expression afterMarker with
      | .ok value next => .ok {
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        } next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Dispatch one non-recovering canonical pattern layer. -/
def patternCore (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  if isSymbol state .underscore then
    PatternInternals.wildcardPattern state
  else if isCoreLiteral state then
    PatternInternals.literalPattern state
  else if isBooleanValue state then
    PatternInternals.booleanBinderPattern state
  else if isSymbol state .leftParen then
    PatternInternals.parenthesizedPattern nested state
  else if isSymbol state .dot then
    PatternInternals.dotConstructorPattern nested state
  else if isContextual state .comptime then
    PatternInternals.comptimePattern expression state
  else if isIdentifier state then PatternInternals.qualifiedPattern nested state
  else rejectAt state { head := .pattern, tail := [] } .pattern

end PatternInternals

namespace PatternInternals

/-- Whether pattern recovery must stop before the current token. -/
def isPatternBoundary (state : State) : Bool :=
  state.atEnd ||
    [.comma, .rightParen, .fatArrow, .pipe, .rightBrace].any
      (isSymbol state)

/-- Finish recovery with one error pattern spanning the consumed tokens. -/
def finishRecoveredPattern (first last : SourceSpan)
    (state : State) : Reply Pattern :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .pattern
  })

/-- Consume malformed pattern tokens until a canonical boundary is reached. -/
def recoverPatternAux (first last : SourceSpan) :
    Nat → State → Reply Pattern
  | 0, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, state =>
      if isPatternBoundary state then
        finishRecoveredPattern first last state
      else
        match state.advance? with
        | some (token, next) => recoverPatternAux first token.span fuel next
        | none => finishRecoveredPattern first last state

end PatternInternals

/-- Build one pattern recursion layer with a supplied comptime expression. -/
def patternLayer (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  match PatternInternals.patternCore nested expression state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if PatternInternals.isPatternBoundary rewound then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            PatternInternals.recoverPatternAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

/-- Whether the current token may begin a canonical pattern. -/
def startsPattern (state : State) : Bool :=
  isSymbol state .underscore || isCoreLiteral state ||
    isBooleanValue state || isSymbol state .leftParen ||
    isSymbol state .dot || isContextual state .comptime ||
    isIdentifier state

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternProperties`
-/

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

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternLeafTotalityProperties`
-/

/-! Totality for non-recursive pattern leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

theorem wildcardPattern_ordinary : Parser.Ordinary wildcardPattern := by
  intro input
  rcases (symbol_ordinary .underscore .pattern) input with
    ⟨marker, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := marker.span
        value := .wildcard marker.span
      }, next, by simp only [wildcardPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [wildcardPattern, bind, result]⟩

theorem wildcardPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid wildcardPattern :=
  wildcardPattern_ordinary.invariantFreeOnValid

theorem wildcardPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    wildcardPattern input ≠ .invariant error :=
  wildcardPattern_ordinary.ne_invariant input error

theorem literalPattern_ordinary : Parser.Ordinary literalPattern := by
  intro input
  rcases coreLiteral_ordinary input with
    ⟨literal, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := literal.span
        value := .literal literal
      }, next, by simp only [literalPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [literalPattern, bind, result]⟩

theorem literalPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid literalPattern :=
  literalPattern_ordinary.invariantFreeOnValid

theorem literalPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    literalPattern input ≠ .invariant error :=
  literalPattern_ordinary.ne_invariant input error

theorem booleanBinderPattern_ordinary :
    Parser.Ordinary booleanBinderPattern := by
  intro input
  rcases booleanIdentifier_ordinary input with
    ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := name.span
        value := .binder name
      }, next, by simp only [booleanBinderPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [booleanBinderPattern, bind, result]⟩

theorem booleanBinderPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid booleanBinderPattern :=
  booleanBinderPattern_ordinary.invariantFreeOnValid

theorem booleanBinderPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    booleanBinderPattern input ≠ .invariant error :=
  booleanBinderPattern_ordinary.ne_invariant input error

theorem patternName_ordinary : Parser.Ordinary patternName := by
  intro input
  unfold patternName
  split
  · exact booleanIdentifier_ordinary input
  · exact identifier_ordinary .pattern input

theorem patternName_invariantFreeOnValid :
    Parser.InvariantFreeOnValid patternName :=
  patternName_ordinary.invariantFreeOnValid

theorem patternName_ne_invariant (input : State)
    (error : ParserInvariantError) :
    patternName input ≠ .invariant error :=
  patternName_ordinary.ne_invariant input error

theorem patternName_elementTotalityContract :
    ElementTotalityContract patternName := {
  validFor := patternName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := patternName_preservesTokenWindow
  cursorLtOnSuccess := patternName_cursor_lt_onSuccess
  invariantFree := fun input _ error => patternName_ne_invariant input error
}

/-- Comptime leaves add no invariant beyond the supplied expression parser. -/
theorem comptimePattern_invariantFreeOnValid (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid (comptimePattern expression) := by
  intro input inputValid
  rcases (contextual_ordinary .comptime .pattern) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := contextual_validFor .comptime .pattern input inputValid
    rw [markerResult] at markerValid
    have expressionFree := Parser.invariantFreeOnValid_of_ne_invariant
      expressionContract.invariantFree
    rcases expressionFree afterMarker markerValid.2.1 with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        }, next, by
          simp only [comptimePattern, markerResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [comptimePattern, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [comptimePattern, markerResult]⟩

theorem comptimePattern_ordinary (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor) :
    (∃ pattern next, comptimePattern expression input = .ok pattern next) ∨
    (∃ failure next,
      comptimePattern expression input = .reject failure next) :=
  comptimePattern_invariantFreeOnValid expression expressionContract
    input inputValid

theorem comptimePattern_ne_invariant (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    comptimePattern expression input ≠ .invariant error :=
  (comptimePattern_invariantFreeOnValid expression expressionContract)
    |>.ne_invariant input inputValid error

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternLeafFuelTotalityProperties`
-/

/-! Recursive-fuel totality for comptime pattern leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/--
Consuming the `comptime` marker places the recursive expression call below its
fixed fuel bound.
-/
theorem comptimePattern_ordinary_of_elementFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, comptimePattern expression input = .ok pattern next) ∨
    (∃ failure next,
      comptimePattern expression input = .reject failure next) := by
  rcases (contextual_ordinary .comptime .pattern) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := contextual_validFor .comptime .pattern
      input inputValid
    rw [markerResult] at markerValid
    have markerWindow := contextual_preservesTokenWindow
      .comptime .pattern input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.contextual .comptime) .pattern
        (·.isContextual .comptime) markerResult
    have expressionAdequate :
        afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerValid.2.1
        markerWindow.2 markerProgress adequate
    rcases contract.ordinary afterMarker markerValid.2.1
        expressionAdequate with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        }, next, by
          simp only [comptimePattern, markerResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [comptimePattern, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [comptimePattern, markerResult]⟩

theorem comptimePattern_ne_invariant_of_elementFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    comptimePattern expression input ≠ .invariant error := by
  intro failed
  rcases comptimePattern_ordinary_of_elementFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternArgumentsFuelTotalityProperties`
-/

/-! Fuel-aware totality for recursive constructor-pattern arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A syntactically nonempty argument parse satisfies its defensive refinement. -/
theorem requirePatternArguments_ok_of_delimitedNoTrailing_false_ok
    (nested : Parser Pattern)
    {input afterDelimited : State} {parsed : DelimitedList Pattern}
    (parsedResult : delimitedNoTrailing .leftParen .rightParen false nested
      .pattern .pattern input = .ok parsed afterDelimited) :
    ∃ nonempty,
      requirePatternArguments parsed afterDelimited =
        .ok nonempty afterDelimited := by
  have nonempty := delimitedNoTrailing_false_elements_ne_nil_onSuccess
    .leftParen .rightParen nested .pattern .pattern parsedResult
  unfold requirePatternArguments
  cases elements : parsed.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

theorem constructorArguments_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      constructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      constructorArguments nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_elementFuel
      .leftParen .rightParen false false nested .pattern .pattern
      nestedFuel contract input inputValid adequate with
    ⟨parsed, afterDelimited, parsedResult⟩ |
    ⟨failure, rejected, parsedResult⟩
  · have noTrailingResult :
        delimitedNoTrailing .leftParen .rightParen false nested
          .pattern .pattern input = .ok parsed afterDelimited := by
      simpa only [delimitedNoTrailing] using parsedResult
    rcases requirePatternArguments_ok_of_delimitedNoTrailing_false_ok
        nested noTrailingResult with ⟨nonempty, nonemptyResult⟩
    exact Or.inl ⟨nonempty, afterDelimited, by
      simp only [constructorArguments, bind, noTrailingResult,
        nonemptyResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [constructorArguments, bind, delimitedNoTrailing,
        parsedResult]⟩

theorem constructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    constructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases constructorArguments_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem optionalConstructorArguments_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalConstructorArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases constructorArguments_ordinary_of_elementFuel nested nestedFuel
        contract input inputValid adequate with
      ⟨arguments, next, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · exact Or.inl ⟨some arguments, next, by
        simp only [optionalConstructorArguments, present, ↓reduceIte,
          orElse, argumentsResult, pure, bind]⟩
    · exact Or.inl ⟨none, input, by
        simp only [optionalConstructorArguments, present, ↓reduceIte,
          orElse, argumentsResult, pure, bind]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalConstructorArguments, absent, Bool.false_eq_true,
        ↓reduceIte]⟩

theorem optionalConstructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalConstructorArguments_ordinary_of_elementFuel nested
      nestedFuel contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternConstructorFuelTotalityProperties`
-/

/-! Fuel-aware totality for leading-dot constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

theorem dotConstructorPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ pattern next,
      dotConstructorPattern nested input = .ok pattern next) ∨
    (∃ failure next,
      dotConstructorPattern nested input = .reject failure next) := by
  rcases (symbol_ordinary .dot .pattern) input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have dotValid := symbol_validFor .dot .pattern input inputValid
    rw [dotResult] at dotValid
    have dotWindow := symbol_preservesTokenWindow .dot .pattern input
    rw [dotResult] at dotWindow
    have afterDotAdequate : afterDot.remainingCount < nestedFuel :=
      remainingCount_lt_after_strict_progress dotValid.2.1 dotWindow.2
        (acceptToken_cursor_lt_onSuccess (.symbol .dot) .pattern
          (· == .symbol .dot) dotResult) adequate
    rcases patternName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameValid := patternName_validFor afterDot dotValid.2.1
      rw [nameResult] at nameValid
      have nameWindow := patternName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (Nat.le_of_lt (patternName_cursor_lt_onSuccess nameResult))
          afterDotAdequate
      rcases optionalConstructorArguments_ordinary_of_elementFuel nested
          nestedFuel contract afterName nameValid.2.1 (by omega) with
        ⟨arguments, final, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact Or.inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .constructor (some dot.span) [] name arguments
          }, final, by
            simp only [dotConstructorPattern, bind, dotResult, nameResult,
              argumentsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [dotConstructorPattern, bind, dotResult, nameResult,
            argumentsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [dotConstructorPattern, bind, dotResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [dotConstructorPattern, bind, dotResult]⟩

theorem dotConstructorPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    dotConstructorPattern nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructorPattern_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternQualifiedFuelTotalityProperties`
-/

/-! Fuel-aware totality for qualified binder and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A qualified name's nonempty carrier remains nonempty after reversal. -/
theorem qualifiedName_components_reverse_ne_nil (path : QualifiedName) :
    path.value.components.toList.reverse ≠ [] := by
  rcases path.value.components with ⟨head, tail⟩
  simp [NonemptyList.toList]

theorem qualifiedPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ pattern next, qualifiedPattern nested input = .ok pattern next) ∨
    (∃ failure next,
      qualifiedPattern nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .pattern .pattern) input with
    ⟨path, afterPath, pathResult⟩ |
    ⟨failure, rejected, pathResult⟩
  · have pathValid := qualifiedName_validFor .pattern .pattern input inputValid
    rw [pathResult] at pathValid
    have pathWindow := qualifiedName_preservesTokenWindow .pattern .pattern input
    rw [pathResult] at pathWindow
    have afterPathAdequate : afterPath.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le pathWindow.2
        (qualifiedName_cursorMonotoneOnSuccess .pattern .pattern input path
          afterPath pathResult) adequate
    rcases optionalConstructorArguments_ordinary_of_elementFuel nested
        nestedFuel contract afterPath pathValid.2.1 afterPathAdequate with
      ⟨arguments, final, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · let components := path.value.components.toList
      cases reversed : components.reverse with
      | nil =>
          exact False.elim
            (qualifiedName_components_reverse_ne_nil path (by
              simpa only [components] using reversed))
      | cons name qualifiersRev =>
          simp only [qualifiedPattern, bind, pathResult, argumentsResult,
            components, reversed]
          split <;> exact Or.inl ⟨_, final, rfl⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [qualifiedPattern, bind, pathResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [qualifiedPattern, bind, pathResult]⟩

theorem qualifiedPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    qualifiedPattern nested input ≠ .invariant error := by
  intro failed
  rcases qualifiedPattern_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternRecoveryTotalityProperties`
-/

/-! Production-fuel adequacy for malformed pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- More fuel than remaining tokens makes pattern recovery terminate. -/
theorem recoverPatternAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
    ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverPatternAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverPatternAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ value final,
              recoverPatternAux first token.span fuel next = .ok value final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- Adequately fueled recovery has an ordinary success result. -/
theorem recoverPatternAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ value final,
      recoverPatternAux first last fuel state = .ok value final) ∨
      (∃ failure final,
        recoverPatternAux first last fuel state = .reject failure final) :=
  Or.inl (recoverPatternAux_exists_ok_of_remainingCount_lt first
    fuel last state adequate)

theorem recoverPatternAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverPatternAux first last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverPatternAux_exists_ok_of_remainingCount_lt first fuel last state
      adequate with ⟨value, final, result⟩
  rw [result] at failed
  contradiction

/-- The production recovery fuel is always adequate. -/
theorem recoverPatternAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverPatternAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverPatternAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

/-- Production-fueled recovery is ordinary on every input state. -/
theorem recoverPatternAux_production_ordinary (first last : SourceSpan) :
    Parser.Ordinary (fun state =>
      recoverPatternAux first last (state.remainingCount + 1) state) := by
  intro state
  exact Or.inl (recoverPatternAux_production_exists_ok first last state)

/-- Production-fueled recovery is invariant-free on valid parser states. -/
theorem recoverPatternAux_production_invariantFreeOnValid
    (first last : SourceSpan) :
    Parser.InvariantFreeOnValid (fun state =>
      recoverPatternAux first last (state.remainingCount + 1) state) :=
  (recoverPatternAux_production_ordinary first last).invariantFreeOnValid

/-- Production-fueled recovery cannot expose an internal invariant. -/
theorem recoverPatternAux_production_ne_invariant
    (first last : SourceSpan) (state : State)
    (error : ParserInvariantError) :
    recoverPatternAux first last (state.remainingCount + 1) state ≠
      .invariant error :=
  (recoverPatternAux_production_ordinary first last).ne_invariant state error

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternTupleTotalityProperties`
-/

/-! Fuel-aware totality for grouped patterns and pattern tuples. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Closing a grouped pattern or tuple is invariant-free on valid input. -/
theorem closePatternTuple_invariantFreeOnValid (opening : Token)
    (elementsRev : List Pattern) :
    Parser.InvariantFreeOnValid (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .rightParen .pattern)
    (symbol_ordinary .rightParen .pattern).invariantFreeOnValid
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_invariantFreeOnValid _
  | cons only tail =>
      cases tail <;> exact Parser.pure_invariantFreeOnValid _

/--
The pattern-tuple tail is ordinary when both its loop fuel and the nested
parser's fixed recursive-fuel bound are adequate.
-/
theorem patternTupleTail_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      (∃ value next,
        patternTupleTail nested opening loopFuel elementsRev input =
          .ok value next) ∨
      (∃ failure next,
        patternTupleTail nested opening loopFuel elementsRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      unfold patternTupleTail
      cases commaResult : symbol .comma .pattern input with
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .comma .pattern input error commaResult)
      | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
      | ok comma afterComma =>
          have commaValid := symbol_validFor .comma .pattern input inputValid
          rw [commaResult] at commaValid
          have commaWindow := symbol_preservesTokenWindow .comma .pattern input
          rw [commaResult] at commaWindow
          have commaProgress : input.cursor < afterComma.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .comma) .pattern
              (· == .symbol .comma) commaResult
          have afterCommaNestedAdequate :
              afterComma.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress commaValid.2.1
              commaWindow.2 commaProgress nestedAdequate
          simp only
          split
          · exact closePatternTuple_invariantFreeOnValid opening elementsRev
              afterComma commaValid.2.1
          · cases nestedResult : nested afterComma with
            | invariant error =>
                exact False.elim (contract.ne_invariant afterComma
                  commaValid.2.1 afterCommaNestedAdequate error nestedResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have valueValid := contract.validFor afterComma commaValid.2.1
                rw [nestedResult] at valueValid
                have valueWindow := contract.preservesTokenWindow afterComma
                rw [nestedResult] at valueWindow
                have valueProgress := contract.cursorLtOnSuccess nestedResult
                dsimp only
                split
                · omega
                · split
                  · have nextWindow : next.window = input.window :=
                      valueWindow.2.trans commaWindow.2
                    have nextLoopAdequate :
                        next.remainingCount < loopFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        nextWindow (Nat.lt_trans commaProgress valueProgress)
                        (by simpa [Nat.succ_eq_add_one] using loopAdequate)
                    have nextNestedAdequate :
                        next.remainingCount < nestedFuel + 1 := by
                      have preserved : next.remainingCount < nestedFuel :=
                        remainingCount_lt_of_cursor_le valueWindow.2
                          (Nat.le_of_lt valueProgress)
                          afterCommaNestedAdequate
                      omega
                    exact inductionHypothesis (value :: elementsRev) next
                      valueValid.2.1 nextLoopAdequate nextNestedAdequate
                  · exact closePatternTuple_invariantFreeOnValid opening
                      (value :: elementsRev) next valueValid.2.1

theorem patternTupleTail_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (loopFuel : Nat) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    patternTupleTail nested opening loopFuel elementsRev input ≠
      .invariant error := by
  intro failed
  rcases patternTupleTail_ordinary_of_elementFuel nested nestedFuel contract
      opening loopFuel elementsRev input inputValid loopAdequate
        nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production pattern-tuple loop fuel is always adequate. -/
theorem patternTupleTail_production_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next,
      patternTupleTail nested opening (input.remainingCount + 1) elementsRev
        input = .ok value next) ∨
    (∃ failure next,
      patternTupleTail nested opening (input.remainingCount + 1) elementsRev
        input = .reject failure next) :=
  patternTupleTail_ordinary_of_elementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate

theorem patternTupleTail_production_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    patternTupleTail nested opening (input.remainingCount + 1) elementsRev
      input ≠ .invariant error :=
  patternTupleTail_ne_invariant_of_elementFuel nested nestedFuel contract
    opening (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate error

/--
Parenthesized-pattern parsing is ordinary with one fuel unit beyond its nested
parser. The opening parenthesis spends that unit before the first nested call.
-/
theorem parenthesizedPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesizedPattern nested input = .ok value next) ∨
      (∃ failure next,
        parenthesizedPattern nested input = .reject failure next) := by
  unfold parenthesizedPattern
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .leftParen .pattern input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen .pattern input inputValid
      rw [openingResult] at openingValid
      have openingWindow := symbol_preservesTokenWindow .leftParen .pattern input
      rw [openingResult] at openingWindow
      have openingProgress : input.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .pattern
          (· == .symbol .leftParen) openingResult
      have afterOpeningAdequate :
          afterOpening.remainingCount < nestedFuel :=
        remainingCount_lt_after_strict_progress openingValid.2.1
          openingWindow.2 openingProgress adequate
      simp only
      split
      · exact closePatternTuple_invariantFreeOnValid opening [] afterOpening
          openingValid.2.1
      · cases nestedResult : nested afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening
              openingValid.2.1 afterOpeningAdequate error nestedResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok first next =>
            have firstValid := contract.validFor afterOpening openingValid.2.1
            rw [nestedResult] at firstValid
            have firstWindow := contract.preservesTokenWindow afterOpening
            rw [nestedResult] at firstWindow
            have firstProgress := contract.cursorLtOnSuccess nestedResult
            dsimp only
            split
            · omega
            · split
              · have nextAdequate :
                    next.remainingCount < nestedFuel + 1 := by
                  have preserved : next.remainingCount < nestedFuel :=
                    remainingCount_lt_of_cursor_le firstWindow.2
                      (Nat.le_of_lt firstProgress) afterOpeningAdequate
                  omega
                exact patternTupleTail_production_ordinary_of_elementFuel
                  nested nestedFuel contract opening [first] next
                    firstValid.2.1 nextAdequate
              · exact closePatternTuple_invariantFreeOnValid opening [first]
                  next firstValid.2.1

theorem parenthesizedPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    parenthesizedPattern nested input ≠ .invariant error := by
  intro failed
  rcases parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternCoreFuelTotalityProperties`
-/

/-! Fuel-aware totality for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/--
Every non-recovering pattern branch is ordinary when both recursive consumers
receive one unit beyond their fixed fuel bounds.
-/
theorem patternCore_ordinary_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, patternCore nested expression input = .ok pattern next) ∨
    (∃ failure next,
      patternCore nested expression input = .reject failure next) := by
  unfold patternCore
  split
  · exact wildcardPattern_ordinary input
  · split
    · exact literalPattern_ordinary input
    · split
      · exact booleanBinderPattern_ordinary input
      · split
        · exact parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel
            nestedContract input inputValid nestedAdequate
        · split
          · exact dotConstructorPattern_ordinary_of_elementFuel nested
              nestedFuel nestedContract input inputValid nestedAdequate
          · split
            · exact comptimePattern_ordinary_of_elementFuel expression
                expressionFuel expressionContract input inputValid
                expressionAdequate
            · split
              · exact qualifiedPattern_ordinary_of_elementFuel nested nestedFuel
                  nestedContract input inputValid nestedAdequate
              · exact Or.inr ⟨_, input, rfl⟩

theorem patternCore_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternCore nested expression input ≠ .invariant error := by
  intro failed
  rcases patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternCoreStrictProperties`
-/

/-! Strict cursor progress for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bind_cursor_lt_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

theorem wildcardPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : wildcardPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold wildcardPattern at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.symbol .underscore)
      .pattern (· == .symbol .underscore) result)
    (fun marker => Parser.pure_cursorMonotoneOnSuccess _)
    parsed

theorem literalPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : literalPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold literalPattern at parsed
  apply bind_cursor_lt_of_first coreLiteral_cursor_lt_onSuccess
    (fun literal => Parser.pure_cursorMonotoneOnSuccess _) parsed

theorem booleanBinderPattern_cursor_lt_onSuccess
    {input final : State} {value : Pattern}
    (parsed : booleanBinderPattern input = .ok value final) :
    input.cursor < final.cursor := by
  unfold booleanBinderPattern at parsed
  apply bind_cursor_lt_of_first booleanIdentifier_cursor_lt_onSuccess
    (fun name => Parser.pure_cursorMonotoneOnSuccess _) parsed

theorem parenthesizedPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : Pattern}
    (parsed : parenthesizedPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parenthesizedPattern at parsed
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingStrict := acceptToken_cursor_lt_onSuccess
        (.symbol .leftParen) .pattern (· == .symbol .leftParen) openingResult
      split at parsed
      · exact Nat.lt_of_lt_of_le openingStrict
          (closePatternTuple_cursorMonotoneOnSuccess opening []
            afterOpening value final parsed)
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
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (patternTupleTail_cursorMonotoneOnSuccess nested
                      nestedMonotone opening (next.remainingCount + 1)
                      [first] next value final parsed))
              · exact Nat.lt_of_lt_of_le openingStrict
                  (Nat.le_trans firstMonotone
                    (closePatternTuple_cursorMonotoneOnSuccess opening
                      [first] next value final parsed))

theorem dotConstructorPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    {input final : State} {value : Pattern}
    (parsed : dotConstructorPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold dotConstructorPattern at parsed
  cases dotResult : symbol .dot .pattern input with
  | reject failure rejected => simp [bind, dotResult] at parsed
  | invariant error => simp [bind, dotResult] at parsed
  | ok dot afterDot =>
      simp only [bind, dotResult] at parsed
      cases nameResult : patternName afterDot with
      | reject failure rejected => simp [nameResult] at parsed
      | invariant error => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          cases argumentsResult : optionalConstructorArguments nested afterName with
          | reject failure rejected => simp [argumentsResult] at parsed
          | invariant error => simp [argumentsResult] at parsed
          | ok arguments next =>
              simp only [argumentsResult, pure] at parsed
              have dotStrict := acceptToken_cursor_lt_onSuccess (.symbol .dot)
                .pattern (· == .symbol .dot) dotResult
              have rest := Nat.le_trans
                (patternName_cursorMonotoneOnSuccess afterDot name afterName
                  nameResult)
                (optionalConstructorArguments_cursorMonotoneOnSuccess nested
                  afterName arguments next argumentsResult)
              cases parsed
              exact Nat.lt_of_lt_of_le dotStrict rest

theorem comptimePattern_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : comptimePattern expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold comptimePattern at parsed
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at parsed
      | reject failure rejected => simp [expressionResult] at parsed
      | ok inner next =>
          simp only [expressionResult] at parsed
          have strict := acceptToken_cursor_lt_onSuccess
            (.contextual .comptime) .pattern (·.isContextual .comptime)
            markerResult
          have rest := expressionMonotone afterMarker inner next
            expressionResult
          cases parsed
          exact Nat.lt_of_lt_of_le strict rest

theorem qualifiedPattern_cursor_lt_onSuccess
    (nested : Parser Pattern)
    {input final : State} {value : Pattern}
    (parsed : qualifiedPattern nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold qualifiedPattern at parsed
  cases pathResult : qualifiedName .pattern .pattern input with
  | reject failure rejected => simp [bind, pathResult] at parsed
  | invariant error => simp [bind, pathResult] at parsed
  | ok path afterPath =>
      simp only [bind, pathResult] at parsed
      cases argumentsResult : optionalConstructorArguments nested afterPath with
      | reject failure rejected => simp [argumentsResult] at parsed
      | invariant error => simp [argumentsResult] at parsed
      | ok arguments next =>
          simp only [argumentsResult] at parsed
          let components := path.value.components.toList
          cases reversed : components.reverse with
          | nil => simp [components, reversed] at parsed
          | cons name qualifiersRev =>
              simp only [components, reversed] at parsed
              split at parsed <;> simp only [pure] at parsed
              all_goals
                have pathStrict := qualifiedName_cursor_lt_onSuccess .pattern
                  .pattern pathResult
                have rest := optionalConstructorArguments_cursorMonotoneOnSuccess
                  nested afterPath arguments next argumentsResult
                cases parsed
                exact Nat.lt_of_lt_of_le pathStrict rest

theorem patternCore_cursor_lt_onSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : patternCore nested expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold patternCore at parsed
  split at parsed
  · exact wildcardPattern_cursor_lt_onSuccess parsed
  · split at parsed
    · exact literalPattern_cursor_lt_onSuccess parsed
    · split at parsed
      · exact booleanBinderPattern_cursor_lt_onSuccess parsed
      · split at parsed
        · exact parenthesizedPattern_cursor_lt_onSuccess nested
            nestedMonotone parsed
        · split at parsed
          · exact dotConstructorPattern_cursor_lt_onSuccess nested parsed
          · split at parsed
            · exact comptimePattern_cursor_lt_onSuccess expression
                expressionMonotone parsed
            · split at parsed
              · exact qualifiedPattern_cursor_lt_onSuccess nested parsed
              · simp [rejectAt] at parsed

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternCoreFuelContractProperties`
-/

/-! A reusable fuel contract for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Existing branchwise syntax validity projects to the weak loop boundary. -/
theorem patternCore_weakValidFor
    (nested : Parser Pattern) (expression : Parser Expr)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (patternCore nested expression).ValidFor (fun _ _ => True) :=
  (patternCore_validFor nested expression expressionValid nestedValid
    nestedPreserves expressionValidFor spanValid expressionStarts).mono
      (fun _ _ _ => trivial)

/--
The smaller of the two one-step recursive budgets is the single generic fuel
accepted by `FuelElementTotalityContract`.
-/
theorem patternCore_fuelElementTotalityContract
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    FuelElementTotalityContract (patternCore nested expression)
      (Nat.min (nestedFuel + 1) (expressionFuel + 1)) := {
  validFor := patternCore_weakValidFor nested expression expressionValid
    nestedValid nestedContract.preservesTokenWindow.preservesTokensOnSuccess
    expressionValidFor spanValid expressionStarts
  preservesTokenWindow := patternCore_preservesTokenWindow nested expression
    nestedContract.preservesTokenWindow expressionContract.preservesTokenWindow
  cursorLtOnSuccess := patternCore_cursor_lt_onSuccess nested expression
    (fun input value next result =>
      Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
    (fun input value next result =>
      Nat.le_of_lt (expressionContract.cursorLtOnSuccess result))
  ordinary := by
    intro input inputValid adequate
    apply patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_left (nestedFuel + 1) (expressionFuel + 1))
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_right (nestedFuel + 1) (expressionFuel + 1))
}

end Solcore.Syntax.Parser.PatternInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.PatternLayerFuelTotalityProperties`
-/

/-! Fuel-aware totality for one recovering pattern layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem patternAdvance_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

namespace PatternInternals

theorem patternLayer_ordinary_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, patternLayer nested expression input = .ok pattern next) ∨
    (∃ failure next,
      patternLayer nested expression input = .reject failure next) := by
  rcases patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨pattern, next, by
      simp only [patternLayer, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isPatternBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [patternLayer, coreResult, rewound, boundary, ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [patternLayer, coreResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverPatternAux_production_exists_ok token.span token.span
              (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverPatternAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) = .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [patternLayer, coreResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem patternLayer_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternLayer nested expression input ≠ .invariant error := by
  intro failed
  rcases patternLayer_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem patternLayer_cursor_lt_onSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : patternLayer nested expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold patternLayer at parsed
  cases coreResult : patternCore nested expression input with
  | invariant error => simp [coreResult] at parsed
  | ok pattern next =>
      simp only [coreResult] at parsed
      cases parsed
      exact patternCore_cursor_lt_onSuccess nested expression nestedMonotone
        expressionMonotone coreResult
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound := { failedState with cursor := input.cursor }
      split at parsed
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            rw [advanced] at parsed
            contradiction
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            rw [advanced] at parsed
            have recoveryMonotone := recoverPatternAux_cursorMonotoneOnSuccess
              token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := patternAdvance_state_shape advanced
            have afterCursor : afterToken.cursor = input.cursor + 1 := by
              simp [shape, rewound]
            have emittedCursor :
                (afterToken.emit failure.toDiagnostic).cursor =
                  afterToken.cursor := rfl
            rw [emittedCursor, afterCursor] at recoveryMonotone
            omega

theorem patternLayer_fuelElementTotalityContract
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    FuelElementTotalityContract (patternLayer nested expression)
      (Nat.min (nestedFuel + 1) (expressionFuel + 1)) := {
  validFor := (patternLayer_validFor nested expression expressionValid
    nestedValid nestedContract.preservesTokenWindow expressionValidFor
    spanValid expressionStarts expressionContract.preservesTokenWindow).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := patternLayer_preservesTokenWindow nested expression
    nestedContract.preservesTokenWindow expressionContract.preservesTokenWindow
  cursorLtOnSuccess := patternLayer_cursor_lt_onSuccess nested expression
    (fun _ _ _ result => Nat.le_of_lt
      (nestedContract.cursorLtOnSuccess result))
    (fun _ _ _ result => Nat.le_of_lt
      (expressionContract.cursorLtOnSuccess result))
  ordinary := by
    intro state stateValid adequate
    apply patternLayer_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract state stateValid
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_left (nestedFuel + 1) (expressionFuel + 1))
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_right (nestedFuel + 1) (expressionFuel + 1))
}

end PatternInternals

end Solcore.Syntax.Parser
