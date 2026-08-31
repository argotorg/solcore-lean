import Solcore.Syntax.Parser.Statement.Simple
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.StatementValidity

/-! Contracts for nonrecursive canonical Core-statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace StatementSimpleInternals

private theorem simpleBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

private theorem advanceAfterValueAssignPeek_validFor {input : State}
    {token : Token} (valid : input.ValidFor)
    (found : input.peek? = some token) :
    token.span.ValidFor input.file ∧
      ({ input with cursor := input.cursor + 1 } : State).ValidFor ∧
      ({ input with cursor := input.cursor + 1 } : State).file = input.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Assignment-operator success consumes the current token exactly once. -/
theorem valueAssignOperator_ok_state_shape {input next : State}
    {operator : Located ValueAssignOp}
    (parsed : valueAssignOperator input = .ok operator next) :
    ∃ token, input.peek? = some token ∧ token.span = operator.span ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      unfold rejectAt at parsed
      contradiction
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          unfold rejectAt at parsed
          contradiction
      | some value =>
          simp only [accepted] at parsed
          cases parsed
          exact ⟨token, rfl, rfl, rfl⟩

/-- Assignment-operator success preserves source and state validity. -/
theorem valueAssignOperator_ok_validFor {input next : State}
    {operator : Located ValueAssignOp} (valid : input.ValidFor)
    (parsed : valueAssignOperator input = .ok operator next) :
    operator.span.ValidFor input.file ∧ next.ValidFor ∧
      next.file = input.file := by
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨token, found, span, rfl⟩
  have advanced := advanceAfterValueAssignPeek_validFor valid found
  exact ⟨by simpa [span] using advanced.1, advanced.2⟩

/-- Assignment-operator rejection leaves the parser state unchanged. -/
theorem valueAssignOperator_reject_state_shape {input next : State}
    {failure : Failure}
    (parsed : valueAssignOperator input = .reject failure next) :
    next = input := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      unfold rejectAt at parsed
      cases parsed
      rfl
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          unfold rejectAt at parsed
          cases parsed
          rfl
      | some value => simp [accepted] at parsed

/-- Assignment-operator rejection retains valid failure provenance. -/
theorem valueAssignOperator_reject_validFor {input next : State}
    {failure : Failure} (valid : input.ValidFor)
    (parsed : valueAssignOperator input = .reject failure next) :
    failure.span.ValidFor input.file ∧ next.ValidFor ∧
      next.file = input.file := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      exact rejectAt_reject_validFor valid _ _ parsed
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          exact rejectAt_reject_validFor valid _ _ parsed
      | some value => simp [accepted] at parsed

/-- Every ordinary assignment-operator result has valid provenance. -/
theorem valueAssignOperator_validFor :
    valueAssignOperator.ValidFor Located.ValidFor := by
  intro input valid
  cases parsed : valueAssignOperator input with
  | ok operator next =>
      exact valueAssignOperator_ok_validFor valid parsed
  | reject failure next =>
      exact valueAssignOperator_reject_validFor valid parsed
  | invariant error => trivial

/-- Assignment-operator parsing preserves the complete token window. -/
theorem valueAssignOperator_preservesTokenWindow :
    Parser.PreservesTokenWindow valueAssignOperator := by
  intro input
  cases parsed : valueAssignOperator input with
  | ok operator next =>
      rcases valueAssignOperator_ok_state_shape parsed with
        ⟨_token, _found, _span, rfl⟩
      exact ⟨rfl, rfl⟩
  | reject failure next =>
      rw [valueAssignOperator_reject_state_shape parsed]
      exact ⟨rfl, rfl⟩
  | invariant error => trivial

theorem valueAssignOperator_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess valueAssignOperator :=
  valueAssignOperator_preservesTokenWindow.preservesTokensOnSuccess

/-- Assignment-operator success advances by exactly one token. -/
theorem valueAssignOperator_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess valueAssignOperator := by
  intro input operator next parsed
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨_token, _found, _span, rfl⟩
  simp

/-- Assignment operators start at the current input token. -/
theorem valueAssignOperator_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess valueAssignOperator (·.span) := by
  intro input operator next parsed
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨token, found, span, _next⟩
  exact ⟨token, found, congrArg SourceSpan.startByte span⟩

namespace AssignmentTail

/-- Every source range retained by one assignment suffix is valid. -/
def ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : AssignmentTail → Prop
  | .value operator right =>
      operator.span.ValidFor file ∧ expressionValid file right
  | .bitNot operator => operator.ValidFor file

/-- The first source span consumed by an assignment suffix. -/
def startSpan : AssignmentTail → SourceSpan
  | .value operator _ => operator.span
  | .bitNot operator => operator

end AssignmentTail

/-- Assignment tails retain operator and nested-expression provenance. -/
theorem assignmentTail_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid) :
    (assignmentTail expression).ValidFor
      (AssignmentTail.ValidFor expressionValueValid) := by
  intro input inputValid
  unfold assignmentTail
  split
  · exact (Parser.bind_validFor_of_value
      (symbol_validFor .tildeEqual .statement) (by
        intro operator next nextValid operatorValid
        exact ⟨by simpa [AssignmentTail.ValidFor, Located.ValidFor] using
            operatorValid,
          nextValid, rfl⟩)) input inputValid
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        unfold rejectAt Reply.ValidFor
        exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
    | some selectedOperator =>
        have branch : (do
            let operator ← valueAssignOperator
            let right ← expression
            pure (AssignmentTail.value operator right)).ValidFor
            (AssignmentTail.ValidFor expressionValueValid) := by
          apply Parser.bind_validFor_of_value valueAssignOperator_validFor
          intro operator afterOperator afterOperatorValid operatorValid
          change ((expression >>= fun right =>
            pure (AssignmentTail.value operator right)) afterOperator
              ).ValidFor afterOperator _
          simp only [bind]
          have expressionReply := expressionValid afterOperator
            afterOperatorValid
          cases expressionResult : expression afterOperator with
          | ok right afterExpression =>
              rw [expressionResult] at expressionReply
              exact ⟨⟨by simpa only [Located.ValidFor] using operatorValid,
                expressionReply.1⟩, expressionReply.2.1,
                expressionReply.2.2⟩
          | reject failure rejected =>
              rw [expressionResult] at expressionReply
              exact ⟨expressionReply.1, expressionReply.2.1,
                expressionReply.2.2⟩
          | invariant error => trivial
        exact branch input inputValid

/-- Optional assignment tails retain provenance whenever present. -/
theorem optionalAssignmentTail_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid) :
    (optionalAssignmentTail expression).ValidFor
      (Option.ValidFor (AssignmentTail.ValidFor expressionValueValid)) := by
  intro input inputValid
  unfold optionalAssignmentTail
  split
  · exact (Parser.bind_validFor_of_value
      (assignmentTail_validFor expression expressionValueValid expressionValid)
      (by
        intro tail next nextValid tailValid
        exact ⟨by simpa only [Option.ValidFor] using tailValid,
          nextValid, rfl⟩)) input inputValid
  · exact ⟨trivial, inputValid, rfl⟩

/-- Assignment tails start at their written assignment operator. -/
theorem assignmentTail_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess (assignmentTail expression)
      AssignmentTail.startSpan := by
  intro input tail final parsed
  unfold assignmentTail at parsed
  split at parsed
  · rcases simpleBind_ok_components parsed with
      ⟨operator, afterOperator, operatorResult, finished⟩
    have starts := symbol_startsAtCurrentTokenOnSuccess
      .tildeEqual .statement input operator afterOperator operatorResult
    cases finished
    exact starts
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        simp only [selected] at parsed
        unfold rejectAt at parsed
        contradiction
    | some selectedOperator =>
        simp only [selected] at parsed
        rcases simpleBind_ok_components parsed with
          ⟨operator, afterOperator, operatorResult, rest⟩
        rcases simpleBind_ok_components rest with
          ⟨right, afterRight, _rightResult, finished⟩
        have starts := valueAssignOperator_startsAtCurrentTokenOnSuccess
          input operator afterOperator operatorResult
        cases finished
        exact starts

/-- Every successful assignment tail consumes its operator token. -/
theorem assignmentTail_cursor_lt_onSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {tail : AssignmentTail}
    (parsed : assignmentTail expression input = .ok tail final) :
    input.cursor < final.cursor := by
  unfold assignmentTail at parsed
  split at parsed
  · rcases simpleBind_ok_components parsed with
      ⟨operator, afterOperator, operatorResult, finished⟩
    have strict : input.cursor < afterOperator.cursor := by
      rw [(symbol_ok_state_shape .tildeEqual .statement operatorResult).2]
      simp
    cases finished
    exact strict
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        simp only [selected] at parsed
        unfold rejectAt at parsed
        contradiction
    | some selectedOperator =>
        simp only [selected] at parsed
        rcases simpleBind_ok_components parsed with
          ⟨operator, afterOperator, operatorResult, rest⟩
        rcases simpleBind_ok_components rest with
          ⟨right, afterRight, rightResult, finished⟩
        have strict : input.cursor < afterOperator.cursor := by
          rw [(valueAssignOperator_ok_state_shape
            operatorResult).choose_spec.2.2]
          simp
        have rightMonotone := expressionCursor afterOperator right
          afterRight rightResult
        cases finished
        exact Nat.lt_of_lt_of_le strict rightMonotone

/-- An assignment operator starts no later than its retained endpoint. -/
theorem assignmentTail_start_le_endOnSuccess
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span))
    {input final : State} {tail : AssignmentTail}
    (inputValid : input.ValidFor)
    (parsed : assignmentTail expression input = .ok tail final) :
    tail.startSpan.startByte ≤ (assignmentEnd tail).endByte := by
  unfold assignmentTail at parsed
  split at parsed
  · rcases simpleBind_ok_components parsed with
      ⟨operator, afterOperator, operatorResult, finished⟩
    have operatorContract := symbol_validFor .tildeEqual .statement input
      inputValid
    rw [operatorResult] at operatorContract
    cases finished
    exact operatorContract.1.2.1
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        simp only [selected] at parsed
        unfold rejectAt at parsed
        contradiction
    | some selectedOperator =>
        simp only [selected] at parsed
        rcases simpleBind_ok_components parsed with
          ⟨operator, afterOperator, operatorResult, rest⟩
        rcases simpleBind_ok_components rest with
          ⟨right, afterRight, rightResult, finished⟩
        have operatorContract := valueAssignOperator_validFor input inputValid
        rw [operatorResult] at operatorContract
        have rightContract := expressionValid afterOperator
          operatorContract.2.1
        rw [rightResult] at rightContract
        have rightSpanValid : right.span.ValidFor input.file := by
          simpa [operatorContract.2.2] using
            expressionSpan afterOperator.file right rightContract.1
        rcases valueAssignOperator_ok_state_shape operatorResult with
          ⟨operatorToken, operatorFound, operatorSpan, afterOperatorEq⟩
        have advanced : input.advance? =
            some (operatorToken, afterOperator) := by
          unfold State.advance?
          rw [operatorFound, afterOperatorEq]
          rfl
        rcases expressionStarts afterOperator right afterRight rightResult with
          ⟨rightToken, rightFound, rightStart⟩
        have separated := inputValid.consumed_end_le_peek_start_after_advance
          advanced rightFound
        cases finished
        exact Nat.le_trans operatorContract.1.2.1
          (Nat.le_trans (by simpa [operatorSpan, rightStart] using separated)
            rightSpanValid.2.1)

/-- A present optional tail exposes the operator at the caller's cursor. -/
theorem optionalAssignmentTail_some_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) {input final : State}
    {tail : AssignmentTail}
    (parsed : optionalAssignmentTail expression input =
      .ok (some tail) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = tail.startSpan.startByte := by
  unfold optionalAssignmentTail at parsed
  split at parsed
  · rcases simpleBind_ok_components parsed with
      ⟨parsedTail, afterTail, tailResult, finished⟩
    have starts := assignmentTail_startsAtCurrentTokenOnSuccess expression
      input parsedTail afterTail tailResult
    cases finished
    exact starts
  · cases parsed

/-- A valid assignment tail has a valid final endpoint span. -/
theorem assignmentEnd_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    {file : SourceFile} {tail : AssignmentTail}
    (valid : tail.ValidFor expressionValueValid file) :
    (assignmentEnd tail).ValidFor file := by
  cases tail with
  | value operator right => exact expressionSpan file right valid.2
  | bitNot operator => exact valid

/-- The selected statement endpoint is valid in every priority branch. -/
theorem statementEnd_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    {file : SourceFile} {left : Expr} {tail : Option AssignmentTail}
    {semicolon : Option SourceSpan}
    (leftValid : expressionValueValid file left)
    (tailValid : Option.ValidFor
      (AssignmentTail.ValidFor expressionValueValid) file tail)
    (semicolonValid : Option.ValidFor
      (fun source span => span.ValidFor source) file semicolon) :
    (statementEnd left tail semicolon).ValidFor file := by
  cases semicolon with
  | some marker => simpa [Option.ValidFor, statementEnd] using semicolonValid
  | none =>
      cases tail with
      | some value =>
          exact assignmentEnd_validFor expressionValueValid expressionSpan
            (by simpa [Option.ValidFor] using tailValid)
      | none => exact expressionSpan file left leftValid

/-- Assignment tails preserve token windows when nested expressions do. -/
theorem assignmentTail_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (assignmentTail expression) := by
  intro input
  unfold assignmentTail
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .tildeEqual .statement)
    intro operator
    exact Parser.pure_preservesTokenWindow _
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none => exact rejectAt_preservesTokenWindow input _ _
    | some operator =>
        apply Parser.bind_preservesTokenWindow
          valueAssignOperator_preservesTokenWindow
        intro parsedOperator
        apply Parser.bind_preservesTokenWindow expressionWindow
        intro right
        exact Parser.pure_preservesTokenWindow _

theorem assignmentTail_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (assignmentTail expression) :=
  (assignmentTail_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Assignment tails never rewind when nested expressions are monotone. -/
theorem assignmentTail_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (assignmentTail expression) := by
  intro input tail next parsed
  unfold assignmentTail at parsed
  split at parsed
  · exact (Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .tildeEqual .statement)
      (fun operator => Parser.pure_cursorMonotoneOnSuccess _))
        input tail next parsed
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        simp only [selected] at parsed
        unfold rejectAt at parsed
        contradiction
    | some operator =>
        simp only [selected] at parsed
        exact (Parser.bind_cursorMonotoneOnSuccess
          valueAssignOperator_cursorMonotoneOnSuccess
          (fun parsedOperator => Parser.bind_cursorMonotoneOnSuccess
            expressionCursor
            (fun right => Parser.pure_cursorMonotoneOnSuccess _)))
              input tail next parsed

/-- Optional assignment tails retain complete ordinary token windows. -/
theorem optionalAssignmentTail_preservesTokenWindow
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (optionalAssignmentTail expression) := by
  intro input
  unfold optionalAssignmentTail
  split
  · apply Parser.bind_preservesTokenWindow
      (assignmentTail_preservesTokenWindow expression expressionWindow)
    intro tail
    exact Parser.pure_preservesTokenWindow _
  · exact ⟨rfl, rfl⟩

theorem optionalAssignmentTail_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (optionalAssignmentTail expression) :=
  (optionalAssignmentTail_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Optional assignment tails preserve nested cursor monotonicity. -/
theorem optionalAssignmentTail_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (optionalAssignmentTail expression) := by
  intro input tail next parsed
  unfold optionalAssignmentTail at parsed
  split at parsed
  · exact (Parser.bind_cursorMonotoneOnSuccess
      (assignmentTail_cursorMonotoneOnSuccess expression expressionCursor)
      (fun value => Parser.pure_cursorMonotoneOnSuccess _))
        input tail next parsed
  · cases parsed
    exact Nat.le_refl _

/-- Optional semicolons retain valid marker provenance when present. -/
theorem optionalSemicolon_validFor :
    optionalSemicolon.ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold optionalSemicolon
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .semicolon
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (symbol_validFor .semicolon .statement)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional semicolons preserve every ordinary token window. -/
theorem optionalSemicolon_preservesTokenWindow :
    Parser.PreservesTokenWindow optionalSemicolon := by
  unfold optionalSemicolon
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .semicolon
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .semicolon .statement)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalSemicolon_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess optionalSemicolon :=
  optionalSemicolon_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional semicolon parsing never rewinds the token cursor. -/
theorem optionalSemicolon_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess optionalSemicolon := by
  unfold optionalSemicolon
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .semicolon
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .semicolon .statement)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present optional semicolon starts at the current semicolon token. -/
theorem optionalSemicolon_some_startsAtCurrentTokenOnSuccess
    {input final : State} {span : SourceSpan}
    (parsed : optionalSemicolon input = .ok (some span) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = span.startByte := by
  unfold optionalSemicolon getState at parsed
  simp only [bind] at parsed
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at parsed
    change (do
      let marker ← symbol .semicolon .statement
      pure (some marker.span)) input = .ok (some span) final at parsed
    simp only [bind] at parsed
    cases markerResult : symbol .semicolon .statement input with
    | ok marker next =>
        simp only [markerResult] at parsed
        change Reply.ok (some marker.span) next =
          Reply.ok (some span) final at parsed
        have starts := symbol_startsAtCurrentTokenOnSuccess
          .semicolon .statement input marker next markerResult
        cases parsed
        exact starts
    | reject failure rejected => simp [markerResult] at parsed
    | invariant error => simp [markerResult] at parsed
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some span) final at parsed
    cases parsed

/-- Optional return values retain nested expression provenance when present. -/
theorem optionalReturnValue_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid) :
    (optionalReturnValue expression).ValidFor
      (Option.ValidFor expressionValueValid) := by
  unfold optionalReturnValue
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases empty : isSymbol observed .semicolon
  · simp only [empty, if_true]
    exact Parser.pure_validFor none _ (fun _ => trivial)
  · simp only [empty]
    apply Parser.bind_validFor_of_value expressionValid
    intro value input inputValid valueValid
    exact ⟨by simpa only [Option.ValidFor] using valueValid,
      inputValid, rfl⟩

/-- Optional return values preserve every ordinary token window. -/
theorem optionalReturnValue_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (optionalReturnValue expression) := by
  unfold optionalReturnValue
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases empty : isSymbol observed .semicolon
  · simp only [empty, if_true]
    exact Parser.pure_preservesTokenWindow none
  · simp only [empty]
    apply Parser.bind_preservesTokenWindow expressionWindow
    intro value
    exact Parser.pure_preservesTokenWindow _

theorem optionalReturnValue_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (optionalReturnValue expression) :=
  (optionalReturnValue_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Optional return-value parsing never rewinds the token cursor. -/
theorem optionalReturnValue_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (optionalReturnValue expression) := by
  unfold optionalReturnValue
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases empty : isSymbol observed .semicolon
  · simp only [empty, if_true]
    exact Parser.pure_cursorMonotoneOnSuccess none
  · simp only [empty]
    apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
    intro value
    exact Parser.pure_cursorMonotoneOnSuccess _

end StatementSimpleInternals

/-- Assignment/expression statements preserve nested expression windows. -/
theorem assignmentOrExpressionStatement_preservesTokenWindow
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow
      (assignmentOrExpressionStatement expression) := by
  unfold assignmentOrExpressionStatement
  apply Parser.bind_preservesTokenWindow expressionWindow
  intro left
  apply Parser.bind_preservesTokenWindow
    (StatementSimpleInternals.optionalAssignmentTail_preservesTokenWindow
      expression expressionWindow)
  intro tail
  apply Parser.bind_preservesTokenWindow
    StatementSimpleInternals.optionalSemicolon_preservesTokenWindow
  intro semicolon
  dsimp only
  cases tail with
  | none => exact Parser.pure_preservesTokenWindow _
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            apply Parser.bind_preservesTokenWindow
              (emitDiagnostic_preservesTokenWindow _)
            intro _
            exact Parser.pure_preservesTokenWindow _
          · simp only [missing]
            exact Parser.pure_preservesTokenWindow _
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            apply Parser.bind_preservesTokenWindow
              (emitDiagnostic_preservesTokenWindow _)
            intro _
            exact Parser.pure_preservesTokenWindow _
          · simp only [missing]
            exact Parser.pure_preservesTokenWindow _

theorem assignmentOrExpressionStatement_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess
      (assignmentOrExpressionStatement expression) :=
  (assignmentOrExpressionStatement_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Assignment/expression statements inherit expression cursor monotonicity. -/
theorem assignmentOrExpressionStatement_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess
      (assignmentOrExpressionStatement expression) := by
  unfold assignmentOrExpressionStatement
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
      expression expressionCursor)
  intro tail
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalSemicolon_cursorMonotoneOnSuccess
  intro semicolon
  dsimp only
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            apply Parser.bind_cursorMonotoneOnSuccess
              (emitDiagnostic_cursorMonotoneOnSuccess _)
            intro _
            exact Parser.pure_cursorMonotoneOnSuccess _
          · simp only [missing]
            exact Parser.pure_cursorMonotoneOnSuccess _
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            apply Parser.bind_cursorMonotoneOnSuccess
              (emitDiagnostic_cursorMonotoneOnSuccess _)
            intro _
            exact Parser.pure_cursorMonotoneOnSuccess _
          · simp only [missing]
            exact Parser.pure_cursorMonotoneOnSuccess _

/-- Assignment/expression statements start where their left expression does. -/
theorem assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (assignmentOrExpressionStatement expression) (·.span) := by
  unfold assignmentOrExpressionStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first expressionStarts
  intro left input statement final parsed
  rcases StatementSimpleInternals.simpleBind_ok_components parsed with
    ⟨tail, afterTail, _tailResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, _semicolonResult, finished⟩
  dsimp only at finished
  cases tail with
  | none =>
      cases finished
      rfl
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished
              with ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            rfl
          · simp only [missing] at finished
            cases finished
            rfl
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished
              with ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            rfl
          · simp only [missing] at finished
            cases finished
            rfl

/-- A successful assignment/expression statement has a source-valid outer span. -/
theorem assignmentOrExpressionStatement_span_validFor_onSuccess
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span))
    {input final : State} {statement : Statement}
    (inputValid : input.ValidFor)
    (parsed : assignmentOrExpressionStatement expression input =
      .ok statement final) :
    statement.span.ValidFor input.file := by
  have stages := parsed
  unfold assignmentOrExpressionStatement at stages
  rcases StatementSimpleInternals.simpleBind_ok_components stages with
    ⟨left, afterLeft, leftResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨tail, afterTail, tailResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have leftContract := expressionValid input inputValid
  rw [leftResult] at leftContract
  have tailContract := StatementSimpleInternals.optionalAssignmentTail_validFor
    expression expressionValueValid expressionValid afterLeft leftContract.2.1
  rw [tailResult] at tailContract
  have semicolonContract := StatementSimpleInternals.optionalSemicolon_validFor
    afterTail tailContract.2.1
  rw [semicolonResult] at semicolonContract
  have leftSpanValid : left.span.ValidFor input.file :=
    expressionSpan input.file left leftContract.1
  have tailValid : Option.ValidFor
      (StatementSimpleInternals.AssignmentTail.ValidFor expressionValueValid)
      input.file tail := by
    simpa [leftContract.2.2] using tailContract.1
  have semicolonValid : Option.ValidFor
      (fun file span => span.ValidFor file) input.file semicolon := by
    simpa [tailContract.2.2, leftContract.2.2] using semicolonContract.1
  have endpointValid := StatementSimpleInternals.statementEnd_validFor
    expressionValueValid expressionSpan leftContract.1 tailValid semicolonValid
  rcases expressionStarts input left afterLeft leftResult with
    ⟨firstToken, firstFound, firstStart⟩
  have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have firstSpanValid := inputValid.peek?_span_validFor firstFound
  have afterLeftWindow := expressionWindow input
  rw [leftResult] at afterLeftWindow
  have leftStartBefore {later : State} {laterToken : Token}
      {targetStart : Nat} (tokens : later.tokens = input.tokens)
      (cursor : input.cursor < later.cursor)
      (found : later.peek? = some laterToken)
      (target : laterToken.span.startByte = targetStart) :
      left.span.startByte ≤ targetStart := by
    have laterAt : input.tokens[later.cursor]? = some laterToken := by
      simpa [tokens] using State.getElem?_eq_some_of_peek?_eq_some found
    have separated := inputValid.token_end_le_token_start_of_getElem?_lt
      firstAt laterAt cursor
    exact Nat.le_trans (by simpa [firstStart] using firstSpanValid.2.1)
      (by simpa [target] using separated)
  have ordered : left.span.startByte ≤
      (StatementSimpleInternals.statementEnd left tail semicolon).endByte := by
    cases semicolon with
    | some marker =>
        rcases StatementSimpleInternals.optionalSemicolon_some_startsAtCurrentTokenOnSuccess
          semicolonResult with ⟨markerToken, markerFound, markerStart⟩
        have tailWindow :=
          StatementSimpleInternals.optionalAssignmentTail_preservesTokenWindow
            expression expressionWindow afterLeft
        rw [tailResult] at tailWindow
        have tokens : afterTail.tokens = input.tokens :=
          tailWindow.1.trans afterLeftWindow.1
        have cursor : input.cursor < afterTail.cursor :=
          Nat.lt_of_lt_of_le (expressionCursorLt leftResult)
            (StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
              expression
              (fun before value after result =>
                Nat.le_of_lt (expressionCursorLt result))
              afterLeft tail afterTail tailResult)
        have beforeMarker := leftStartBefore tokens cursor markerFound markerStart
        simpa [StatementSimpleInternals.statementEnd] using
          Nat.le_trans beforeMarker endpointValid.2.1
    | none =>
        cases tail with
        | none =>
            simpa [StatementSimpleInternals.statementEnd] using leftSpanValid.2.1
        | some assignment =>
            rcases StatementSimpleInternals.optionalAssignmentTail_some_startsAtCurrentTokenOnSuccess
              expression tailResult with ⟨operatorToken, operatorFound, operatorStart⟩
            have beforeOperator := leftStartBefore afterLeftWindow.1
              (expressionCursorLt leftResult) operatorFound operatorStart
            have assignmentResult :
                StatementSimpleInternals.assignmentTail expression afterLeft =
                  .ok assignment afterTail := by
              unfold StatementSimpleInternals.optionalAssignmentTail at tailResult
              split at tailResult
              · rcases StatementSimpleInternals.simpleBind_ok_components tailResult with
                  ⟨parsedTail, next, parsedTailResult, completed⟩
                cases completed
                exact parsedTailResult
              · cases tailResult
            have assignmentOrdered :=
              StatementSimpleInternals.assignmentTail_start_le_endOnSuccess
                expression expressionValueValid expressionValid expressionSpan
                expressionStarts leftContract.2.1 assignmentResult
            simpa [StatementSimpleInternals.statementEnd] using
              Nat.le_trans beforeOperator assignmentOrdered
  have outerValid := SourceSpan.cover_validFor leftSpanValid endpointValid ordered
  dsimp only at finished
  cases tail with
  | none =>
      cases finished
      exact outerValid
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished with
              ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            exact outerValid
          · simp only [missing] at finished
            cases finished
            exact outerValid
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished with
              ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            exact outerValid
          · simp only [missing] at finished
            cases finished
            exact outerValid

/-- A successful assignment/expression statement retains all nested provenance. -/
theorem assignmentOrExpressionStatement_value_validFor_onSuccess
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span))
    {input final : State} {statement : Statement}
    (inputValid : input.ValidFor)
    (parsed : assignmentOrExpressionStatement expression input =
      .ok statement final) :
    Statement.ValidFor expressionValueValid patternValueValid yulValueValid
      input.file statement := by
  have outerValid := assignmentOrExpressionStatement_span_validFor_onSuccess
    expression expressionValueValid expressionValid expressionSpan
    expressionWindow expressionCursorLt expressionStarts inputValid parsed
  have stages := parsed
  unfold assignmentOrExpressionStatement at stages
  rcases StatementSimpleInternals.simpleBind_ok_components stages with
    ⟨left, afterLeft, leftResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨tail, afterTail, tailResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, _semicolonResult, finished⟩
  have leftContract := expressionValid input inputValid
  rw [leftResult] at leftContract
  have tailContract := StatementSimpleInternals.optionalAssignmentTail_validFor
    expression expressionValueValid expressionValid afterLeft leftContract.2.1
  rw [tailResult] at tailContract
  have tailValid : Option.ValidFor
      (StatementSimpleInternals.AssignmentTail.ValidFor expressionValueValid)
      input.file tail := by
    simpa [leftContract.2.2] using tailContract.1
  dsimp only at finished
  cases tail with
  | none =>
      cases finished
      exact Statement.ValidFor.expression outerValid leftContract.1
  | some tail =>
      cases tail with
      | value operator right =>
          have retained : operator.span.ValidFor input.file ∧
              expressionValueValid input.file right := by
            simpa [Option.ValidFor,
              StatementSimpleInternals.AssignmentTail.ValidFor] using tailValid
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished with
              ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            exact Statement.ValidFor.assignValue outerValid leftContract.1
              retained.1 retained.2
          · simp only [missing] at finished
            cases finished
            exact Statement.ValidFor.assignValue outerValid leftContract.1
              retained.1 retained.2
      | bitNot operator =>
          have retained : operator.ValidFor input.file := by
            simpa [Option.ValidFor,
              StatementSimpleInternals.AssignmentTail.ValidFor] using tailValid
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true] at finished
            rcases StatementSimpleInternals.simpleBind_ok_components finished with
              ⟨_, afterDiagnostic, _diagnosticResult, completed⟩
            cases completed
            exact Statement.ValidFor.assignBitNot outerValid leftContract.1
              retained
          · simp only [missing] at finished
            cases finished
            exact Statement.ValidFor.assignBitNot outerValid leftContract.1
              retained

/-- Assignment/expression parsing preserves state and source validity on every
ordinary result, while successful values retain all nested provenance. -/
theorem assignmentOrExpressionStatement_validFor
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (assignmentOrExpressionStatement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  apply Parser.validFor_of_ok_reject _ _
  · intro input inputValid statement final parsed
    have statementValid :=
      assignmentOrExpressionStatement_value_validFor_onSuccess expression
        expressionValueValid patternValueValid yulValueValid expressionValid
        expressionSpan expressionWindow expressionCursorLt expressionStarts
        inputValid parsed
    have stages := parsed
    unfold assignmentOrExpressionStatement at stages
    rcases StatementSimpleInternals.simpleBind_ok_components stages with
      ⟨left, afterLeft, leftResult, rest⟩
    rcases StatementSimpleInternals.simpleBind_ok_components rest with
      ⟨tail, afterTail, tailResult, rest⟩
    rcases StatementSimpleInternals.simpleBind_ok_components rest with
      ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
    have leftContract := expressionValid input inputValid
    rw [leftResult] at leftContract
    have tailContract :=
      StatementSimpleInternals.optionalAssignmentTail_validFor expression
        expressionValueValid expressionValid afterLeft leftContract.2.1
    rw [tailResult] at tailContract
    have semicolonContract :=
      StatementSimpleInternals.optionalSemicolon_validFor afterTail
        tailContract.2.1
    rw [semicolonResult] at semicolonContract
    have statementValidAfter : Statement.ValidFor expressionValueValid
        patternValueValid yulValueValid afterSemicolon.file statement := by
      simpa [semicolonContract.2.2, tailContract.2.2,
        leftContract.2.2] using statementValid
    have finalContract : final.ValidFor ∧
        final.file = afterSemicolon.file := by
      dsimp only at finished
      cases tail with
      | none =>
          cases finished
          exact ⟨semicolonContract.2.1, rfl⟩
      | some tail =>
          cases tail with
          | value operator right =>
              by_cases missing : semicolon.isNone
              · simp only [missing, if_true] at finished
                unfold emitDiagnostic modifyState at finished
                simp only [bind] at finished
                cases finished
                exact ⟨semicolonContract.2.1.emit_validFor _
                  statementValidAfter.span_valid, rfl⟩
              · simp only [missing] at finished
                cases finished
                exact ⟨semicolonContract.2.1, rfl⟩
          | bitNot operator =>
              by_cases missing : semicolon.isNone
              · simp only [missing, if_true] at finished
                unfold emitDiagnostic modifyState at finished
                simp only [bind] at finished
                cases finished
                exact ⟨semicolonContract.2.1.emit_validFor _
                  statementValidAfter.span_valid, rfl⟩
              · simp only [missing] at finished
                cases finished
                exact ⟨semicolonContract.2.1, rfl⟩
    exact ⟨statementValid, finalContract.1,
      finalContract.2.trans (semicolonContract.2.2.trans
        (tailContract.2.2.trans leftContract.2.2))⟩
  · intro input inputValid failure final parsed
    unfold assignmentOrExpressionStatement at parsed
    simp only [bind] at parsed
    cases leftResult : expression input with
    | invariant error => simp [leftResult] at parsed
    | reject leftFailure afterLeft =>
        simp only [leftResult] at parsed
        cases parsed
        have contract := expressionValid input inputValid
        rw [leftResult] at contract
        exact contract
    | ok left afterLeft =>
        simp only [leftResult] at parsed
        have leftContract := expressionValid input inputValid
        rw [leftResult] at leftContract
        cases tailResult :
            StatementSimpleInternals.optionalAssignmentTail expression
              afterLeft with
        | invariant error => simp [tailResult] at parsed
        | reject tailFailure afterTail =>
            simp only [tailResult] at parsed
            cases parsed
            have contract :=
              StatementSimpleInternals.optionalAssignmentTail_validFor
                expression expressionValueValid expressionValid afterLeft
                leftContract.2.1
            rw [tailResult] at contract
            exact contract.of_file_eq leftContract.2.2
        | ok tail afterTail =>
            simp only [tailResult] at parsed
            have tailContract :=
              StatementSimpleInternals.optionalAssignmentTail_validFor
                expression expressionValueValid expressionValid afterLeft
                leftContract.2.1
            rw [tailResult] at tailContract
            cases semicolonResult :
                StatementSimpleInternals.optionalSemicolon afterTail with
            | invariant error => simp [semicolonResult] at parsed
            | reject semicolonFailure afterSemicolon =>
                simp only [semicolonResult] at parsed
                cases parsed
                have contract :=
                  StatementSimpleInternals.optionalSemicolon_validFor afterTail
                    tailContract.2.1
                rw [semicolonResult] at contract
                exact contract.of_file_eq
                  (tailContract.2.2.trans leftContract.2.2)
            | ok semicolon afterSemicolon =>
                simp only [semicolonResult] at parsed
                cases tail with
                | none => contradiction
                | some tail =>
                    cases tail with
                    | value operator right =>
                        by_cases missing : semicolon.isNone
                        · simp [missing, emitDiagnostic, modifyState] at parsed
                        · simp [missing] at parsed
                    | bitNot operator =>
                        by_cases missing : semicolon.isNone
                        · simp [missing, emitDiagnostic, modifyState] at parsed
                        · simp [missing] at parsed

end Solcore.Syntax.Parser
