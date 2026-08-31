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

/-- Optional `let` types retain their colon-following type provenance. -/
theorem optionalLetType_validFor :
    optionalLetType.ValidFor (Option.ValidFor TypeExpr.ValidFor) := by
  unfold optionalLetType
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .colon
  · simp only [present, if_true]
    apply Parser.bind_validFor (symbol_validFor .colon .statement)
    intro colon
    apply Parser.bind_validFor_of_value typeExpr_validFor
    intro type input inputValid typeValid
    exact ⟨by simpa only [Option.ValidFor] using typeValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional `let` types preserve every ordinary token window. -/
theorem optionalLetType_preservesTokenWindow :
    Parser.PreservesTokenWindow optionalLetType := by
  unfold optionalLetType
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .colon
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colon .statement)
    intro colon
    apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
    intro type
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalLetType_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess optionalLetType :=
  optionalLetType_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional `let` type parsing never rewinds the token cursor. -/
theorem optionalLetType_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess optionalLetType := by
  unfold optionalLetType
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .colon
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .colon .statement)
    intro colon
    apply Parser.bind_cursorMonotoneOnSuccess typeExpr_cursorMonotoneOnSuccess
    intro type
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- Optional `let` initializers retain nested expression provenance. -/
theorem optionalLetInitializer_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid) :
    (optionalLetInitializer expression).ValidFor
      (Option.ValidFor expressionValueValid) := by
  unfold optionalLetInitializer
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_validFor (symbol_validFor .equal .statement)
    intro equal
    apply Parser.bind_validFor_of_value expressionValid
    intro value input inputValid valueValid
    exact ⟨by simpa only [Option.ValidFor] using valueValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional `let` initializers preserve every ordinary token window. -/
theorem optionalLetInitializer_preservesTokenWindow
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (optionalLetInitializer expression) := by
  unfold optionalLetInitializer
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .equal .statement)
    intro equal
    apply Parser.bind_preservesTokenWindow expressionWindow
    intro value
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalLetInitializer_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (optionalLetInitializer expression) :=
  (optionalLetInitializer_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Optional `let` initializer parsing never rewinds the token cursor. -/
theorem optionalLetInitializer_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (optionalLetInitializer expression) := by
  unfold optionalLetInitializer
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .equal .statement)
    intro equal
    apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
    intro value
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present optional type exposes the first token after its colon. -/
theorem optionalLetType_some_startsAfterColon {input final : State}
    {type : TypeExpr}
    (parsed : optionalLetType input = .ok (some type) final) :
    ∃ colon afterColon first,
      symbol .colon .statement input = .ok colon afterColon ∧
      afterColon.peek? = some first ∧
      first.span.startByte = type.span.startByte := by
  unfold optionalLetType getState at parsed
  simp only [bind] at parsed
  by_cases present : isSymbol input .colon
  · simp only [present, if_true] at parsed
    rcases simpleBind_ok_components parsed with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases simpleBind_ok_components rest with
      ⟨parsedType, afterType, typeResult, finished⟩
    have typeEq : parsedType = type := by cases finished; rfl
    subst parsedType
    rcases typeExpr_startsAtCurrentTokenOnSuccess
        afterColon type afterType typeResult with
      ⟨first, firstFound, firstStart⟩
    exact ⟨colon, afterColon, first, colonResult, firstFound, firstStart⟩
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some type) final at parsed
    cases parsed

/-- A present initializer exposes the expression token after its equals sign. -/
theorem optionalLetInitializer_some_startsAfterEqual
    (expression : Parser Expr)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span))
    {input final : State} {value : Expr}
    (parsed : optionalLetInitializer expression input =
      .ok (some value) final) :
    ∃ equal afterEqual first,
      symbol .equal .statement input = .ok equal afterEqual ∧
      afterEqual.peek? = some first ∧
      first.span.startByte = value.span.startByte := by
  unfold optionalLetInitializer getState at parsed
  simp only [bind] at parsed
  by_cases present : isSymbol input .equal
  · simp only [present, if_true] at parsed
    rcases simpleBind_ok_components parsed with
      ⟨equal, afterEqual, equalResult, rest⟩
    rcases simpleBind_ok_components rest with
      ⟨parsedValue, afterValue, valueResult, finished⟩
    have valueEq : parsedValue = value := by cases finished; rfl
    subst parsedValue
    rcases expressionStarts afterEqual value afterValue valueResult with
      ⟨first, firstFound, firstStart⟩
    exact ⟨equal, afterEqual, first, equalResult, firstFound, firstStart⟩
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some value) final at parsed
    cases parsed

/-- For-header let items preserve nested expression token windows. -/
theorem forLetItem_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (forLetItem expression) := by
  unfold forLetItem
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .letKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .statement)
  intro name
  apply Parser.bind_preservesTokenWindow optionalLetType_preservesTokenWindow
  intro type
  apply Parser.bind_preservesTokenWindow
    (optionalLetInitializer_preservesTokenWindow expression expressionWindow)
  intro initializer
  exact Parser.pure_preservesTokenWindow _

theorem forLetItem_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (forLetItem expression) :=
  (forLetItem_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- For-header let items never rewind the token cursor. -/
theorem forLetItem_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (forLetItem expression) := by
  unfold forLetItem
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .letKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalLetType_cursorMonotoneOnSuccess
  intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalLetInitializer_cursorMonotoneOnSuccess expression
      expressionCursor)
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A for-header let item starts at its leading `let` keyword. -/
theorem forLetItem_startsAtCurrentTokenOnSuccess (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (forLetItem expression) (·.span) := by
  unfold forLetItem
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw))
  intro marker input item final parsed
  rcases simpleBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases simpleBind_ok_components rest with
    ⟨type, afterType, _typeResult, rest⟩
  rcases simpleBind_ok_components rest with
    ⟨initializer, afterInitializer, _initializerResult, finished⟩
  cases finished
  rfl

/-- The selected for-let endpoint retains valid source provenance. -/
theorem forLetEnd_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    {file : SourceFile} {name : Identifier} {type : Option TypeExpr}
    {initializer : Option Expr} (nameValid : name.span.ValidFor file)
    (typeValid : Option.ValidFor TypeExpr.ValidFor file type)
    (initializerValid : Option.ValidFor expressionValueValid file initializer) :
    (forLetEnd name type initializer).ValidFor file := by
  cases initializer with
  | some value =>
      exact expressionSpan file value
        (by simpa only [Option.ValidFor] using initializerValid)
  | none =>
      cases type with
      | some value =>
          exact TypeExpr.ValidFor.span_valid
            (by simpa only [Option.ValidFor] using typeValid)
      | none => exact nameValid

/-- For-header let items retain name, type, initializer, and outer ranges. -/
theorem forLetItem_validFor
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (forLetItem expression).ValidFor
      (ForItem.ValidFor expressionValueValid) := by
  have weak : (forLetItem expression).ValidFor (fun _ _ => True) := by
    unfold forLetItem
    apply Parser.bind_validFor (keyword_validFor .letKw .statement)
    intro marker
    apply Parser.bind_validFor (identifier_validFor .statement)
    intro name
    apply Parser.bind_validFor optionalLetType_validFor
    intro type
    apply Parser.bind_validFor
      (optionalLetInitializer_validFor expression expressionValueValid
        expressionValid)
    intro initializer
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : forLetItem expression input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok item final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold forLetItem at stages
      rcases simpleBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases simpleBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases simpleBind_ok_components rest with
        ⟨type, afterType, typeResult, rest⟩
      rcases simpleBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, finished⟩
      have markerReply := keyword_validFor .letKw .statement input inputValid
      rw [markerResult] at markerReply
      have nameReply := identifier_validFor .statement afterMarker
        markerReply.2.1
      rw [nameResult] at nameReply
      have typeReply := optionalLetType_validFor afterName nameReply.2.1
      rw [typeResult] at typeReply
      have initializerReply := optionalLetInitializer_validFor expression
        expressionValueValid expressionValid afterType typeReply.2.1
      rw [initializerResult] at initializerReply
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have nameValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerReply.2.2] using nameReply.1
      have typeValid : Option.ValidFor TypeExpr.ValidFor input.file type := by
        simpa [nameReply.2.2, markerReply.2.2] using typeReply.1
      have initializerValid : Option.ValidFor expressionValueValid input.file
          initializer := by
        simpa [typeReply.2.2, nameReply.2.2, markerReply.2.2] using
          initializerReply.1
      have endpointValid := forLetEnd_validFor expressionValueValid
        expressionSpan nameValid typeValid initializerValid
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some
        (acceptToken_ok_state_shape (.keyword .letKw) .statement
          (· == .keyword .letKw) markerResult).1
      have markerBefore {later : State} {first : Token}
          {endpoint : SourceSpan} (tokens : later.tokens = input.tokens)
          (cursor : input.cursor < later.cursor)
          (found : later.peek? = some first)
          (starts : first.span.startByte = endpoint.startByte)
          (valid : endpoint.ValidFor input.file) :
          marker.span.startByte ≤ endpoint.endByte := by
        have firstAt : input.tokens[later.cursor]? = some first := by
          simpa [tokens] using State.getElem?_eq_some_of_peek?_eq_some found
        exact Nat.le_trans markerValid.2.1 (Nat.le_trans
          (inputValid.token_end_le_token_start_of_getElem?_lt markerAt firstAt
            cursor) (by simpa [starts] using valid.2.1))
      have markerTokens := keyword_preservesTokensOnSuccess .letKw .statement
        input marker afterMarker markerResult
      have markerCursor := acceptToken_cursor_lt_onSuccess
        (.keyword .letKw) .statement (· == .keyword .letKw) markerResult
      have nameTokens := identifier_preservesTokensOnSuccess .statement
        afterMarker name afterName nameResult
      have nameCursor := identifier_cursorMonotoneOnSuccess .statement
        afterMarker name afterName nameResult
      have typeTokens := optionalLetType_preservesTokensOnSuccess
        afterName type afterType typeResult
      have typeCursor := optionalLetType_cursorMonotoneOnSuccess
        afterName type afterType typeResult
      have endpointOrder : marker.span.startByte ≤
          (forLetEnd name type initializer).endByte := by
        cases initializer with
        | some value =>
            rcases optionalLetInitializer_some_startsAfterEqual expression
                expressionStarts initializerResult with
              ⟨equal, afterEqual, first, equalResult, firstFound, firstStart⟩
            exact markerBefore
              ((symbol_preservesTokensOnSuccess .equal .statement _ _ _
                equalResult).trans (typeTokens.trans (nameTokens.trans markerTokens)))
              (Nat.lt_of_lt_of_le markerCursor (Nat.le_trans nameCursor
                (Nat.le_trans typeCursor (Nat.le_of_lt
                  (acceptToken_cursor_lt_onSuccess (.symbol .equal) .statement
                    (· == .symbol .equal) equalResult))))) firstFound firstStart
              (expressionSpan input.file value
                (by simpa only [Option.ValidFor] using initializerValid))
        | none =>
            cases type with
            | some value =>
                rcases optionalLetType_some_startsAfterColon typeResult with
                  ⟨colon, afterColon, first, colonResult, firstFound, firstStart⟩
                exact markerBefore
                  ((symbol_preservesTokensOnSuccess .colon .statement _ _ _
                    colonResult).trans (nameTokens.trans markerTokens))
                  (Nat.lt_of_lt_of_le markerCursor (Nat.le_trans nameCursor
                    (Nat.le_of_lt (acceptToken_cursor_lt_onSuccess
                      (.symbol .colon) .statement (· == .symbol .colon)
                        colonResult)))) firstFound firstStart
                  (TypeExpr.ValidFor.span_valid
                    (by simpa only [Option.ValidFor] using typeValid))
            | none =>
                rcases identifier_ok_state_shape .statement nameResult with
                  ⟨first, firstFound, firstSpan, _tokens, _cursor⟩
                exact markerBefore markerTokens markerCursor firstFound
                  (congrArg SourceSpan.startByte firstSpan) nameValid
      have outerValid := SourceSpan.cover_validFor markerValid endpointValid
        endpointOrder
      have retainedType : ∀ value ∈ type,
          TypeExpr.ValidFor input.file value := by
        intro value member
        cases type <;> simp_all [Option.ValidFor]
      have retainedInitializer : ∀ value ∈ initializer,
          expressionValueValid input.file value := by
        intro value member
        cases initializer <;> simp_all [Option.ValidFor]
      cases finished
      exact ⟨ForItem.ValidFor.letDecl outerValid nameValid retainedType
        retainedInitializer, weakResult.2.1, weakResult.2.2⟩

/-- For-header assignment/expression items preserve nested token windows. -/
theorem forAssignmentOrExpression_preservesTokenWindow
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow
      (forAssignmentOrExpression expression) := by
  unfold forAssignmentOrExpression
  apply Parser.bind_preservesTokenWindow expressionWindow
  intro left
  apply Parser.bind_preservesTokenWindow
    (optionalAssignmentTail_preservesTokenWindow expression expressionWindow)
  intro tail
  cases tail with
  | none => exact Parser.pure_preservesTokenWindow _
  | some tail =>
      cases tail <;> exact Parser.pure_preservesTokenWindow _

theorem forAssignmentOrExpression_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess
      (forAssignmentOrExpression expression) :=
  (forAssignmentOrExpression_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- For-header assignment/expression items never rewind the token cursor. -/
theorem forAssignmentOrExpression_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess
      (forAssignmentOrExpression expression) := by
  unfold forAssignmentOrExpression
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalAssignmentTail_cursorMonotoneOnSuccess expression
      expressionCursor)
  intro tail
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail <;> exact Parser.pure_cursorMonotoneOnSuccess _

/-- A for-header assignment/expression item starts at its left expression. -/
theorem forAssignmentOrExpression_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (forAssignmentOrExpression expression) (·.span) := by
  unfold forAssignmentOrExpression
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first expressionStarts
  intro left input item final parsed
  rcases simpleBind_ok_components parsed with
    ⟨tail, afterTail, _tailResult, finished⟩
  cases tail with
  | none => cases finished; rfl
  | some tail => cases tail <;> cases finished <;> rfl

/-- For-header assignment/expression items retain every nested source range. -/
theorem forAssignmentOrExpression_validFor
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (forAssignmentOrExpression expression).ValidFor
      (ForItem.ValidFor expressionValueValid) := by
  have weak : (forAssignmentOrExpression expression).ValidFor
      (fun _ _ => True) := by
    unfold forAssignmentOrExpression
    apply Parser.bind_validFor expressionValid
    intro left
    apply Parser.bind_validFor
      (optionalAssignmentTail_validFor expression expressionValueValid
        expressionValid)
    intro tail
    cases tail with
    | none => exact Parser.pure_validFor _ _ (fun _ => trivial)
    | some tail =>
        cases tail <;> exact Parser.pure_validFor _ _ (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : forAssignmentOrExpression expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok item final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold forAssignmentOrExpression at stages
      rcases simpleBind_ok_components stages with
        ⟨left, afterLeft, leftResult, rest⟩
      rcases simpleBind_ok_components rest with
        ⟨tail, afterTail, tailResult, finished⟩
      have leftContract := expressionValid input inputValid
      rw [leftResult] at leftContract
      have tailContract := optionalAssignmentTail_validFor expression
        expressionValueValid expressionValid afterLeft leftContract.2.1
      rw [tailResult] at tailContract
      have leftSpanValid := expressionSpan input.file left leftContract.1
      have tailValidInput : Option.ValidFor
          (AssignmentTail.ValidFor expressionValueValid) input.file tail := by
        simpa [leftContract.2.2] using tailContract.1
      cases tail with
      | none =>
          cases finished
          exact ⟨ForItem.ValidFor.expression leftSpanValid leftContract.1,
            weakResult.2.1, weakResult.2.2⟩
      | some assignment =>
          have assignmentValid : AssignmentTail.ValidFor expressionValueValid
              input.file assignment := by
            simpa only [Option.ValidFor] using tailValidInput
          have endpointValid := assignmentEnd_validFor expressionValueValid
            expressionSpan assignmentValid
          rcases expressionStarts input left afterLeft leftResult with
            ⟨firstToken, firstFound, firstStart⟩
          have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
          have firstSpanValid := inputValid.peek?_span_validFor firstFound
          have leftWindow := expressionWindow input
          rw [leftResult] at leftWindow
          rcases optionalAssignmentTail_some_startsAtCurrentTokenOnSuccess
            expression tailResult with
            ⟨operatorToken, operatorFound, operatorStart⟩
          have operatorAt : input.tokens[afterLeft.cursor]? =
              some operatorToken := by
            simpa [leftWindow.1] using
              State.getElem?_eq_some_of_peek?_eq_some operatorFound
          have separated := inputValid.token_end_le_token_start_of_getElem?_lt
            firstAt operatorAt (expressionCursorLt leftResult)
          have beforeOperator : left.span.startByte ≤
              assignment.startSpan.startByte :=
            Nat.le_trans (by simpa [firstStart] using firstSpanValid.2.1)
              (by simpa [operatorStart] using separated)
          have assignmentResult : assignmentTail expression afterLeft =
              .ok assignment afterTail := by
            unfold optionalAssignmentTail at tailResult
            split at tailResult
            · rcases simpleBind_ok_components tailResult with
                ⟨parsedTail, next, parsedTailResult, completed⟩
              cases completed
              exact parsedTailResult
            · cases tailResult
          have endpointOrder := assignmentTail_start_le_endOnSuccess expression
            expressionValueValid expressionValid expressionSpan
              expressionStarts leftContract.2.1 assignmentResult
          have outerValid := SourceSpan.cover_validFor leftSpanValid
            endpointValid (Nat.le_trans beforeOperator endpointOrder)
          cases assignment with
          | value operator right =>
              cases finished
              exact ⟨ForItem.ValidFor.assignValue outerValid leftContract.1
                assignmentValid.1 assignmentValid.2,
                weakResult.2.1, weakResult.2.2⟩
          | bitNot operator =>
              cases finished
              exact ⟨ForItem.ValidFor.assignBitNot outerValid leftContract.1
                assignmentValid, weakResult.2.1, weakResult.2.2⟩

end StatementSimpleInternals

/-- Public for-header items preserve every ordinary token window. -/
theorem forItem_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (forItem expression) := by
  intro input
  unfold forItem
  by_cases letBranch : isKeyword input .letKw
  · simp only [letBranch, if_true]
    exact StatementSimpleInternals.forLetItem_preservesTokenWindow
      expression expressionWindow input
  · simp only [letBranch]
    exact StatementSimpleInternals.forAssignmentOrExpression_preservesTokenWindow
      expression expressionWindow input

theorem forItem_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (forItem expression) :=
  (forItem_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Public for-header item parsing never rewinds the token cursor. -/
theorem forItem_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (forItem expression) := by
  intro input item next parsed
  unfold forItem at parsed
  by_cases letBranch : isKeyword input .letKw
  · simp only [letBranch, if_true] at parsed
    exact StatementSimpleInternals.forLetItem_cursorMonotoneOnSuccess
      expression expressionCursor input item next parsed
  · simp only [letBranch] at parsed
    exact StatementSimpleInternals.forAssignmentOrExpression_cursorMonotoneOnSuccess
      expression expressionCursor input item next parsed

/-- Public for-header items start at their selected branch's current token. -/
theorem forItem_startsAtCurrentTokenOnSuccess (expression : Parser Expr)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess (forItem expression) (·.span) := by
  intro input item next parsed
  unfold forItem at parsed
  by_cases letBranch : isKeyword input .letKw
  · simp only [letBranch, if_true] at parsed
    exact StatementSimpleInternals.forLetItem_startsAtCurrentTokenOnSuccess
      expression input item next parsed
  · simp only [letBranch] at parsed
    exact StatementSimpleInternals.forAssignmentOrExpression_startsAtCurrentTokenOnSuccess
      expression expressionStarts input item next parsed

/-- Every public for-header item retains complete source provenance. -/
theorem forItem_validFor
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSpan : ∀ file value,
      expressionValueValid file value → value.span.ValidFor file)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursorLt : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    (forItem expression).ValidFor
      (ForItem.ValidFor expressionValueValid) := by
  intro input inputValid
  unfold forItem
  by_cases letBranch : isKeyword input .letKw
  · simp only [letBranch, if_true]
    exact StatementSimpleInternals.forLetItem_validFor expression
      expressionValueValid expressionValid expressionSpan expressionStarts
        input inputValid
  · simp only [letBranch]
    exact StatementSimpleInternals.forAssignmentOrExpression_validFor
      expression expressionValueValid expressionValid expressionSpan
        expressionWindow expressionCursorLt expressionStarts input inputValid

/-- Let statements preserve nested expression token windows. -/
theorem letStatement_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (letStatement expression) := by
  unfold letStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .letKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .statement)
  intro name
  apply Parser.bind_preservesTokenWindow
    StatementSimpleInternals.optionalLetType_preservesTokenWindow
  intro type
  apply Parser.bind_preservesTokenWindow
    (StatementSimpleInternals.optionalLetInitializer_preservesTokenWindow
      expression expressionWindow)
  intro initializer
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .statement)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

theorem letStatement_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (letStatement expression) :=
  (letStatement_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Let-statement parsing never rewinds the token cursor. -/
theorem letStatement_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (letStatement expression) := by
  unfold letStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .letKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
  intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
      expression expressionCursor)
  intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A let statement starts at its leading `let` keyword. -/
theorem letStatement_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (letStatement expression) (·.span) := by
  unfold letStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw))
  intro marker input statement final parsed
  rcases StatementSimpleInternals.simpleBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨type, afterType, _typeResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨initializer, afterInitializer, _initializerResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, _semicolonResult, finished⟩
  cases finished
  rfl

/-- A successful let statement has a valid keyword-to-semicolon range. -/
theorem letStatement_span_validOnSuccess (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {statement : Statement}
    (inputValid : input.ValidFor)
    (parsed : letStatement expression input = .ok statement final) :
    statement.span.ValidFor input.file := by
  have stages := parsed
  unfold letStatement at stages
  rcases StatementSimpleInternals.simpleBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨type, afterType, typeResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨initializer, afterInitializer, initializerResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have markerContract := keyword_validFor .letKw .statement input inputValid
  rw [markerResult] at markerContract
  have nameContract := identifier_validFor .statement afterMarker
    markerContract.2.1
  rw [nameResult] at nameContract
  have typeContract := StatementSimpleInternals.optionalLetType_validFor
    afterName nameContract.2.1
  rw [typeResult] at typeContract
  have initializerContract :=
    StatementSimpleInternals.optionalLetInitializer_validFor expression
      expressionValueValid expressionValid afterType typeContract.2.1
  rw [initializerResult] at initializerContract
  have semicolonContract := symbol_validFor .semicolon .statement
    afterInitializer initializerContract.2.1
  rw [semicolonResult] at semicolonContract
  have markerValid : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerContract.1
  have semicolonValid : semicolon.span.ValidFor input.file := by
    simpa only [Located.ValidFor, initializerContract.2.2,
      typeContract.2.2, nameContract.2.2, markerContract.2.2] using
      semicolonContract.1
  have markerShape := acceptToken_ok_state_shape (.keyword .letKw)
    .statement (· == .keyword .letKw) markerResult
  have semicolonShape := symbol_ok_state_shape .semicolon .statement
    semicolonResult
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
  have semicolonAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
  have markerTokens := keyword_preservesTokensOnSuccess .letKw .statement
    input marker afterMarker markerResult
  have nameTokens := identifier_preservesTokensOnSuccess .statement
    afterMarker name afterName nameResult
  have typeTokens :=
    StatementSimpleInternals.optionalLetType_preservesTokensOnSuccess
      afterName type afterType typeResult
  have initializerTokens :=
    StatementSimpleInternals.optionalLetInitializer_preservesTokensOnSuccess
      expression expressionWindow afterType initializer afterInitializer
        initializerResult
  have semicolonAt : input.tokens[afterInitializer.cursor]? = some semicolon := by
    simpa [initializerTokens, typeTokens, nameTokens, markerTokens] using
      semicolonAtAfter
  have cursorOrder : input.cursor < afterInitializer.cursor :=
    Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.keyword .letKw) .statement
        (· == .keyword .letKw) markerResult)
      (Nat.le_trans
        (identifier_cursorMonotoneOnSuccess .statement afterMarker name
          afterName nameResult)
        (Nat.le_trans
          (StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
            afterName type afterType typeResult)
          (StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
            expression expressionCursor afterType initializer afterInitializer
              initializerResult)))
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    markerAt semicolonAt cursorOrder
  have ordered : marker.span.startByte ≤ semicolon.span.endByte :=
    Nat.le_trans markerValid.2.1
      (Nat.le_trans separated semicolonValid.2.1)
  cases finished
  exact SourceSpan.cover_validFor markerValid semicolonValid ordered

/-- Complete let statements retain only source-valid syntax. -/
theorem letStatement_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (letStatement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have weak : (letStatement expression).ValidFor (fun _ _ => True) := by
    unfold letStatement
    apply Parser.bind_validFor (keyword_validFor .letKw .statement)
    intro marker
    apply Parser.bind_validFor (identifier_validFor .statement)
    intro name
    apply Parser.bind_validFor
      StatementSimpleInternals.optionalLetType_validFor
    intro type
    apply Parser.bind_validFor
      (StatementSimpleInternals.optionalLetInitializer_validFor expression
        expressionValueValid expressionValid)
    intro initializer
    apply Parser.bind_validFor (symbol_validFor .semicolon .statement)
    intro semicolon
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : letStatement expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold letStatement at stages
      rcases StatementSimpleInternals.simpleBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨type, afterType, typeResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have markerContract := keyword_validFor .letKw .statement input inputValid
      rw [markerResult] at markerContract
      have nameContract := identifier_validFor .statement afterMarker
        markerContract.2.1
      rw [nameResult] at nameContract
      have typeContract := StatementSimpleInternals.optionalLetType_validFor
        afterName nameContract.2.1
      rw [typeResult] at typeContract
      have initializerContract :=
        StatementSimpleInternals.optionalLetInitializer_validFor expression
          expressionValueValid expressionValid afterType typeContract.2.1
      rw [initializerResult] at initializerContract
      have nameValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerContract.2.2] using nameContract.1
      have typeValidInput : Option.ValidFor TypeExpr.ValidFor input.file type := by
        simpa [nameContract.2.2, markerContract.2.2] using typeContract.1
      have initializerValidInput : Option.ValidFor expressionValueValid
          input.file initializer := by
        simpa [typeContract.2.2, nameContract.2.2,
          markerContract.2.2] using initializerContract.1
      have retainedType : ∀ value ∈ type,
          TypeExpr.ValidFor input.file value := by
        cases type with
        | none => simp
        | some value =>
            intro retained member
            have retainedEq : retained = value := by simpa using member.symm
            subst retained
            simpa only [Option.ValidFor] using typeValidInput
      have retainedInitializer : ∀ value ∈ initializer,
          expressionValueValid input.file value := by
        cases initializer with
        | none => simp
        | some value =>
            intro retained member
            have retainedEq : retained = value := by simpa using member.symm
            subst retained
            simpa only [Option.ValidFor] using initializerValidInput
      have outerValid := letStatement_span_validOnSuccess expression
        expressionValueValid expressionValid expressionWindow expressionCursor
        inputValid parsed
      cases finished
      exact ⟨Statement.ValidFor.letDecl outerValid nameValid retainedType
        retainedInitializer, weakResult.2.1, weakResult.2.2⟩

/-- Return statements preserve nested expression token windows. -/
theorem returnStatement_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (returnStatement expression) := by
  unfold returnStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .returnKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (StatementSimpleInternals.optionalReturnValue_preservesTokenWindow
      expression expressionWindow)
  intro value
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .statement)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

theorem returnStatement_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (returnStatement expression) :=
  (returnStatement_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess

/-- Return-statement parsing never rewinds the token cursor. -/
theorem returnStatement_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (returnStatement expression) := by
  unfold returnStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .returnKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
      expression expressionCursor)
  intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A return statement starts at its `return` keyword. -/
theorem returnStatement_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (returnStatement expression) (·.span) := by
  unfold returnStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .returnKw)
      .statement (· == .keyword .returnKw))
  intro marker input statement final parsed
  rcases StatementSimpleInternals.simpleBind_ok_components parsed with
    ⟨value, afterValue, valueResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  rfl

/-- A successful return statement has a valid keyword-to-semicolon range. -/
theorem returnStatement_span_validOnSuccess (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {statement : Statement}
    (inputValid : input.ValidFor)
    (parsed : returnStatement expression input = .ok statement final) :
    statement.span.ValidFor input.file := by
  have stages := parsed
  unfold returnStatement at stages
  rcases StatementSimpleInternals.simpleBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨value, afterValue, valueResult, rest⟩
  rcases StatementSimpleInternals.simpleBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have markerContract := keyword_validFor .returnKw .statement input inputValid
  rw [markerResult] at markerContract
  have valueContract := StatementSimpleInternals.optionalReturnValue_validFor
    expression expressionValueValid expressionValid afterMarker
      markerContract.2.1
  rw [valueResult] at valueContract
  have semicolonContract := symbol_validFor .semicolon .statement afterValue
    valueContract.2.1
  rw [semicolonResult] at semicolonContract
  have markerValid : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerContract.1
  have semicolonValid : semicolon.span.ValidFor input.file := by
    simpa only [Located.ValidFor, valueContract.2.2,
      markerContract.2.2] using semicolonContract.1
  have markerShape := acceptToken_ok_state_shape (.keyword .returnKw)
    .statement (· == .keyword .returnKw) markerResult
  have semicolonShape := symbol_ok_state_shape .semicolon .statement
    semicolonResult
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
  have semicolonAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
  have valueTokens :=
    StatementSimpleInternals.optionalReturnValue_preservesTokensOnSuccess
      expression expressionWindow afterMarker value afterValue valueResult
  have markerTokens := keyword_preservesTokensOnSuccess .returnKw .statement
    input marker afterMarker markerResult
  have semicolonAt : input.tokens[afterValue.cursor]? = some semicolon := by
    simpa [valueTokens, markerTokens] using semicolonAtAfter
  have cursorOrder : input.cursor < afterValue.cursor :=
    Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.keyword .returnKw) .statement
        (· == .keyword .returnKw) markerResult)
      (StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
        expression expressionCursor afterMarker value afterValue valueResult)
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    markerAt semicolonAt cursorOrder
  have ordered : marker.span.startByte ≤ semicolon.span.endByte :=
    Nat.le_trans markerValid.2.1
      (Nat.le_trans separated semicolonValid.2.1)
  cases finished
  exact SourceSpan.cover_validFor markerValid semicolonValid ordered

/-- Complete return statements retain only source-valid syntax. -/
theorem returnStatement_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (returnStatement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have weak : (returnStatement expression).ValidFor (fun _ _ => True) := by
    unfold returnStatement
    apply Parser.bind_validFor (keyword_validFor .returnKw .statement)
    intro marker
    apply Parser.bind_validFor
      (StatementSimpleInternals.optionalReturnValue_validFor expression
        expressionValueValid expressionValid)
    intro value
    apply Parser.bind_validFor (symbol_validFor .semicolon .statement)
    intro semicolon
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : returnStatement expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold returnStatement at stages
      rcases StatementSimpleInternals.simpleBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨value, afterValue, valueResult, rest⟩
      rcases StatementSimpleInternals.simpleBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have markerContract := keyword_validFor .returnKw .statement input
        inputValid
      rw [markerResult] at markerContract
      have valueContract :=
        StatementSimpleInternals.optionalReturnValue_validFor expression
          expressionValueValid expressionValid afterMarker markerContract.2.1
      rw [valueResult] at valueContract
      have valueValidInput : Option.ValidFor expressionValueValid input.file
          value := by
        simpa [markerContract.2.2] using valueContract.1
      have retained : ∀ expression ∈ value,
          expressionValueValid input.file expression := by
        cases value with
        | none => simp
        | some expression =>
            intro retained member
            have retainedEq : retained = expression := by
              simpa using member.symm
            subst retained
            simpa only [Option.ValidFor] using valueValidInput
      have outerValid := returnStatement_span_validOnSuccess expression
        expressionValueValid expressionValid expressionWindow expressionCursor
        inputValid parsed
      cases finished
      exact ⟨Statement.ValidFor.returnStmt outerValid retained,
        weakResult.2.1, weakResult.2.2⟩

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
