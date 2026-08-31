import Solcore.Syntax.Parser.Statement.Simple
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

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

end Solcore.Syntax.Parser
