import Solcore.Syntax.Parser.PrimitiveCarrierProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Whether the final expression of a block may omit its semicolon. -/
inductive TailExpressionPolicy where
  | allow
  | require
  deriving Repr, BEq, DecidableEq

private def validateExpressionSemicolon
    (statement : Statement) (state : State) : State :=
  match statement.value with
  | .expression _ false => state.emit {
      span := statement.span
      kind := .constraintViolation .expressionRequiresSemicolon
    }
  | _ => state

private def validateBlockTails (policy : TailExpressionPolicy) :
    List Statement → State → State
  | [], state => state
  | [last], state =>
      match policy with
      | .allow => state
      | .require => validateExpressionSemicolon last state
  | first :: rest, state =>
      validateBlockTails policy rest
        (validateExpressionSemicolon first state)

private def closeCoreBlock (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser Block := do
  let closing ← symbol .rightBrace .statement
  let body := bodyRev.reverse
  let _ ← modifyState (validateBlockTails policy body)
  pure {
    span := SourceSpan.cover opening.span closing.span
    value := body
  }

private def coreBlockItems (statement : Parser Statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    Nat → List Statement → State → Reply Block
  | 0, _, state => .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1, bodyRev, state =>
      if isSymbol state .rightBrace then
        closeCoreBlock opening policy bodyRev state
      else if state.atEnd then
        match symbol .rightBrace .statement state with
        | .ok _ _ => .invariant (.noProgress .statement state.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        let before := state.cursor
        match statement state with
        | .ok value next =>
            if next.cursor > before then
              coreBlockItems statement opening policy fuel
                (value :: bodyRev) next
            else
              .invariant (.noProgress .statement next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error

/-- Parse one braced Core statement sequence with explicit tail policy. -/
def coreBlock (statement : Parser Statement)
    (policy : TailExpressionPolicy) : Parser Block := fun state =>
  match symbol .leftBrace .statement state with
  | .ok opening next =>
      coreBlockItems statement opening policy
        (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private theorem validateExpressionSemicolon_state_shape
    (statement : Statement) (state : State) :
    (validateExpressionSemicolon statement state).tokens = state.tokens ∧
      (validateExpressionSemicolon statement state).cursor = state.cursor := by
  rcases statement with ⟨span, value⟩
  cases value <;> try exact ⟨rfl, rfl⟩
  case expression expression trailingSemicolon =>
    cases trailingSemicolon <;> exact ⟨rfl, rfl⟩

private theorem validateBlockTails_state_shape :
    ∀ policy statements state,
      (validateBlockTails policy statements state).tokens = state.tokens ∧
        (validateBlockTails policy statements state).cursor = state.cursor := by
  intro policy statements
  induction statements with
  | nil =>
      intro state
      exact ⟨rfl, rfl⟩
  | cons first rest inductionHypothesis =>
      intro state
      cases rest with
      | nil =>
          cases policy with
          | allow => exact ⟨rfl, rfl⟩
          | require => exact validateExpressionSemicolon_state_shape first state
      | cons second tail =>
          have recursive := inductionHypothesis
            (validateExpressionSemicolon first state)
          have update := validateExpressionSemicolon_state_shape first state
          exact ⟨recursive.1.trans update.1,
            recursive.2.trans update.2⟩

private theorem bind_cursor_lt_onSuccess_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ input value afterFirst,
      first input = .ok value afterFirst →
        input.cursor < afterFirst.cursor)
    (nextMonotone : ∀ value,
      Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (result : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at result
      exact Nat.lt_of_lt_of_le
        (firstStrict input firstValue afterFirst firstResult)
        (nextMonotone firstValue afterFirst value final result)
  | reject failure rejected =>
      simp [firstResult] at result
  | invariant error =>
      simp [firstResult] at result

private theorem closeCoreBlock_preservesTokensOnSuccess (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser.PreservesTokensOnSuccess
      (closeCoreBlock opening policy bodyRev) := by
  unfold closeCoreBlock
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .rightBrace .statement)
  intro closing
  dsimp only
  apply Parser.bind_preservesTokensOnSuccess
  · apply modifyState_preservesTokensOnSuccess
    intro state
    exact (validateBlockTails_state_shape policy bodyRev.reverse state).1
  · intro _
    exact Parser.pure_preservesTokensOnSuccess _

private theorem closeCoreBlock_cursor_lt_onSuccess (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input next : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    input.cursor < next.cursor := by
  unfold closeCoreBlock at result
  apply bind_cursor_lt_onSuccess_of_first
    (next := fun closing : Token =>
      let body := bodyRev.reverse
      do
      modifyState (validateBlockTails policy body)
      pure ({
        span := SourceSpan.cover opening.span closing.span
        value := body
      } : Block)) _ _ result
  · intro state closing afterClosing closingResult
    exact acceptToken_cursor_lt_onSuccess (.symbol .rightBrace)
      .statement (fun kind => kind == .symbol .rightBrace) closingResult
  · intro closing
    dsimp only
    apply Parser.bind_cursorMonotoneOnSuccess
    · apply modifyState_cursorMonotoneOnSuccess
      intro state
      rw [(validateBlockTails_state_shape policy bodyRev.reverse state).2]
      exact Nat.le_refl _
    · intro _
      exact Parser.pure_cursorMonotoneOnSuccess _

private theorem closeCoreBlock_ok_state_shape (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input next : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  ⟨closeCoreBlock_preservesTokensOnSuccess opening policy bodyRev
      input body next result,
    closeCoreBlock_cursor_lt_onSuccess opening policy bodyRev result⟩

private theorem coreBlockItems_ok_state_shape
    (statement : Parser Statement)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body next,
      coreBlockItems statement opening policy fuel bodyRev input =
          .ok body next →
        next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result
      unfold coreBlockItems at result
      split at result
      · exact closeCoreBlock_ok_state_shape opening policy bodyRev result
      · split at result
        · cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing =>
              simp [closingResult] at result
          | reject failure rejected =>
              simp [closingResult] at result
          | invariant error =>
              simp [closingResult] at result
        · cases statementResult : statement input with
          | ok value afterStatement =>
              simp only [statementResult] at result
              split at result
              · have recursive := inductionHypothesis
                    (value :: bodyRev) afterStatement body next result
                exact ⟨recursive.1.trans
                    (statementShape input value afterStatement statementResult),
                  Nat.lt_trans (by assumption) recursive.2⟩
              · contradiction
          | reject failure rejected =>
              simp [statementResult] at result
          | invariant error =>
              simp [statementResult] at result

private theorem coreBlockItems_cursor_lt_onSuccess
    (statement : Parser Statement) (opening : Token)
    (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body next,
      coreBlockItems statement opening policy fuel bodyRev input =
          .ok body next →
        input.cursor < next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intros
      contradiction
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result
      unfold coreBlockItems at result
      split at result
      · exact closeCoreBlock_cursor_lt_onSuccess opening policy bodyRev result
      · split at result
        · cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | invariant error => simp [closingResult] at result
        · cases statementResult : statement input with
          | ok value afterStatement =>
              simp only [statementResult] at result
              split at result
              · exact Nat.lt_trans (by assumption)
                  (inductionHypothesis (value :: bodyRev) afterStatement body
                    next result)
              · contradiction
          | reject failure rejected => simp [statementResult] at result
          | invariant error => simp [statementResult] at result

/-- Core-block success preserves the statement parser's immutable carrier. -/
theorem coreBlock_preservesTokensOnSuccess (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (coreBlock statement policy) := by
  intro input body next result
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have blockShape := coreBlockItems_ok_state_shape statement
        statementShape opening policy (afterOpening.remainingCount + 1) []
          afterOpening body next result
      have openingShape :=
        symbol_ok_state_shape .leftBrace .statement openingResult
      exact blockShape.1.trans (by rw [openingShape.2])
  | reject failure rejected =>
      simp [openingResult] at result
  | invariant error =>
      simp [openingResult] at result

/-- Every successful Core block consumes its opening and closing braces. -/
theorem coreBlock_cursor_lt_onSuccess (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    {input next : State} {body : Block}
    (result : coreBlock statement policy input = .ok body next) :
    input.cursor < next.cursor := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingShape :=
        symbol_ok_state_shape .leftBrace .statement openingResult
      have blockProgress := coreBlockItems_cursor_lt_onSuccess statement
        opening policy (afterOpening.remainingCount + 1) [] afterOpening body
          next result
      exact Nat.lt_trans (by rw [openingShape.2]; simp) blockProgress
  | reject failure rejected =>
      simp [openingResult] at result
  | invariant error =>
      simp [openingResult] at result

/-- Successful Core-block parsing never rewinds the token cursor. -/
theorem coreBlock_cursorMonotoneOnSuccess (statement : Parser Statement)
    (policy : TailExpressionPolicy) :
    Parser.CursorMonotoneOnSuccess (coreBlock statement policy) := by
  intro input body next result
  exact Nat.le_of_lt
    (coreBlock_cursor_lt_onSuccess statement policy result)

private structure CapturedBlock where
  span : SourceSpan
  window : TokenWindow

private def captureBlockTail (state : State) (opening : Token) :
    Nat → Nat → Nat → Option CapturedBlock
  | 0, _, _ => none
  | fuel + 1, depth, offset =>
      match state.peekOffset? offset with
      | none => none
      | some token =>
          match token.value with
          | .symbol .leftBrace =>
              captureBlockTail state opening fuel (depth + 1) (offset + 1)
          | .symbol .rightBrace =>
              if depth == 1 then
                some {
                  span := SourceSpan.cover opening.span token.span
                  window := {
                    endIndex := state.cursor + offset + 1
                    endByte := token.span.endByte
                  }
                }
              else
                captureBlockTail state opening fuel (depth - 1) (offset + 1)
          | _ => captureBlockTail state opening fuel depth (offset + 1)

private def captureBlock? (state : State) : Option CapturedBlock :=
  match state.peek? with
  | some opening =>
      if opening.value == .symbol .leftBrace then
        captureBlockTail state opening state.remainingCount 1 1
      else
        none
  | none => none

/--
Run a block parser in its balanced brace window. An ordinary body rejection is
local to that window: retain its complete span and diagnostics, produce an empty
body, and resume the parent immediately after the captured closing brace.
Unclosed bodies and parser invariants are deliberately not recovered here.
-/
def isolateBlock (parser : Parser Block) : Parser Block := fun state =>
  match captureBlock? state with
  | none => parser state
  | some captured =>
      let child := state.enterWindow state.cursor captured.window
      match parser child with
      | .ok body childAfter =>
          let parentAfter := { state with cursor := captured.window.endIndex }
          .ok body (parentAfter.mergeDiagnostics childAfter)
      | .reject failure childAfter =>
          let parentAfter := { state with cursor := captured.window.endIndex }
          let merged := parentAfter.mergeDiagnostics childAfter
          .ok { span := captured.span, value := [] }
            (merged.emit failure.toDiagnostic)
      | .invariant error => .invariant error

end Solcore.Syntax.Parser
