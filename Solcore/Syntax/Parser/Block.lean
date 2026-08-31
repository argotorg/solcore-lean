import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.StateCursorProperties
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ExpressionValidity

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

private theorem validateExpressionSemicolon_window_shape
    (statement : Statement) (state : State) :
    (validateExpressionSemicolon statement state).window = state.window := by
  rcases statement with ⟨span, value⟩
  cases value <;> try rfl
  case expression expression trailingSemicolon =>
    cases trailingSemicolon <;> rfl

private theorem validateBlockTails_window_shape :
    ∀ policy statements state,
      (validateBlockTails policy statements state).window = state.window := by
  intro policy statements
  induction statements with
  | nil => intro state; rfl
  | cons first rest inductionHypothesis =>
      intro state
      cases rest with
      | nil =>
          cases policy with
          | allow => rfl
          | require =>
              exact validateExpressionSemicolon_window_shape first state
      | cons second tail =>
          exact (inductionHypothesis
            (validateExpressionSemicolon first state)).trans
              (validateExpressionSemicolon_window_shape first state)

private theorem validateExpressionSemicolon_file_shape
    (statement : Statement) (state : State) :
    (validateExpressionSemicolon statement state).file = state.file := by
  rcases statement with ⟨span, value⟩
  cases value <;> try rfl
  case expression expression trailingSemicolon =>
    cases trailingSemicolon <;> rfl

private theorem validateBlockTails_file_shape :
    ∀ policy statements state,
      (validateBlockTails policy statements state).file = state.file := by
  intro policy statements
  induction statements with
  | nil => intro state; rfl
  | cons first rest inductionHypothesis =>
      intro state
      cases rest with
      | nil =>
          cases policy with
          | allow => rfl
          | require =>
              exact validateExpressionSemicolon_file_shape first state
      | cons second tail =>
          exact (inductionHypothesis
            (validateExpressionSemicolon first state)).trans
              (validateExpressionSemicolon_file_shape first state)

private theorem validateExpressionSemicolon_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementSpan : ∀ file statement,
      statementValid file statement → statement.span.ValidFor file)
    (statement : Statement) (state : State)
    (stateValid : state.ValidFor)
    (retainedValid : statementValid state.file statement) :
    (validateExpressionSemicolon statement state).ValidFor := by
  rcases statement with ⟨span, value⟩
  cases value <;> try exact stateValid
  case expression expression trailingSemicolon =>
    cases trailingSemicolon
    · exact stateValid.emit_validFor _
        (statementSpan state.file ⟨span, .expression expression false⟩
          retainedValid)
    · exact stateValid

private theorem validateBlockTails_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementSpan : ∀ file statement,
      statementValid file statement → statement.span.ValidFor file) :
    ∀ policy statements state,
      state.ValidFor →
      List.ValidFor statementValid state.file statements →
      (validateBlockTails policy statements state).ValidFor := by
  intro policy statements
  induction statements with
  | nil =>
      intro state stateValid statementsValid
      exact stateValid
  | cons first rest inductionHypothesis =>
      intro state stateValid statementsValid
      cases rest with
      | nil =>
          cases policy with
          | allow => exact stateValid
          | require =>
              exact validateExpressionSemicolon_validFor statementValid
                statementSpan first state stateValid
                (statementsValid first (by simp))
      | cons second tail =>
          have updatedValid := validateExpressionSemicolon_validFor
            statementValid statementSpan first state stateValid
              (statementsValid first (by simp))
          apply inductionHypothesis _ updatedValid
          intro retained member
          have retainedValid := statementsValid retained (by simp [member])
          simpa [validateExpressionSemicolon_file_shape first state] using
            retainedValid

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

private theorem closeCoreBlock_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementSpan : ∀ file statement,
      statementValid file statement → statement.span.ValidFor file)
    (opening : Token) (policy : TailExpressionPolicy)
    (bodyRev : List Statement) {input : State} {openingIndex : Nat}
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (bodyValid : List.ValidFor statementValid input.file bodyRev) :
    (closeCoreBlock opening policy bodyRev input).ValidFor input
      (Block.ValidFor statementValid) := by
  unfold closeCoreBlock
  simp only [bind]
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .rightBrace .statement input inputValid
      rw [closingResult] at valid
      exact valid
  | ok closing afterClosing =>
      have closingValid :=
        symbol_validFor .rightBrace .statement input inputValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape .rightBrace .statement
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
      have reversedValid : List.ValidFor statementValid afterClosing.file
          bodyRev.reverse := by
        intro retained member
        have retainedValid := bodyValid retained (by simpa using member)
        simpa [closingValid.2.2] using retainedValid
      have validated := validateBlockTails_validFor statementValid
        statementSpan policy bodyRev.reverse afterClosing closingValid.2.1
          reversedValid
      simp only [modifyState, pure]
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingSpanValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)), ?_⟩,
        validated, ?_⟩
      · intro retained member
        exact bodyValid retained (by simpa using member)
      · exact (validateBlockTails_file_shape policy bodyRev.reverse
          afterClosing).trans closingValid.2.2

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

private theorem closeCoreBlock_preservesTokenWindow (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser.PreservesTokenWindow
      (closeCoreBlock opening policy bodyRev) := by
  unfold closeCoreBlock
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .statement)
  intro closing
  dsimp only
  apply Parser.bind_preservesTokenWindow
  · apply modifyState_preservesTokenWindow
    intro state
    exact ⟨(validateBlockTails_state_shape policy bodyRev.reverse state).1,
      validateBlockTails_window_shape policy bodyRev.reverse state⟩
  · intro _
    exact Parser.pure_preservesTokenWindow _

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

/-- Closing a Core block retains the opening-brace start byte. -/
private theorem closeCoreBlock_preservesOpeningStartOnSuccess
    (opening : Token) (policy : TailExpressionPolicy)
    (bodyRev : List Statement) {input next : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    body.span.startByte = opening.span.startByte := by
  unfold closeCoreBlock at result
  simp only [bind] at result
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult] at result
      simp only [modifyState] at result
      cases result
      rfl

/-- Every successful item loop retains the original opening-brace start. -/
private theorem coreBlockItems_preservesOpeningStartOnSuccess
    (statement : Parser Statement) (opening : Token)
    (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body next,
      coreBlockItems statement opening policy fuel bodyRev input =
          .ok body next →
        body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result
      unfold coreBlockItems at result
      split at result
      · exact closeCoreBlock_preservesOpeningStartOnSuccess opening policy
          bodyRev result
      · split at result
        · cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | invariant error => simp [closingResult] at result
        · cases statementResult : statement input with
          | ok value afterStatement =>
              simp only [statementResult] at result
              split at result
              · exact inductionHypothesis (value :: bodyRev) afterStatement
                  body next result
              · contradiction
          | reject failure rejected => simp [statementResult] at result
          | invariant error => simp [statementResult] at result

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

private theorem coreBlockItems_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementSpan : ∀ file statement,
      statementValid file statement → statement.span.ValidFor file)
    (statement : Parser Statement)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input openingIndex,
      input.ValidFor →
      input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor statementValid input.file bodyRev →
      (coreBlockItems statement opening policy fuel bodyRev input).ValidFor
        input (Block.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev input openingIndex inputValid openingFound openingBefore
        bodyValid
      unfold coreBlockItems
      split
      · exact closeCoreBlock_validFor statementValid statementSpan opening
          policy bodyRev inputValid openingFound openingBefore bodyValid
      · split
        · cases closingResult : symbol .rightBrace .statement input with
          | invariant error => trivial
          | reject failure rejected =>
              have valid :=
                symbol_validFor .rightBrace .statement input inputValid
              rw [closingResult] at valid
              exact valid
          | ok closing next => trivial
        · cases statementResult : statement input with
          | invariant error => trivial
          | reject failure rejected =>
              have valid := statementContract input inputValid
              rw [statementResult] at valid
              exact valid
          | ok retained next =>
              have retainedReply := statementContract input inputValid
              rw [statementResult] at retainedReply
              simp only
              split
              · have tokensEq := statementShape input retained next
                    statementResult
                have accumulatedValid : List.ValidFor statementValid
                    next.file (retained :: bodyRev) := by
                  intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · simpa [retainedReply.2.2] using retainedReply.1
                  · have prior := bodyValid item member
                    simpa [retainedReply.2.2] using prior
                have recursive := inductionHypothesis (retained :: bodyRev)
                  next openingIndex retainedReply.2.1
                    (by simpa [tokensEq] using openingFound)
                    (Nat.lt_trans openingBefore (by assumption))
                    accumulatedValid
                exact recursive.of_file_eq retainedReply.2.2
              · trivial

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

private theorem coreBlockItems_preservesTokenWindow
    (statement : Parser Statement)
    (statementShape : Parser.PreservesTokenWindow statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev,
      Parser.PreservesTokenWindow
        (coreBlockItems statement opening policy fuel bodyRev) := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev input
      unfold coreBlockItems
      split
      · exact closeCoreBlock_preservesTokenWindow opening policy bodyRev input
      · split
        · have closingShape :=
            symbol_preservesTokenWindow .rightBrace .statement input
          cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing => trivial
          | reject failure rejected =>
              rw [closingResult] at closingShape
              exact closingShape
          | invariant error => trivial
        · have itemShape := statementShape input
          cases statementResult : statement input with
          | ok value afterStatement =>
              rw [statementResult] at itemShape
              simp only
              split
              · exact (inductionHypothesis (value :: bodyRev)
                  afterStatement).trans itemShape
              · trivial
          | reject failure rejected =>
              rw [statementResult] at itemShape
              exact itemShape
          | invariant error => trivial

/-- A valid, token-preserving statement parser lifts through Core braces. -/
theorem coreBlock_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (statementSpan : ∀ file retained,
      statementValid file retained → retained.span.ValidFor file) :
    (coreBlock statement policy).ValidFor
      (Block.ValidFor statementValid) := by
  intro input inputValid
  unfold coreBlock
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftBrace .statement input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid :=
        symbol_validFor .leftBrace .statement input inputValid
      rw [openingResult] at openingValid
      have openingShape :=
        symbol_ok_state_shape .leftBrace .statement openingResult
      have openingFound :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have recursive := coreBlockItems_validFor statementValid statementSpan
        statement statementContract statementShape opening policy
          (afterOpening.remainingCount + 1) [] afterOpening input.cursor
          openingValid.2.1
          (by simpa [openingShape.2] using openingFound)
          (by rw [openingShape.2]; simp)
          (by simp [List.ValidFor])
      exact recursive.of_file_eq openingValid.2.2

/-- Core-block replies preserve the statement parser's complete token window. -/
theorem coreBlock_preservesTokenWindow (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (coreBlock statement policy) := by
  intro input
  unfold coreBlock
  have openingShape :=
    symbol_preservesTokenWindow .leftBrace .statement input
  cases openingResult : symbol .leftBrace .statement input with
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      exact (coreBlockItems_preservesTokenWindow statement statementShape
        opening policy (afterOpening.remainingCount + 1) []
        afterOpening).trans openingShape
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

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

/-- A successful Core block starts at its opening-brace token. -/
theorem coreBlock_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy) :
    Parser.StartsAtCurrentTokenOnSuccess
      (coreBlock statement policy) (·.span) := by
  intro input body next result
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have found :=
        (symbol_ok_state_shape .leftBrace .statement openingResult).1
      have start := coreBlockItems_preservesOpeningStartOnSuccess statement
        opening policy (afterOpening.remainingCount + 1) [] afterOpening body
          next result
      exact ⟨opening, found, start.symm⟩

namespace BlockInternals

structure CapturedBlock where
  span : SourceSpan
  window : TokenWindow

def captureBlockTail (state : State) (opening : Token) :
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

def captureBlock? (state : State) : Option CapturedBlock :=
  match state.peek? with
  | some opening =>
      if opening.value == .symbol .leftBrace then
        captureBlockTail state opening state.remainingCount 1 1
      else
        none
  | none => none

namespace CapturedBlock

/-- Source and child-window invariants retained by a balanced capture. -/
structure ValidFor (input : State) (captured : CapturedBlock) : Prop where
  span : captured.span.ValidFor input.file
  cursor_lt_endIndex : input.cursor < captured.window.endIndex
  endIndex_le_window : captured.window.endIndex ≤ input.window.endIndex
  endIndex_le_tokens : captured.window.endIndex ≤ input.tokens.size
  endByte_le_source :
    captured.window.endByte ≤ input.file.content.utf8ByteSize
  endByte_boundary :
    isUtf8Boundary input.file.content captured.window.endByte = true
  entered :
    (input.enterWindow input.cursor captured.window).ValidFor

end CapturedBlock

private theorem peekOffset?_index_lt_endIndex {state : State}
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    state.cursor + offset < state.window.endIndex := by
  unfold State.peekOffset? at found
  dsimp only at found
  split at found
  · assumption
  · contradiction

/-- Every successful tail capture defines a valid nested parser window. -/
theorem captureBlockTail_validFor (state : State) (opening : Token) :
    ∀ fuel depth offset captured,
      state.ValidFor →
      state.peek? = some opening →
      0 < offset →
      captureBlockTail state opening fuel depth offset = some captured →
      captured.ValidFor state := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro depth offset captured stateValid openingFound offsetPositive result
      unfold captureBlockTail at result
      cases found : state.peekOffset? offset with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          rcases token with ⟨closingSpan, kind⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;> try
                exact inductionHypothesis _ (offset + 1) _ stateValid
                  openingFound (by omega) result
              case rightBrace =>
                by_cases atRoot : depth = 1
                · subst depth
                  have capturedEq := Option.some.inj (by
                    simpa using result)
                  subst captured
                  have openingValid := stateValid.peek?_span_validFor
                    openingFound
                  have openingAt :=
                    State.getElem?_eq_some_of_peek?_eq_some openingFound
                  have closingAt :=
                    State.getElem?_eq_some_of_peekOffset?_eq_some found
                  have closingValid :=
                    stateValid.token_span_validFor_of_getElem?_eq_some
                      closingAt
                  have separated :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      openingAt closingAt (by omega)
                  have coverOrdered :
                      opening.span.startByte ≤ closingSpan.endByte :=
                    Nat.le_trans openingValid.2.1
                      (Nat.le_trans separated closingValid.2.1)
                  have spanValid := SourceSpan.cover_validFor openingValid
                    closingValid coverOrdered
                  have offsetInWindow :=
                    peekOffset?_index_lt_endIndex found
                  have childEndLeWindow :
                      state.cursor + offset + 1 ≤ state.window.endIndex := by
                    omega
                  have childEndLeTokens :
                      state.cursor + offset + 1 ≤ state.tokens.size :=
                    Nat.le_trans childEndLeWindow stateValid.endIndex_le_size
                  have childValid :
                      (state.enterWindow state.cursor {
                        endIndex := state.cursor + offset + 1
                        endByte := closingSpan.endByte
                      }).ValidFor := by
                    refine {
                      tokens := stateValid.tokens
                      cursor_le_endIndex := by
                        change state.cursor ≤ state.cursor + offset + 1
                        omega
                      endIndex_le_size := childEndLeTokens
                      endByte_le_source := closingValid.2.2.1
                      endByte_boundary := closingValid.2.2.2.2
                      diagnosticsRev := ?_
                    }
                    intro diagnostic member
                    simp [State.enterWindow] at member
                  exact {
                    span := spanValid
                    cursor_lt_endIndex := by
                      change state.cursor < state.cursor + offset + 1
                      omega
                    endIndex_le_window := childEndLeWindow
                    endIndex_le_tokens := childEndLeTokens
                    endByte_le_source := closingValid.2.2.1
                    endByte_boundary := closingValid.2.2.2.2
                    entered := childValid
                  }
                · exact inductionHypothesis (depth - 1) (offset + 1) _
                    stateValid openingFound (by omega) (by
                      simpa [atRoot] using result)
          | keyword keyword =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | identifier text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | yulIdentifier text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | decimalLiteral text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | hexadecimalLiteral text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | stringLiteral text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | yulMetaBacktick text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result
          | yulMetaInterpolation text =>
              exact inductionHypothesis _ (offset + 1) _ stateValid
                openingFound (by omega) result

/-- A balanced capture from a valid input yields a valid child window. -/
theorem captureBlock?_validFor {input : State} {captured : CapturedBlock}
    (inputValid : input.ValidFor)
    (result : captureBlock? input = some captured) :
    captured.ValidFor input := by
  unfold captureBlock? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some opening =>
      simp only [found] at result
      split at result
      · exact captureBlockTail_validFor input opening input.remainingCount 1 1
          captured inputValid found (by omega) result
      · contradiction

private theorem captureBlockTail_preservesOpeningStart
    (state : State) (opening : Token) :
    ∀ fuel depth offset captured,
      captureBlockTail state opening fuel depth offset = some captured →
      opening.span.startByte = captured.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro depth offset captured result
      unfold captureBlockTail at result
      cases found : state.peekOffset? offset with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          rcases token with ⟨closingSpan, kind⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;> try
                exact inductionHypothesis _ _ _ result
              case rightBrace =>
                by_cases atRoot : depth = 1
                · subst depth
                  have capturedEq := Option.some.inj (by
                    simpa using result)
                  subst captured
                  rfl
                · exact inductionHypothesis (depth - 1) (offset + 1) _
                    (by simpa [atRoot] using result)
          | keyword keyword => exact inductionHypothesis _ _ _ result
          | identifier text => exact inductionHypothesis _ _ _ result
          | yulIdentifier text => exact inductionHypothesis _ _ _ result
          | decimalLiteral text => exact inductionHypothesis _ _ _ result
          | hexadecimalLiteral text => exact inductionHypothesis _ _ _ result
          | stringLiteral text => exact inductionHypothesis _ _ _ result
          | yulMetaBacktick text => exact inductionHypothesis _ _ _ result
          | yulMetaInterpolation text =>
              exact inductionHypothesis _ _ _ result

/-- A balanced capture starts at the current opening-brace token. -/
theorem captureBlock?_startsAtCurrentToken {input : State}
    {captured : CapturedBlock}
    (result : captureBlock? input = some captured) :
    ∃ opening, input.peek? = some opening ∧
      opening.span.startByte = captured.span.startByte := by
  unfold captureBlock? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some opening =>
      simp only [found] at result
      split at result
      · exact ⟨opening, rfl,
          captureBlockTail_preservesOpeningStart input opening
            input.remainingCount 1 1 captured result⟩
      · contradiction

end BlockInternals

open BlockInternals

private theorem captureBlockTail_cursor_lt_endIndex
    (state : State) (opening : Token) :
    ∀ fuel depth offset captured,
      captureBlockTail state opening fuel depth offset = some captured →
        state.cursor < captured.window.endIndex := by
  intro fuel
  induction fuel with
  | zero =>
      intros
      contradiction
  | succ fuel inductionHypothesis =>
      intro depth offset captured result
      unfold captureBlockTail at result
      cases found : state.peekOffset? offset with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          rcases token with ⟨span, kind⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;>
                try { exact inductionHypothesis _ _ _ result }
              case rightBrace =>
                by_cases atRoot : depth = 1
                · subst depth
                  have capturedEq := Option.some.inj (by
                    simpa using result)
                  subst captured
                  change state.cursor < state.cursor + offset + 1
                  omega
                · apply inductionHypothesis (depth - 1) (offset + 1)
                  simpa [atRoot] using result
          | keyword keyword => exact inductionHypothesis _ _ _ result
          | identifier text => exact inductionHypothesis _ _ _ result
          | yulIdentifier text => exact inductionHypothesis _ _ _ result
          | decimalLiteral text => exact inductionHypothesis _ _ _ result
          | hexadecimalLiteral text => exact inductionHypothesis _ _ _ result
          | stringLiteral text => exact inductionHypothesis _ _ _ result
          | yulMetaBacktick text => exact inductionHypothesis _ _ _ result
          | yulMetaInterpolation text =>
              exact inductionHypothesis _ _ _ result

private theorem captureBlock?_cursor_lt_endIndex {state : State}
    {captured : CapturedBlock}
    (result : captureBlock? state = some captured) :
    state.cursor < captured.window.endIndex := by
  unfold captureBlock? at result
  cases found : state.peek? with
  | none => simp [found] at result
  | some opening =>
      simp only [found] at result
      split at result
      · exact captureBlockTail_cursor_lt_endIndex state opening
          state.remainingCount 1 1 captured result
      · contradiction

/-- Whether the current cursor begins a lexically balanced braced block. -/
def hasBalancedBlockCapture (state : State) : Bool :=
  (captureBlock? state).isSome

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

private theorem parentAfterCapture_validFor {input : State}
    {captured : CapturedBlock} (inputValid : input.ValidFor)
    (capturedValid : captured.ValidFor input) :
    ({ input with cursor := captured.window.endIndex } : State).ValidFor := by
  exact {
    tokens := inputValid.tokens
    cursor_le_endIndex := capturedValid.endIndex_le_window
    endIndex_le_size := inputValid.endIndex_le_size
    endByte_le_source := inputValid.endByte_le_source
    endByte_boundary := inputValid.endByte_boundary
    diagnosticsRev := inputValid.diagnosticsRev
  }

private theorem mergeDiagnostics_validFor {parent child : State}
    (parentValid : parent.ValidFor) (childValid : child.ValidFor)
    (childFile : child.file = parent.file) :
    (parent.mergeDiagnostics child).ValidFor := by
  refine {
    tokens := parentValid.tokens
    cursor_le_endIndex := parentValid.cursor_le_endIndex
    endIndex_le_size := parentValid.endIndex_le_size
    endByte_le_source := parentValid.endByte_le_source
    endByte_boundary := parentValid.endByte_boundary
    diagnosticsRev := ?_
  }
  intro diagnostic member
  change diagnostic ∈ child.diagnosticsRev ++ parent.diagnosticsRev at member
  change diagnostic.span.ValidFor parent.file
  rcases List.mem_append.mp member with childMember | parentMember
  · simpa only [childFile] using
      childValid.diagnosticsRev diagnostic childMember
  · exact parentValid.diagnosticsRev diagnostic parentMember

/-- Isolation preserves recursive block and parser-state validity. -/
theorem isolateBlock_validFor
    (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Block)
    (parserValid : parser.ValidFor (Block.ValidFor statementValid)) :
    (isolateBlock parser).ValidFor (Block.ValidFor statementValid) := by
  intro input inputValid
  unfold isolateBlock
  cases captureResult : captureBlock? input with
  | none =>
      simpa only [captureResult] using parserValid input inputValid
  | some captured =>
      have capturedValid := captureBlock?_validFor inputValid captureResult
      have childReplyValid := parserValid
        (input.enterWindow input.cursor captured.window)
        capturedValid.entered
      simp only
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok body childAfter =>
          rw [childResult] at childReplyValid
          simp only [Reply.ValidFor]
          have bodyValid : Block.ValidFor statementValid input.file body := by
            simpa [State.enterWindow] using childReplyValid.1
          have parentValid := parentAfterCapture_validFor inputValid
            capturedValid
          have childFile : childAfter.file = input.file := by
            simpa [State.enterWindow] using childReplyValid.2.2
          have mergedValid := mergeDiagnostics_validFor parentValid
            childReplyValid.2.1 childFile
          exact ⟨bodyValid, mergedValid, rfl⟩
      | reject failure childAfter =>
          rw [childResult] at childReplyValid
          simp only [Reply.ValidFor]
          have emptyValid : Block.ValidFor statementValid input.file {
              span := captured.span
              value := []
            } := ⟨capturedValid.span, by simp⟩
          have parentValid := parentAfterCapture_validFor inputValid
            capturedValid
          have childFile : childAfter.file = input.file := by
            simpa [State.enterWindow] using childReplyValid.2.2
          have mergedValid := mergeDiagnostics_validFor parentValid
            childReplyValid.2.1 childFile
          have failureValid : failure.span.ValidFor input.file := by
            simpa [State.enterWindow] using childReplyValid.1
          have emittedValid := mergedValid.emit_validFor
            failure.toDiagnostic
            (failure.toDiagnostic_span_validFor failureValid)
          exact ⟨emptyValid, emittedValid, rfl⟩
      | invariant error =>
          simp only [Reply.ValidFor]

/-- Block isolation preserves the parent token carrier on every success path. -/
theorem isolateBlock_preservesTokensOnSuccess (parser : Parser Block)
    (parserShape : Parser.PreservesTokensOnSuccess parser) :
    Parser.PreservesTokensOnSuccess (isolateBlock parser) := by
  intro input body next result
  unfold isolateBlock at result
  cases captureResult : captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact parserShape input body next result
  | some captured =>
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          rfl
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          rfl
      | invariant error =>
          simp [childResult] at result

/-- Block isolation preserves the parent's complete ordinary token window. -/
theorem isolateBlock_preservesTokenWindow (parser : Parser Block)
    (parserShape : Parser.PreservesTokenWindow parser) :
    Parser.PreservesTokenWindow (isolateBlock parser) := by
  intro input
  unfold isolateBlock
  cases captureResult : captureBlock? input with
  | none =>
      exact parserShape input
  | some captured =>
      simp only
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok childBody childAfter =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨rfl, rfl⟩
      | reject failure childAfter =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨rfl, rfl⟩
      | invariant error =>
          simp only [Reply.PreservesTokenWindow]

private theorem isolateBlock_cursor_lt_onSuccess_of_capture
    (parser : Parser Block) {input next : State} {body : Block}
    {captured : CapturedBlock}
    (captureResult : captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor := by
  have capturedProgress := captureBlock?_cursor_lt_endIndex captureResult
  unfold isolateBlock at result
  simp only [captureResult] at result
  cases childResult : parser
      (input.enterWindow input.cursor captured.window) with
  | ok childBody childAfter =>
      simp only [childResult] at result
      cases result
      simpa [State.mergeDiagnostics] using capturedProgress
  | reject failure childAfter =>
      simp only [childResult] at result
      cases result
      simpa [State.mergeDiagnostics, State.emit] using capturedProgress
  | invariant error =>
      simp [childResult] at result

/-- A balanced captured block always advances beyond its closing brace. -/
theorem isolateBlock_cursor_lt_onSuccess_of_balancedCapture
    (parser : Parser Block) {input next : State} {body : Block}
    (captured : hasBalancedBlockCapture input = true)
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor := by
  rcases Option.isSome_iff_exists.mp captured with
    ⟨capturedBlock, captureResult⟩
  exact isolateBlock_cursor_lt_onSuccess_of_capture parser captureResult result

/-- Block isolation either keeps the parser's progress or skips its capture. -/
theorem isolateBlock_cursorMonotoneOnSuccess (parser : Parser Block)
    (parserMonotone : Parser.CursorMonotoneOnSuccess parser) :
    Parser.CursorMonotoneOnSuccess (isolateBlock parser) := by
  intro input body next result
  cases captureResult : captureBlock? input with
  | none =>
      unfold isolateBlock at result
      simp only [captureResult] at result
      exact parserMonotone input body next result
  | some captured =>
      exact Nat.le_of_lt
        (isolateBlock_cursor_lt_onSuccess_of_capture parser captureResult result)

/-- Block isolation retains the current-token start on every success path. -/
theorem isolateBlock_startsAtCurrentTokenOnSuccess (parser : Parser Block)
    (parserStarts :
      Parser.StartsAtCurrentTokenOnSuccess parser (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess (isolateBlock parser) (·.span) := by
  intro input body next result
  unfold isolateBlock at result
  cases captureResult : captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact parserStarts input body next result
  | some captured =>
      rcases captureBlock?_startsAtCurrentToken captureResult with
        ⟨opening, openingFound, captureStart⟩
      have capturedProgress := captureBlock?_cursor_lt_endIndex captureResult
      have inputProgress :=
        State.cursor_lt_endIndex_of_peek?_eq_some openingFound
      have childOpening :
          (input.enterWindow input.cursor captured.window).peek? =
            some opening := by
        simpa [State.peek?, State.enterWindow, capturedProgress,
          inputProgress] using openingFound
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          rcases parserStarts _ _ _ childResult with
            ⟨token, childFound, childStart⟩
          have tokenEq : token = opening :=
            Option.some.inj (childFound.symm.trans childOpening)
          subst token
          exact ⟨opening, openingFound, childStart⟩
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          exact ⟨opening, openingFound, captureStart⟩
      | invariant error =>
          simp [childResult] at result

/-- A source-valid Core block remains source-valid inside its capture window. -/
theorem isolatedCoreBlock_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (statementSpan : ∀ file retained,
      statementValid file retained → retained.span.ValidFor file) :
    (isolateBlock (coreBlock statement policy)).ValidFor
      (Block.ValidFor statementValid) :=
  isolateBlock_validFor statementValid (coreBlock statement policy)
    (coreBlock_validFor statementValid statement policy statementContract
      statementShape statementSpan)

/-- Capturing a Core block preserves every ordinary token window. -/
theorem isolatedCoreBlock_preservesTokenWindow
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow
      (isolateBlock (coreBlock statement policy)) :=
  isolateBlock_preservesTokenWindow (coreBlock statement policy)
    (coreBlock_preservesTokenWindow statement policy statementShape)

/-- Capturing a Core block preserves its immutable token carrier on success. -/
theorem isolatedCoreBlock_preservesTokensOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess
      (isolateBlock (coreBlock statement policy)) :=
  isolateBlock_preservesTokensOnSuccess (coreBlock statement policy)
    (coreBlock_preservesTokensOnSuccess statement policy statementShape)

/-- Captured Core-block success never rewinds the parent cursor. -/
theorem isolatedCoreBlock_cursorMonotoneOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy) :
    Parser.CursorMonotoneOnSuccess
      (isolateBlock (coreBlock statement policy)) :=
  isolateBlock_cursorMonotoneOnSuccess (coreBlock statement policy)
    (coreBlock_cursorMonotoneOnSuccess statement policy)

/-- Captured Core blocks retain the parent input's opening-brace start. -/
theorem isolatedCoreBlock_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy) :
    Parser.StartsAtCurrentTokenOnSuccess
      (isolateBlock (coreBlock statement policy)) (·.span) :=
  isolateBlock_startsAtCurrentTokenOnSuccess (coreBlock statement policy)
    (coreBlock_startsAtCurrentTokenOnSuccess statement policy)

end Solcore.Syntax.Parser
