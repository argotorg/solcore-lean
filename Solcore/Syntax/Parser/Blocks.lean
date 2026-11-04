import Solcore.Syntax.Parser.State
import Solcore.Syntax.Source
import Solcore.Syntax.Term
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Parser.Validity
import Solcore.Syntax.ExpressionValidity
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Parser.PrimitiveProperties
import Solcore.Syntax.Yul
import Solcore.Syntax.Type
import Solcore.Syntax.Foundation
import Solcore.Syntax.Operator
import Solcore.Syntax.DeclarativeCoreBlockGrammar
import Solcore.Syntax.Literal
import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.DeclarativeCoreBlockTailTraceGrammar
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.Parser.DiagnosticReflectionProperties

/-!
Block capture and Core block parsing.

Main declarations: `captureBlock?`, `isolateBlock`, `coreBlock`, `validateBlockTails`.

Unlike the other front files, this one also holds proofs: they name private helpers, so
they stay beside them. The rest of the proofs are internal.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Block
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Whether the final expression of a block may omit its semicolon. -/
inductive TailExpressionPolicy where
  | allow
  | require
  deriving Repr, BEq, DecidableEq

/-- Parser policy viewed in the parser-independent Core block grammar. -/
def TailExpressionPolicy.declarative :
    TailExpressionPolicy → DeclarativeGrammar.CoreBlockTailPolicy
  | .allow => .allow
  | .require => .require

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

private theorem validateExpressionSemicolon_diagnosticFree_iff
    (statement : Statement) (state : State) :
    (validateExpressionSemicolon statement state).diagnosticsRev = [] ↔
      state.diagnosticsRev = [] ∧
        DeclarativeGrammar.CoreBlockStatementTerminated statement := by
  rcases statement with ⟨span, value⟩
  cases value <;> try
    simp [validateExpressionSemicolon,
      DeclarativeGrammar.CoreBlockStatementTerminated, State.emit]
  case expression expression trailingSemicolon =>
    cases trailingSemicolon with
    | false => simp
    | true => simp

private theorem validateBlockTails_diagnosticFree_iff :
    ∀ policy statements state,
      (validateBlockTails policy statements state).diagnosticsRev = [] ↔
        state.diagnosticsRev = [] ∧
          DeclarativeGrammar.CoreBlockTailsValid policy.declarative
            statements := by
  intro policy statements
  induction statements with
  | nil =>
      intro state
      simp [validateBlockTails,
        DeclarativeGrammar.CoreBlockTailsValid]
  | cons first rest inductionHypothesis =>
      intro state
      cases rest with
      | nil =>
          cases policy <;>
            simp [validateBlockTails,
              TailExpressionPolicy.declarative,
              validateExpressionSemicolon_diagnosticFree_iff]
      | cons second tail =>
          simp [validateBlockTails,
            DeclarativeGrammar.CoreBlockTailsValid,
            TailExpressionPolicy.declarative,
            inductionHypothesis,
            validateExpressionSemicolon_diagnosticFree_iff, and_assoc]

def closeCoreBlock (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser Block := do
  let closing ← symbol .rightBrace .statement
  let body := bodyRev.reverse
  let _ ← modifyState (validateBlockTails policy body)
  pure {
    span := SourceSpan.cover opening.span closing.span
    value := body
  }

def coreBlockItems (statement : Parser Statement)
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

private theorem validateExpressionSemicolon_trace_sound (statement : Statement) (state : State) :
    ∃ trace, DeclarativeGrammar.CoreBlockStatementDiagnosticTrace statement trace ∧
      (validateExpressionSemicolon statement state).diagnostics = state.diagnostics ++ trace := by
  rcases statement with ⟨span, value⟩
  cases value <;> try exact ⟨[], .clean trivial, by simp [validateExpressionSemicolon]⟩
  case expression expression trailingSemicolon =>
    cases trailingSemicolon with
    | true => exact ⟨[], .clean trivial, by simp [validateExpressionSemicolon]⟩
    | false =>
        exact ⟨_, .missing (fun impossible => impossible), by
          simp [validateExpressionSemicolon, State.emit, State.diagnostics]⟩

private theorem validateBlockTails_trace_sound :
    ∀ policy statements state,
      ∃ trace, DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative statements trace ∧
        (validateBlockTails policy statements state).diagnostics = state.diagnostics ++ trace := by
  intro policy statements
  induction statements with
  | nil => intro state; exact ⟨[], .nil, by simp [validateBlockTails]⟩
  | cons first rest ih =>
      intro state
      cases rest with
      | nil =>
          cases policy with
          | allow => exact ⟨[], .lastAllowed, by simp [validateBlockTails]⟩
          | require =>
              rcases validateExpressionSemicolon_trace_sound first state with
                ⟨trace, checked, diagnosticEq⟩
              exact ⟨trace, .lastRequired checked, diagnosticEq⟩
      | cons second tail =>
          rcases validateExpressionSemicolon_trace_sound first state with
            ⟨headTrace, checked, headEq⟩
          rcases ih (validateExpressionSemicolon first state) with
            ⟨tailTrace, tailChecked, tailEq⟩
          refine ⟨headTrace ++ tailTrace, .cons checked tailChecked, ?_⟩
          change (validateBlockTails policy (second :: tail)
            (validateExpressionSemicolon first state)).diagnostics = _
          rw [tailEq, headEq, List.append_assoc]

/-- Raw block closing emits precisely the independent source-ordered tail
validation events, after every incoming diagnostic and the silent brace. -/
theorem closeCoreBlock_success_trace_sound
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input next : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    ∃ trace, DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
        policy.declarative bodyRev.reverse trace ∧
      next.diagnostics = input.diagnostics ++ trace := by
  unfold closeCoreBlock at result
  simp only [bind] at result
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult, modifyState, pure] at result
      cases result
      rcases validateBlockTails_trace_sound policy bodyRev.reverse afterClosing with
        ⟨trace, checked, diagnosticEq⟩
      refine ⟨trace, checked, ?_⟩
      have shape := (symbol_ok_tokenAt .rightBrace .statement closingResult).2
      simpa only [shape, State.diagnostics] using diagnosticEq

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

/-- Closing a raw Core block has the exact brace, source-order body, and
remainder even when tail validation emits ordinary diagnostics. -/
theorem closeCoreBlock_success_ordinary_sound
    (opening : Token) (policy : TailExpressionPolicy)
    (bodyRev : List Statement) {input next : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        value := bodyRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeCoreBlock at result
  simp only [bind] at result
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult, modifyState, pure] at result
      cases result
      have stateShape := validateBlockTails_state_shape policy
        bodyRev.reverse afterClosing
      have windowShape := validateBlockTails_window_shape policy
        bodyRev.reverse afterClosing
      refine ⟨closing.span, rfl, ?_⟩
      simpa [State.declarativeRemainder, stateShape.1, stateShape.2,
        windowShape] using
          symbol_success_exactTokenParses .rightBrace .statement closingResult

/--
A diagnostic-free close exposes its exact brace, body, tail policy, and input
diagnostic state.  This is the public behavioral seam for the private block-tail
validator.
-/
theorem closeCoreBlock_success_sound_and_reflects
    (opening : Token) (policy : TailExpressionPolicy)
    (bodyRev : List Statement) {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeCoreBlock opening policy bodyRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        value := bodyRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      DeclarativeGrammar.CoreBlockTailsValid policy.declarative
        bodyRev.reverse ∧
      input.diagnosticsRev = [] := by
  unfold closeCoreBlock at result
  simp only [bind] at result
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult, modifyState, pure] at result
      cases result
      have validation :=
        (validateBlockTails_diagnosticFree_iff policy bodyRev.reverse
          afterClosing).mp diagnosticFree
      have inputFree := symbol_reflectsDiagnosticFreeOnSuccess .rightBrace
        .statement input closing afterClosing closingResult validation.1
      have remainderEq :
          State.declarativeRemainder
              (validateBlockTails policy bodyRev.reverse afterClosing) =
            afterClosing.declarativeRemainder := by
        have stateShape := validateBlockTails_state_shape policy
          bodyRev.reverse afterClosing
        have windowShape := validateBlockTails_window_shape policy
          bodyRev.reverse afterClosing
        unfold State.declarativeRemainder
        rw [stateShape.1, stateShape.2, windowShape]
      refine ⟨closing.span, rfl, ?_, validation.2, inputFree⟩
      rw [remainderEq]
      exact symbol_success_exactTokenParses .rightBrace .statement
        closingResult

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

/-- Closing and delayed tail validation preserve the complete source and
active token/byte window, regardless of all incoming or emitted events. -/
theorem closeCoreBlock_success_context_eq
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input output : State} {body : Block}
    (result : closeCoreBlock opening policy bodyRev input = .ok body output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold closeCoreBlock at result
  simp only [bind] at result
  cases closingResult : symbol .rightBrace .statement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult, modifyState, pure] at result
      cases result
      have fileEq := validateBlockTails_file_shape policy bodyRev.reverse afterClosing
      have windowEq := validateBlockTails_window_shape policy bodyRev.reverse afterClosing
      have shape := (symbol_ok_tokenAt .rightBrace .statement closingResult).2
      simpa only [shape] using And.intro fileEq windowEq

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

end BlockInternals

open BlockInternals

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
end
