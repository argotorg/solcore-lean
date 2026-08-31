import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.StateCursorProperties
import Solcore.Syntax.ModuleValidity

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Exact operator-token subset accepted inside import/export parentheses. -/
def operatorPart? : TokenKind → Option String
  | .symbol .colonEqual => some ":="
  | .symbol .arrow => some "->"
  | .symbol .fatArrow => some "=>"
  | .symbol .equalEqual => some "=="
  | .symbol .notEqual => some "!="
  | .symbol .greaterEqual => some ">="
  | .symbol .lessEqual => some "<="
  | .symbol .logicalAnd => some "&&"
  | .symbol .logicalOr => some "||"
  | .symbol .plusEqual => some "+="
  | .symbol .minusEqual => some "-="
  | .symbol .starEqual => some "*="
  | .symbol .slashEqual => some "/="
  | .symbol .caretEqual => some "^="
  | .symbol .ampEqual => some "&="
  | .symbol .pipeEqual => some "|="
  | .symbol .percentEqual => some "%="
  | .symbol .tildeEqual => some "~="
  | .symbol .plus => some "+"
  | .symbol .minus => some "-"
  | .symbol .star => some "*"
  | .symbol .slash => some "/"
  | .symbol .percent => some "%"
  | .symbol .bang => some "!"
  | .symbol .tilde => some "~"
  | .symbol .less => some "<"
  | .symbol .greater => some ">"
  | .symbol .equal => some "="
  | .symbol .pipe => some "|"
  | .symbol .amp => some "&"
  | .symbol .caret => some "^"
  | .symbol .colon => some ":"
  | _ => none

def isOperatorPart (kind : TokenKind) : Bool :=
  (operatorPart? kind).isSome

namespace OperatorInternals

/-- Fuel-bounded token collector used by parenthesized operator selectors. -/
def operatorParts (context : ParseContext) :
    Nat → List String → State → Reply (List String)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, partsRev, state =>
      match state.peek? with
      | some token =>
          match operatorPart? token.value with
          | some spelling =>
              operatorParts context fuel (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
          | none =>
              if partsRev.isEmpty then
                rejectAt state { head := .selectorName, tail := [] } context
              else
                .ok partsRev.reverse state
      | none =>
          if partsRev.isEmpty then
            rejectAt state { head := .selectorName, tail := [] } context
          else
            .ok partsRev.reverse state

end OperatorInternals

open OperatorInternals

private theorem operatorParts_validFor (context : ParseContext) :
    ∀ fuel partsRev state,
      (state.ValidFor →
        (operatorParts context fuel partsRev state).ValidFor state
          (fun _ _ => True)) ∧
      ∀ parts next, operatorParts context fuel partsRev state = .ok parts next →
        next.tokens = state.tokens ∧ state.cursor ≤ next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev state
      refine ⟨fun _ => trivial, ?_⟩
      intro parts next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro partsRev state
      unfold operatorParts
      cases found : state.peek? with
      | some token =>
          simp only
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only
              have recursive := inductionHypothesis (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
              refine ⟨?_, ?_⟩
              · intro stateValid
                have advancedValid :
                    ({ state with cursor := state.cursor + 1 } : State).ValidFor := by
                  apply stateValid.advance?_validFor (token := token)
                  unfold State.advance?
                  rw [found]
                  rfl
                exact (recursive.1 advancedValid).of_file_eq rfl
              intro parts next result
              have shape := recursive.2 parts next result
              exact ⟨shape.1, Nat.le_trans
                (Nat.le_add_right state.cursor 1) shape.2⟩
          | none =>
              simp only
              split
              · refine ⟨?_, ?_⟩
                · intro stateValid
                  unfold rejectAt Reply.ValidFor
                  exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
                · intro parts next result
                  contradiction
              · refine ⟨?_, ?_⟩
                · intro stateValid
                  exact ⟨trivial, stateValid, rfl⟩
                intro parts next result
                cases result
                exact ⟨rfl, Nat.le_refl _⟩

      | none =>
          simp only
          split
          · refine ⟨?_, ?_⟩
            · intro stateValid
              unfold rejectAt Reply.ValidFor
              exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
            · intro parts next result
              contradiction
          · refine ⟨?_, ?_⟩
            · intro stateValid
              exact ⟨trivial, stateValid, rfl⟩
            intro parts next result
            cases result
            exact ⟨rfl, Nat.le_refl _⟩

private theorem operatorParts_preservesTokenWindow
    (context : ParseContext) :
    ∀ fuel partsRev,
      Parser.PreservesTokenWindow (operatorParts context fuel partsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro partsRev input
      unfold operatorParts
      cases found : input.peek? with
      | some token =>
          simp only
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only
              exact (inductionHypothesis (spelling :: partsRev)
                { input with cursor := input.cursor + 1 }).trans ⟨rfl, rfl⟩
          | none =>
              simp only
              split
              · exact rejectAt_preservesTokenWindow input _ _
              · exact ⟨rfl, rfl⟩
      | none =>
          simp only
          split
          · exact rejectAt_preservesTokenWindow input _ _
          · exact ⟨rfl, rfl⟩

/-- Parse a nonempty parenthesized operator selector. -/
def operatorSelector (context : ParseContext) : Parser SelectorName := fun state =>
  match symbol .leftParen context state with
  | .ok opening afterOpening =>
      match operatorParts context (afterOpening.remainingCount + 1) []
          afterOpening with
      | .ok parts afterParts =>
          match symbol .rightParen context afterParts with
          | .ok closing next => .ok {
              span := SourceSpan.cover opening.span closing.span
              value := .operator (String.join parts)
            } next
          | .reject failure next => .reject failure next
          | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parenthesized operator selectors preserve their complete source range. -/
theorem operatorSelector_validFor (context : ParseContext) :
    (operatorSelector context).ValidFor SelectorName.ValidFor := by
  intro input inputValid
  unfold operatorSelector
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have openingValid := symbol_validFor .leftParen context input inputValid
      rw [openingResult] at openingValid
      simpa only [Reply.ValidFor] using openingValid
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen context input inputValid
      rw [openingResult] at openingValid
      have openingShape :=
        symbol_ok_state_shape .leftParen context openingResult
      have partsProperties := operatorParts_validFor context
        (afterOpening.remainingCount + 1) [] afterOpening
      simp only
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have partsValid := partsProperties.1 openingValid.2.1
          rw [partsResult] at partsValid
          simpa only [Reply.ValidFor] using
            partsValid.of_file_eq openingValid.2.2
      | ok parts afterParts =>
          have partsValid := partsProperties.1 openingValid.2.1
          rw [partsResult] at partsValid
          have partsShape := partsProperties.2 parts afterParts partsResult
          have openingFoundInput :=
            State.getElem?_eq_some_of_peek?_eq_some openingShape.1
          have openingFoundAfterParts :
              afterParts.tokens[input.cursor]? = some opening := by
            simpa [partsShape.1, openingShape.2] using openingFoundInput
          have openingBeforeAfterOpening :
              input.cursor < afterOpening.cursor := by
            rw [openingShape.2]
            simp
          have openingBeforeAfterParts : input.cursor < afterParts.cursor :=
            Nat.lt_of_lt_of_le openingBeforeAfterOpening partsShape.2
          have openingSpanValidAfterParts :
              opening.span.ValidFor afterParts.file := by
            have spanValid : opening.span.ValidFor input.file := by
              simpa only [Located.ValidFor] using openingValid.1
            simpa [partsValid.2.2, openingValid.2.2] using spanValid
          simp only
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have closingValid :=
                symbol_validFor .rightParen context afterParts partsValid.2.1
              rw [closingResult] at closingValid
              simpa only [Reply.ValidFor] using closingValid.of_file_eq
                (partsValid.2.2.trans openingValid.2.2)
          | ok closing next =>
              have closingValid :=
                symbol_validFor .rightParen context afterParts partsValid.2.1
              rw [closingResult] at closingValid
              have closingShape :=
                symbol_ok_state_shape .rightParen context closingResult
              have closingFound :=
                State.getElem?_eq_some_of_peek?_eq_some closingShape.1
              have openingBeforeClosing :=
                partsValid.2.1.token_end_le_token_start_of_getElem?_lt
                  openingFoundAfterParts closingFound openingBeforeAfterParts
              have closingSpanValid :
                  closing.span.ValidFor afterParts.file := by
                simpa only [Located.ValidFor] using closingValid.1
              have coverValidAfterParts :
                  (SourceSpan.cover opening.span closing.span).ValidFor
                    afterParts.file := by
                apply SourceSpan.cover_validFor openingSpanValidAfterParts
                  closingSpanValid
                exact Nat.le_trans openingSpanValidAfterParts.2.1
                  (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)
              have coverValidInput :
                  (SourceSpan.cover opening.span closing.span).ValidFor
                    input.file := by
                simpa [partsValid.2.2, openingValid.2.2] using
                  coverValidAfterParts
              simp only
              unfold Reply.ValidFor SelectorName.ValidFor
              exact ⟨⟨coverValidInput, trivial⟩, closingValid.2.1,
                closingValid.2.2.trans
                  (partsValid.2.2.trans openingValid.2.2)⟩

/-- Operator selectors preserve the token window on every ordinary reply. -/
theorem operatorSelector_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (operatorSelector context) := by
  intro input
  unfold operatorSelector
  have openingShape := symbol_preservesTokenWindow .leftParen context input
  cases openingResult : symbol .leftParen context input with
  | invariant error =>
      simp only [Reply.PreservesTokenWindow]
  | reject failure rejected =>
      rw [openingResult] at openingShape
      simpa only [openingResult, Reply.PreservesTokenWindow] using openingShape
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      simp only
      have partsShape := operatorParts_preservesTokenWindow context
        (afterOpening.remainingCount + 1) [] afterOpening
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error =>
          simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          rw [partsResult] at partsShape
          simpa only [Reply.PreservesTokenWindow] using
            partsShape.trans openingShape
      | ok parts afterParts =>
          rw [partsResult] at partsShape
          simp only
          have closingShape := symbol_preservesTokenWindow .rightParen
            context afterParts
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error =>
              simp only [Reply.PreservesTokenWindow]
          | reject failure rejected =>
              rw [closingResult] at closingShape
              simpa only [Reply.PreservesTokenWindow] using
                closingShape.trans (partsShape.trans openingShape)
          | ok closing next =>
              rw [closingResult] at closingShape
              simpa only [Reply.PreservesTokenWindow] using
                closingShape.trans (partsShape.trans openingShape)

/-- Operator-selector success preserves the immutable token carrier. -/
theorem operatorSelector_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (operatorSelector context) := by
  intro input selector next result
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              have openingShape :=
                symbol_ok_state_shape .leftParen context openingResult
              have partsShape := (operatorParts_validFor context
                (afterOpening.remainingCount + 1) [] afterOpening).2
                  parts afterParts partsResult
              have closingShape :=
                symbol_ok_state_shape .rightParen context closingResult
              calc
                next.tokens = afterParts.tokens := by rw [closingShape.2]
                _ = afterOpening.tokens := partsShape.1
                _ = input.tokens := by rw [openingShape.2]

/-- An operator selector starts at its retained opening parenthesis. -/
theorem operatorSelector_startsAtCurrentTokenOnSuccess
    (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess
      (operatorSelector context) (·.span) := by
  intro input selector next result
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              exact ⟨opening,
                (symbol_ok_state_shape .leftParen context openingResult).1,
                rfl⟩

/-- Parse either an ordinary identifier or a parenthesized operator. -/
def selectorName (context : ParseContext) : Parser SelectorName := fun state =>
  if isSymbol state .leftParen then
    operatorSelector context state
  else
    match identifier context state with
    | .ok name next => .ok {
        span := name.span
        value := .identifier name
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

/-- Identifier and operator selector branches preserve every stored source span. -/
theorem selectorName_validFor (context : ParseContext) :
    (selectorName context).ValidFor SelectorName.ValidFor := by
  intro input inputValid
  unfold selectorName
  split
  · exact operatorSelector_validFor context input inputValid
  · cases identifierResult : identifier context input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := identifier_validFor context input inputValid
        rw [identifierResult] at nameValid
        simpa only [Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := identifier_validFor context input inputValid
        rw [identifierResult] at nameValid
        have spanValid : name.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using nameValid.1
        simp only
        unfold Reply.ValidFor SelectorName.ValidFor
        exact ⟨⟨spanValid, spanValid⟩, nameValid.2.1, nameValid.2.2⟩

/-- Selector names preserve the token window on every ordinary reply. -/
theorem selectorName_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (selectorName context) := by
  intro input
  unfold selectorName
  split
  · exact operatorSelector_preservesTokenWindow context input
  · have nameShape := identifier_preservesTokenWindow context input
    cases nameResult : identifier context input with
    | invariant error =>
        simp only [Reply.PreservesTokenWindow]
    | reject failure rejected =>
        rw [nameResult] at nameShape
        simpa only [nameResult, Reply.PreservesTokenWindow] using nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        simpa only [nameResult, Reply.PreservesTokenWindow] using nameShape

/-- Selector-name success preserves the token carrier in both branches. -/
theorem selectorName_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (selectorName context) := by
  intro input selector next result
  unfold selectorName at result
  split at result
  · exact operatorSelector_preservesTokensOnSuccess context
      input selector next result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rcases identifier_ok_state_shape context identifierResult with
          ⟨_token, _found, _span, tokensEq, _cursor⟩
        exact tokensEq

/-- A selector name starts at its identifier or opening parenthesis. -/
theorem selectorName_startsAtCurrentTokenOnSuccess (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (selectorName context) (·.span) := by
  intro input selector next result
  unfold selectorName at result
  split at result
  · exact operatorSelector_startsAtCurrentTokenOnSuccess context
      input selector next result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rcases identifier_ok_state_shape context identifierResult with
          ⟨token, found, span, _tokens, _cursor⟩
        exact ⟨token, found, congrArg SourceSpan.startByte span⟩

/-- Parenthesized operator selectors consume both delimiters. -/
theorem operatorSelector_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : operatorSelector context input = .ok selector next) :
    input.cursor < next.cursor := by
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              have openingProgress : input.cursor < afterOpening.cursor := by
                rw [(symbol_ok_state_shape .leftParen context
                  openingResult).2]
                simp
              have partsMonotone := (operatorParts_validFor context
                (afterOpening.remainingCount + 1) [] afterOpening).2
                  parts afterParts partsResult |>.2
              have closingProgress : afterParts.cursor < next.cursor := by
                rw [(symbol_ok_state_shape .rightParen context
                  closingResult).2]
                simp
              exact Nat.lt_trans openingProgress
                (Nat.lt_of_le_of_lt partsMonotone closingProgress)

/-- Operator-selector success never moves the parser cursor backwards. -/
theorem operatorSelector_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (operatorSelector context) := by
  intro input selector next result
  exact Nat.le_of_lt (operatorSelector_cursor_lt_onSuccess context result)

/-- Every successful selector consumes an identifier or operator group. -/
theorem selectorName_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : selectorName context input = .ok selector next) :
    input.cursor < next.cursor := by
  unfold selectorName at result
  split at result
  · exact operatorSelector_cursor_lt_onSuccess context result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rw [(identifier_ok_state_shape context identifierResult).choose_spec.2.2.2]
        simp

/-- Selector-name success never moves the parser cursor backwards. -/
theorem selectorName_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (selectorName context) := by
  intro input selector next result
  exact Nat.le_of_lt (selectorName_cursor_lt_onSuccess context result)

end Solcore.Syntax.Parser
