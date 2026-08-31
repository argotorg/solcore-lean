import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.Parser.Validity
import Solcore.Syntax.Parser.StateCursorProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def closeDelimited {α : Type} (opening : Token)
    (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) : Parser (DelimitedList α) := fun state =>
  match symbol closing context state with
  | .ok token next => .ok {
      span := SourceSpan.cover opening.span token.span
      elements := elementsRev.reverse
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private theorem closeDelimited_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) (state : State) (openingIndex : Nat)
    (stateValid : state.ValidFor)
    (openingValid : opening.span.ValidFor state.file)
    (elementsValid : ∀ element ∈ elementsRev,
      elementValid state.file element)
    (openingFound : state.tokens[openingIndex]? = some opening)
    (openingBeforeCursor : openingIndex < state.cursor) :
    (closeDelimited opening closing context elementsRev state).ValidFor
      state (DelimitedList.ValidFor elementValid) := by
  unfold closeDelimited
  cases closingResult : symbol closing context state with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have closingValid := symbol_validFor closing context state stateValid
      rw [closingResult] at closingValid
      simpa only [Reply.ValidFor] using closingValid
  | ok closingToken next =>
      have closingValid := symbol_validFor closing context state stateValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape closing context closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingBeforeClosing :=
        stateValid.token_end_le_token_start_of_getElem?_lt
          openingFound closingFound openingBeforeCursor
      have closingSpanValid : closingToken.span.ValidFor state.file := by
        simpa only [Located.ValidFor] using closingValid.1
      have coverValid :
          (SourceSpan.cover opening.span closingToken.span).ValidFor state.file := by
        apply SourceSpan.cover_validFor openingValid closingSpanValid
        exact Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)
      simp only
      unfold Reply.ValidFor DelimitedList.ValidFor
      refine ⟨⟨coverValid, ?_⟩, closingValid.2.1, closingValid.2.2⟩
      intro element member
      exact elementsValid element (by simpa using member)

private def afterDelimitedElement {α : Type}
    (element : Parser α) (closing : Symbol)
    (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase)
    (opening : Token) :
    Nat → List α → State → Reply (DelimitedList α)
  | 0, _, state => .invariant (.fuelExhausted phase state.currentSpan)
  | fuel + 1, elementsRev, state =>
      if isSymbol state .comma then
        match symbol .comma context state with
        | .ok _ afterComma =>
            if allowTrailing && isSymbol afterComma closing then
              closeDelimited opening closing context elementsRev afterComma
            else
              let before := afterComma.cursor
              match element afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    afterDelimitedElement element closing allowTrailing context phase opening
                      fuel (value :: elementsRev) next
                  else
                    .invariant (.noProgress phase next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else if isSymbol state closing then
        closeDelimited opening closing context elementsRev state
      else
        rejectAt state {
          head := .symbol .comma
          tail := [.symbol closing]
        } context

private theorem afterDelimitedElement_validFor {α : Type}
    (elementValid : SourceFile → α → Prop) (element : Parser α)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev state openingIndex,
      state.ValidFor →
      opening.span.ValidFor state.file →
      (∀ value ∈ elementsRev, elementValid state.file value) →
      state.tokens[openingIndex]? = some opening →
      openingIndex < state.cursor →
      (afterDelimitedElement element closing allowTrailing context phase opening
        fuel elementsRev state).ValidFor state
          (DelimitedList.ValidFor elementValid) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev state openingIndex stateValid openingValid
        elementsValid openingFound openingBeforeCursor
      trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev state openingIndex stateValid openingValid
        elementsValid openingFound openingBeforeCursor
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have commaValid := symbol_validFor .comma context state stateValid
            rw [commaResult] at commaValid
            simpa only [Reply.ValidFor] using commaValid
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma context state stateValid
            rw [commaResult] at commaValid
            have commaShape := symbol_ok_state_shape .comma context commaResult
            have openingValidAfterComma :
                opening.span.ValidFor afterComma.file := by
              simpa [commaValid.2.2] using openingValid
            have elementsValidAfterComma : ∀ value ∈ elementsRev,
                elementValid afterComma.file value := by
              intro value member
              simpa [commaValid.2.2] using elementsValid value member
            have openingFoundAfterComma :
                afterComma.tokens[openingIndex]? = some opening := by
              simpa [commaShape.2] using openingFound
            have openingBeforeAfterComma : openingIndex < afterComma.cursor := by
              rw [commaShape.2]
              exact Nat.lt_of_lt_of_le openingBeforeCursor
                (Nat.le_add_right state.cursor 1)
            simp only
            split
            · have closed := closeDelimited_validFor elementValid opening
                closing context elementsRev afterComma openingIndex
                commaValid.2.1 openingValidAfterComma
                elementsValidAfterComma openingFoundAfterComma
                openingBeforeAfterComma
              exact closed.of_file_eq commaValid.2.2
            · cases elementResult : element afterComma with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  have valueValid := elementContract afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  simpa only [Reply.ValidFor] using
                    valueValid.of_file_eq commaValid.2.2
              | ok value next =>
                  have valueValid := elementContract afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  have tokensEq := elementShape afterComma value next elementResult
                  simp only
                  split
                  · have openingValidNext :
                        opening.span.ValidFor next.file := by
                      simpa [valueValid.2.2] using openingValidAfterComma
                    have valueValidNext : elementValid next.file value := by
                      simpa [valueValid.2.2] using valueValid.1
                    have elementsValidNext : ∀ item ∈ value :: elementsRev,
                        elementValid next.file item := by
                      intro item member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact valueValidNext
                      · simpa [valueValid.2.2] using
                          elementsValidAfterComma item member
                    have openingFoundNext :
                        next.tokens[openingIndex]? = some opening := by
                      simpa [tokensEq] using openingFoundAfterComma
                    have recursiveValid := inductionHypothesis
                      (value :: elementsRev) next openingIndex valueValid.2.1
                      openingValidNext elementsValidNext openingFoundNext
                      (Nat.lt_trans openingBeforeAfterComma (by assumption))
                    exact recursiveValid.of_file_eq
                      (valueValid.2.2.trans commaValid.2.2)
                  · simp only [Reply.ValidFor]
      · split
        · exact closeDelimited_validFor elementValid opening closing context
            elementsRev state openingIndex stateValid openingValid
            elementsValid openingFound openingBeforeCursor
        · unfold rejectAt Reply.ValidFor
          exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩

/--
Parse a comma-separated delimited sequence. Empty and trailing-comma policy is
selected by the caller; every accepted element must advance the cursor.
-/
def delimitedWithPolicy {α : Type} (opening closing : Symbol)
    (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) := fun state =>
  match symbol opening context state with
  | .ok openingToken afterOpening =>
      if allowEmpty && isSymbol afterOpening closing then
        closeDelimited openingToken closing context [] afterOpening
      else
        let before := afterOpening.cursor
        match element afterOpening with
        | .ok value next =>
            if next.cursor > before then
              afterDelimitedElement element closing allowTrailing context phase openingToken
                (afterOpening.remainingCount + 1) [value] next
            else
              .invariant (.noProgress phase next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- A valid, token-preserving element parser lifts through delimiter policy. -/
theorem delimitedWithPolicy_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase).ValidFor (DelimitedList.ValidFor elementValid) := by
  intro input inputValid
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      simpa only [Reply.ValidFor] using openingValid
  | ok openingToken afterOpening =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      have openingShape := symbol_ok_state_shape opening context openingResult
      have openingSpanValid : openingToken.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using openingValid.1
      have openingFoundInput :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingSpanValidAfter :
          openingToken.span.ValidFor afterOpening.file := by
        simpa [openingValid.2.2] using openingSpanValid
      have openingFoundAfter :
          afterOpening.tokens[input.cursor]? = some openingToken := by
        simpa [openingShape.2] using openingFoundInput
      have openingBeforeAfter : input.cursor < afterOpening.cursor := by
        rw [openingShape.2]
        simp
      simp only
      split
      · have closed := closeDelimited_validFor elementValid openingToken
          closing context [] afterOpening input.cursor openingValid.2.1
          openingSpanValidAfter (by simp) openingFoundAfter openingBeforeAfter
        exact closed.of_file_eq openingValid.2.2
      · cases elementResult : element afterOpening with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valueValid := elementContract afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            simpa only [Reply.ValidFor] using
              valueValid.of_file_eq openingValid.2.2
        | ok value next =>
            have valueValid := elementContract afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            have tokensEq := elementShape afterOpening value next elementResult
            simp only
            split
            · have openingSpanValidNext :
                  openingToken.span.ValidFor next.file := by
                simpa [valueValid.2.2] using openingSpanValidAfter
              have valueValidNext : elementValid next.file value := by
                simpa [valueValid.2.2] using valueValid.1
              have openingFoundNext :
                  next.tokens[input.cursor]? = some openingToken := by
                simpa [tokensEq] using openingFoundAfter
              have tailValid := afterDelimitedElement_validFor elementValid
                element elementContract elementShape closing allowTrailing
                context phase openingToken (afterOpening.remainingCount + 1)
                [value] next input.cursor valueValid.2.1
                openingSpanValidNext (by
                  intro item member
                  simp only [List.mem_singleton] at member
                  subst item
                  exact valueValidNext)
                openingFoundNext
                (Nat.lt_trans openingBeforeAfter (by assumption))
              exact tailValid.of_file_eq
                (valueValid.2.2.trans openingValid.2.2)
            · simp only [Reply.ValidFor]

/-- Parse a delimited list whose final comma is accepted. -/
def delimited {α : Type} (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) :=
  delimitedWithPolicy opening closing allowEmpty true element context phase

/-- Trailing-comma lists preserve delimiter and element provenance. -/
theorem delimited_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimited opening closing allowEmpty element context phase).ValidFor
      (DelimitedList.ValidFor elementValid) := by
  exact delimitedWithPolicy_validFor elementValid opening closing allowEmpty
    true element context phase elementContract elementShape

/-- Parse a delimited list whose final comma is rejected. -/
def delimitedNoTrailing {α : Type} (opening closing : Symbol)
    (allowEmpty : Bool) (element : Parser α) (context : ParseContext)
    (phase : ParserPhase) : Parser (DelimitedList α) :=
  delimitedWithPolicy opening closing allowEmpty false element context phase

/-- Non-trailing-comma lists preserve delimiter and element provenance. -/
theorem delimitedNoTrailing_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimitedNoTrailing opening closing allowEmpty element context phase).ValidFor
      (DelimitedList.ValidFor elementValid) := by
  exact delimitedWithPolicy_validFor elementValid opening closing allowEmpty
    false element context phase elementContract elementShape

private theorem closeDelimited_preservesTokensOnSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) :
    Parser.PreservesTokensOnSuccess
      (closeDelimited opening closing context elementsRev) := by
  intro input values next result
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      exact (symbol_ok_state_shape closing context closingResult).2 ▸ rfl
  | reject failure rejected =>
      simp only [closingResult] at result
      contradiction
  | invariant error =>
      simp only [closingResult] at result
      contradiction

private theorem afterDelimitedElement_preservesTokensOnSuccess {α : Type}
    (element : Parser α) (elementShape : Parser.PreservesTokensOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext)
    (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.PreservesTokensOnSuccess
        (afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp only [afterDelimitedElement] at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaTokens : afterComma.tokens = input.tokens :=
              (symbol_ok_state_shape .comma context commaResult).2 ▸ rfl
            split at result
            · exact (closeDelimited_preservesTokensOnSuccess opening closing
                context elementsRev afterComma values next result).trans
                commaTokens
            · cases elementResult : element afterComma with
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact (inductionHypothesis (value :: elementsRev)
                      afterElement values next result).trans
                      ((elementShape afterComma value afterElement
                        elementResult).trans commaTokens)
                  · contradiction
              | reject failure rejected =>
                  simp only [elementResult] at result
                  contradiction
              | invariant error =>
                  simp only [elementResult] at result
                  contradiction
        | reject failure rejected =>
            simp only [commaResult] at result
            contradiction
        | invariant error =>
            simp only [commaResult] at result
            contradiction
      · split at result
        · exact closeDelimited_preservesTokensOnSuccess opening closing context
            elementsRev input values next result
        · unfold rejectAt at result
          contradiction

/-- Delimited parsing never replaces or reorders the immutable token carrier. -/
theorem delimitedWithPolicy_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next result
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      simp only [openingResult] at result
      have openingTokens : afterOpening.tokens = input.tokens :=
        (symbol_ok_state_shape opening context openingResult).2 ▸ rfl
      split at result
      · exact (closeDelimited_preservesTokensOnSuccess openingToken closing
          context [] afterOpening values next result).trans openingTokens
      · cases elementResult : element afterOpening with
        | ok value afterElement =>
            simp only [elementResult] at result
            split at result
            · exact (afterDelimitedElement_preservesTokensOnSuccess element
                elementShape closing allowTrailing context phase openingToken
                (afterOpening.remainingCount + 1) [value] afterElement values
                next result).trans
                ((elementShape afterOpening value afterElement
                  elementResult).trans openingTokens)
            · contradiction
        | reject failure rejected =>
            simp only [elementResult] at result
            contradiction
        | invariant error =>
            simp only [elementResult] at result
            contradiction
  | reject failure rejected =>
      simp only [openingResult] at result
      contradiction
  | invariant error =>
      simp only [openingResult] at result
      contradiction

theorem delimited_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesTokensOnSuccess opening closing allowEmpty true
    element context phase elementShape

theorem delimitedNoTrailing_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesTokensOnSuccess opening closing allowEmpty false
    element context phase elementShape

private theorem closeDelimited_cursor_lt_onSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.cursor < next.cursor := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      rw [(symbol_ok_state_shape closing context closingResult).2]
      simp
  | reject failure rejected =>
      simp only [closingResult] at result
      contradiction
  | invariant error =>
      simp only [closingResult] at result
      contradiction

private theorem afterDelimitedElement_cursor_lt_onSuccess {α : Type}
    (element : Parser α) (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing allowTrailing context phase opening
          fuel elementsRev input = .ok values next →
        input.cursor < next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp only [afterDelimitedElement] at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaProgress : input.cursor < afterComma.cursor := by
              rw [(symbol_ok_state_shape .comma context commaResult).2]
              simp
            split at result
            · exact Nat.lt_trans commaProgress
                (closeDelimited_cursor_lt_onSuccess opening closing context
                  elementsRev result)
            · cases elementResult : element afterComma with
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact Nat.lt_trans commaProgress
                      (Nat.lt_trans (by assumption)
                        (inductionHypothesis (value :: elementsRev) afterElement
                          values next result))
                  · contradiction
              | reject failure rejected =>
                  simp only [elementResult] at result
                  contradiction
              | invariant error =>
                  simp only [elementResult] at result
                  contradiction
        | reject failure rejected =>
            simp only [commaResult] at result
            contradiction
        | invariant error =>
            simp only [commaResult] at result
            contradiction
      · split at result
        · exact closeDelimited_cursor_lt_onSuccess opening closing context
            elementsRev result
        · unfold rejectAt at result
          contradiction

/-- A successful delimited parser consumes at least its opening and closing tokens. -/
theorem delimitedWithPolicy_cursor_lt_onSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    {input next : State} {values : DelimitedList α}
    (result : delimitedWithPolicy opening closing allowEmpty allowTrailing
      element context phase input = .ok values next) :
    input.cursor < next.cursor := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      simp only [openingResult] at result
      have openingProgress : input.cursor < afterOpening.cursor := by
        rw [(symbol_ok_state_shape opening context openingResult).2]
        simp
      split at result
      · exact Nat.lt_trans openingProgress
          (closeDelimited_cursor_lt_onSuccess openingToken closing context []
            result)
      · cases elementResult : element afterOpening with
        | ok value afterElement =>
            simp only [elementResult] at result
            split at result
            · exact Nat.lt_trans openingProgress
                (Nat.lt_trans (by assumption)
                  (afterDelimitedElement_cursor_lt_onSuccess element closing
                    allowTrailing context phase openingToken
                    (afterOpening.remainingCount + 1) [value] afterElement
                    values next result))
            · contradiction
        | reject failure rejected =>
            simp only [elementResult] at result
            contradiction
        | invariant error =>
            simp only [elementResult] at result
            contradiction
  | reject failure rejected =>
      simp only [openingResult] at result
      contradiction
  | invariant error =>
      simp only [openingResult] at result
      contradiction

theorem delimitedWithPolicy_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next result
  exact Nat.le_of_lt (delimitedWithPolicy_cursor_lt_onSuccess opening closing
    allowEmpty allowTrailing element context phase result)

theorem delimited_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_cursorMonotoneOnSuccess opening closing allowEmpty true
    element context phase

theorem delimitedNoTrailing_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_cursorMonotoneOnSuccess opening closing allowEmpty false
    element context phase

end Solcore.Syntax.Parser
