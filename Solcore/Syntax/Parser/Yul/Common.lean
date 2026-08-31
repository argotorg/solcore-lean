import Solcore.Syntax.Parser.Yul.LeafProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

structure YulNameSequence where
  span : SourceSpan
  names : NonemptyList YulIdentifier

private def finishYulNames (first last : YulIdentifier)
    (tailRev : List YulIdentifier) (state : State) : Reply YulNameSequence :=
  .ok {
    span := SourceSpan.cover first.span last.span
    names := { head := first, tail := tailRev.reverse }
  } state

private def yulNamesTail (first : YulIdentifier) :
    Nat → YulIdentifier → List YulIdentifier → State → Reply YulNameSequence
  | 0, _, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .comma then
        match symbol .comma .yulStatement state with
        | .ok _ afterComma =>
            match yulName afterComma with
            | .ok name next =>
                yulNamesTail first fuel name (name :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishYulNames first last tailRev state

/-- Parse a nonempty, non-trailing comma-separated Yul name sequence. -/
def yulNames : Parser YulNameSequence := fun state =>
  match yulName state with
  | .ok first next =>
      yulNamesTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

structure YulParsedBlock where
  span : SourceSpan
  body : List YulStmt

private def closeYulBlock (opening : Token)
    (bodyRev : List YulStmt) : Parser YulParsedBlock := do
  let closing ← symbol .rightBrace .yulStatement
  pure {
    span := SourceSpan.cover opening.span closing.span
    body := bodyRev.reverse
  }

private def yulBlockItems (statement : Parser YulStmt)
    (opening : Token) : Nat → List YulStmt → State → Reply YulParsedBlock
  | 0, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, bodyRev, state =>
      if isSymbol state .rightBrace then
        closeYulBlock opening bodyRev state
      else if state.atEnd then
        match symbol .rightBrace .yulStatement state with
        | .ok _ _ => .invariant (.noProgress .yul state.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        let before := state.cursor
        match statement state with
        | .ok value next =>
            if next.cursor > before then
              yulBlockItems statement opening fuel (value :: bodyRev) next
            else
              .invariant (.noProgress .yul next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error

/-- Parse braces and a progress-checked list of inline-Yul statements. -/
def yulBlock (statement : Parser YulStmt) : Parser YulParsedBlock := fun state =>
  match symbol .leftBrace .yulStatement state with
  | .ok opening next =>
      yulBlockItems statement opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Empty/trailing parameter list used by inline-Yul function definitions. -/
def yulParameters : Parser (DelimitedList YulIdentifier) :=
  delimited .leftParen .rightParen true yulName .yulStatement .yul

namespace YulNameSequence

/-- The sequence range and every retained Yul name belong to one input file. -/
def ValidFor (file : SourceFile) (values : YulNameSequence) : Prop :=
  values.span.ValidFor file ∧
    ∀ name ∈ values.names.toList, name.span.ValidFor file

end YulNameSequence

private theorem yulNamesTail_validFor (first : YulIdentifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ name ∈ tailRev, name.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (yulNamesTail first fuel last tailRev state).ValidFor state
        YulNameSequence.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold yulNamesTail
      split
      · cases commaResult : symbol .comma .yulStatement state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .comma .yulStatement state stateValid
            rw [commaResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok comma afterComma =>
            have commaValid :=
              symbol_validFor .comma .yulStatement state stateValid
            rw [commaResult] at commaValid
            have commaShape :=
              symbol_ok_state_shape .comma .yulStatement commaResult
            simp only
            cases nameResult : yulName afterComma with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have valid := yulName_validFor afterComma commaValid.2.1
                rw [nameResult] at valid
                exact valid.of_file_eq commaValid.2.2
            | ok name next =>
                have nameValid := yulName_validFor afterComma commaValid.2.1
                rw [nameResult] at nameValid
                rcases yulName_ok_state_shape nameResult with
                  ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
                have nameFoundInState :
                    state.tokens[state.cursor + 1]? = some nameToken := by
                  have foundAtCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some nameFound
                  simpa [commaShape.2] using foundAtCursor
                have firstEndBeforeNameStart :
                    first.span.endByte ≤ name.span.startByte := by
                  have ordered :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      firstFound nameFoundInState
                      (Nat.lt_of_lt_of_le firstBeforeCursor
                        (Nat.le_add_right state.cursor 1))
                  simpa [firstSpan, nameSpan] using ordered
                have nameSpanValid : name.span.ValidFor next.file := by
                  have valid : name.span.ValidFor afterComma.file := by
                    simpa only [Located.ValidFor] using nameValid.1
                  simpa [nameValid.2.2] using valid
                apply (inductionHypothesis name (name :: tailRev) next
                  firstIndex firstToken nameValid.2.1
                  (by simpa [nameValid.2.2, commaValid.2.2] using firstValid)
                  nameSpanValid _ _ _ firstSpan _).of_file_eq
                  (nameValid.2.2.trans commaValid.2.2)
                · intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact nameSpanValid
                  · simpa [nameValid.2.2, commaValid.2.2] using
                      tailValid item member
                · exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeNameStart nameSpanValid.2.1)
                · simpa [nameTokens, commaShape.2] using firstFound
                · rw [nameCursor, commaShape.2]
                  exact Nat.lt_trans
                    (Nat.lt_trans firstBeforeCursor (Nat.lt_succ_self _))
                    (Nat.lt_succ_self _)
      · unfold finishYulNames Reply.ValidFor YulNameSequence.ValidFor
        refine ⟨⟨SourceSpan.cover_validFor firstValid lastValid
          firstBeforeLast, ?_⟩, stateValid, rfl⟩
        intro name member
        simp only [NonemptyList.toList, List.mem_cons,
          List.mem_reverse] at member
        rcases member with rfl | member
        · exact firstValid
        · exact tailValid name member

/-- Yul-name sequences preserve their covering and component provenance. -/
theorem yulNames_validFor :
    yulNames.ValidFor YulNameSequence.ValidFor := by
  intro input inputValid
  unfold yulNames
  cases firstResult : yulName input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := yulName_validFor input inputValid
      rw [firstResult] at valid
      exact valid
  | ok first next =>
      have firstValid := yulName_validFor input inputValid
      rw [firstResult] at firstValid
      rcases yulName_ok_state_shape firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have foundNext : next.tokens[input.cursor]? = some firstToken := by
        have found := State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using found
      have spanValid : first.span.ValidFor next.file := by
        have valid : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using valid
      exact (yulNamesTail_validFor first (next.remainingCount + 1) first []
        next input.cursor firstToken firstValid.2.1 spanValid spanValid
        (by simp) spanValid.2.1 foundNext firstSpan
        (by rw [firstCursor]; simp)).of_file_eq firstValid.2.2

private theorem yulNamesTail_ok_state_shape (first : YulIdentifier) :
    ∀ fuel last tailRev input names next,
      yulNamesTail first fuel last tailRev input = .ok names next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        names.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input names next result
      unfold yulNamesTail at result
      split at result
      · cases commaResult : symbol .comma .yulStatement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            cases nameResult : yulName afterComma with
            | invariant error => simp [nameResult] at result
            | reject failure rejected => simp [nameResult] at result
            | ok name afterName =>
                simp only [nameResult] at result
                have recursive := inductionHypothesis name
                  (name :: tailRev) afterName names next result
                have commaShape :=
                  symbol_ok_state_shape .comma .yulStatement commaResult
                rcases yulName_ok_state_shape nameResult with
                  ⟨_token, _found, _span, nameTokens, nameCursor⟩
                refine ⟨recursive.1.trans
                    (nameTokens.trans (by rw [commaShape.2])), ?_,
                  recursive.2.2⟩
                apply Nat.le_trans _ recursive.2.1
                rw [nameCursor, commaShape.2]
                exact Nat.le_trans (Nat.le_add_right input.cursor 1)
                  (Nat.le_add_right (input.cursor + 1) 1)
      · unfold finishYulNames at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩

/-- Successful Yul-name parsing starts at the first token and makes progress. -/
theorem yulNames_ok_state_shape {input next : State}
    {names : YulNameSequence} (result : yulNames input = .ok names next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = names.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := yulNamesTail_ok_state_shape first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
      rcases yulName_ok_state_shape firstResult with
        ⟨firstToken, found, span, tokens, cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens, ?_⟩
      · exact (congrArg (fun sourceSpan : SourceSpan =>
          sourceSpan.startByte) span).trans tailShape.2.2.symm
      · exact Nat.lt_of_lt_of_le (by rw [cursor]; simp) tailShape.2.1

/-- Yul-name sequence success preserves the immutable token carrier. -/
theorem yulNames_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulNames := by
  intro input names next result
  exact (yulNames_ok_state_shape result).choose_spec.2.2.1

/-- Yul-name sequence success never moves the cursor backwards. -/
theorem yulNames_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulNames := by
  intro input names next result
  exact Nat.le_of_lt (yulNames_ok_state_shape result).choose_spec.2.2.2

/-- Yul parameter lists preserve their delimiter and element provenance. -/
theorem yulParameters_validFor :
    yulParameters.ValidFor (DelimitedList.ValidFor Located.ValidFor) := by
  exact delimited_validFor Located.ValidFor .leftParen .rightParen true
    yulName .yulStatement .yul yulName_validFor
      yulName_preservesTokensOnSuccess

/-- Yul parameter-list success preserves the immutable token carrier. -/
theorem yulParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulParameters := by
  exact delimited_preservesTokensOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul yulName_preservesTokensOnSuccess

/-- Every successful Yul parameter list consumes both delimiters. -/
theorem yulParameters_cursor_lt_onSuccess {input next : State}
    {parameters : DelimitedList YulIdentifier}
    (result : yulParameters input = .ok parameters next) :
    input.cursor < next.cursor := by
  exact delimitedWithPolicy_cursor_lt_onSuccess .leftParen .rightParen true
    true yulName .yulStatement .yul result

/-- Yul parameter-list success never moves the cursor backwards. -/
theorem yulParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulParameters := by
  exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul

end Solcore.Syntax.Parser
