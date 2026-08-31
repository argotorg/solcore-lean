import Solcore.Syntax.Parser.Yul.LeafProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

structure YulNameSequence where
  span : SourceSpan
  names : NonemptyList YulIdentifier

def finishYulNames (first last : YulIdentifier)
    (tailRev : List YulIdentifier) (state : State) : Reply YulNameSequence :=
  .ok {
    span := SourceSpan.cover first.span last.span
    names := { head := first, tail := tailRev.reverse }
  } state

def yulNamesTail (first : YulIdentifier) :
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

namespace YulParsedBlock

/-- A Yul block and every retained statement belong to one input file. -/
def ValidFor (statementValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (block : YulParsedBlock) : Prop :=
  block.span.ValidFor file ∧
    ∀ statement ∈ block.body, statementValid file statement

end YulParsedBlock

private def closeYulBlock (opening : Token)
    (bodyRev : List YulStmt) : Parser YulParsedBlock := fun state =>
  match symbol .rightBrace .yulStatement state with
  | .ok closing next => .ok {
      span := SourceSpan.cover opening.span closing.span
      body := bodyRev.reverse
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

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

private theorem closeYulBlock_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (opening : Token) (bodyRev : List YulStmt) (state : State)
    (openingIndex : Nat) (stateValid : state.ValidFor)
    (openingValid : opening.span.ValidFor state.file)
    (bodyValid : ∀ item ∈ bodyRev, statementValid state.file item)
    (openingFound : state.tokens[openingIndex]? = some opening)
    (openingBeforeCursor : openingIndex < state.cursor) :
    (closeYulBlock opening bodyRev state).ValidFor state
      (YulParsedBlock.ValidFor statementValid) := by
  unfold closeYulBlock
  cases closingResult : symbol .rightBrace .yulStatement state with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .rightBrace .yulStatement state stateValid
      rw [closingResult] at valid
      simpa only [closingResult, Reply.ValidFor] using valid
  | ok closing next =>
      have closingValid :=
        symbol_validFor .rightBrace .yulStatement state stateValid
      rw [closingResult] at closingValid
      have closingShape :=
        symbol_ok_state_shape .rightBrace .yulStatement closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingBeforeClosing :=
        stateValid.token_end_le_token_start_of_getElem?_lt
          openingFound closingFound openingBeforeCursor
      have closingSpanValid : closing.span.ValidFor state.file := by
        simpa only [Located.ValidFor] using closingValid.1
      unfold Reply.ValidFor YulParsedBlock.ValidFor
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingSpanValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)), ?_⟩,
        closingValid.2.1, closingValid.2.2⟩
      intro item member
      exact bodyValid item (by simpa using member)

private theorem yulBlockItems_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (statement : Parser YulStmt)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) :
    ∀ fuel bodyRev state openingIndex,
      state.ValidFor →
      opening.span.ValidFor state.file →
      (∀ item ∈ bodyRev, statementValid state.file item) →
      state.tokens[openingIndex]? = some opening →
      openingIndex < state.cursor →
      (yulBlockItems statement opening fuel bodyRev state).ValidFor state
        (YulParsedBlock.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev state openingIndex stateValid openingValid bodyValid
        openingFound openingBeforeCursor
      unfold yulBlockItems
      split
      · exact closeYulBlock_validFor statementValid opening bodyRev state
          openingIndex stateValid openingValid bodyValid openingFound
          openingBeforeCursor
      · split
        · cases closingResult : symbol .rightBrace .yulStatement state with
          | invariant error => trivial
          | reject failure rejected =>
              have valid :=
                symbol_validFor .rightBrace .yulStatement state stateValid
              rw [closingResult] at valid
              exact valid
          | ok closing next => simp only [Reply.ValidFor]
        · cases itemResult : statement state with
          | invariant error => trivial
          | reject failure rejected =>
              have valid := statementContract state stateValid
              rw [itemResult] at valid
              exact valid
          | ok item next =>
              have itemValid := statementContract state stateValid
              rw [itemResult] at itemValid
              simp only
              split
              · have tokensEq := statementShape state item next itemResult
                have recursive := inductionHypothesis (item :: bodyRev) next
                  openingIndex itemValid.2.1
                  (by simpa [itemValid.2.2] using openingValid)
                  (by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | member
                    · simpa [itemValid.2.2] using itemValid.1
                    · simpa [itemValid.2.2] using
                        bodyValid retained member)
                  (by simpa [tokensEq] using openingFound)
                  (Nat.lt_trans openingBeforeCursor (by assumption))
                exact recursive.of_file_eq itemValid.2.2
              · trivial

/-- A valid, token-preserving statement parser lifts through Yul braces. -/
theorem yulBlock_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (statement : Parser YulStmt)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    (yulBlock statement).ValidFor
      (YulParsedBlock.ValidFor statementValid) := by
  intro input inputValid
  unfold yulBlock
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftBrace .yulStatement input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid :=
        symbol_validFor .leftBrace .yulStatement input inputValid
      rw [openingResult] at openingValid
      have openingShape :=
        symbol_ok_state_shape .leftBrace .yulStatement openingResult
      have openingFound :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have recursive := yulBlockItems_validFor statementValid statement
        statementContract statementShape opening
        (afterOpening.remainingCount + 1) [] afterOpening input.cursor
        openingValid.2.1
        (by simpa only [Located.ValidFor, openingValid.2.2] using
          openingValid.1)
        (by simp) (by simpa [openingShape.2] using openingFound)
        (by rw [openingShape.2]; simp)
      exact recursive.of_file_eq openingValid.2.2

private theorem closeYulBlock_preservesTokenWindow (opening : Token)
    (bodyRev : List YulStmt) :
    Parser.PreservesTokenWindow (closeYulBlock opening bodyRev) := by
  intro input
  unfold closeYulBlock
  have closingShape :=
    symbol_preservesTokenWindow .rightBrace .yulStatement input
  cases closingResult : symbol .rightBrace .yulStatement input with
  | ok closing next => rw [closingResult] at closingShape; exact closingShape
  | reject failure rejected =>
      rw [closingResult] at closingShape
      exact closingShape
  | invariant error => trivial

private theorem yulBlockItems_preservesTokenWindow
    (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement)
    (opening : Token) : ∀ fuel bodyRev,
      Parser.PreservesTokenWindow
        (yulBlockItems statement opening fuel bodyRev) := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev input
      unfold yulBlockItems
      split
      · exact closeYulBlock_preservesTokenWindow opening bodyRev input
      · split
        · have closingShape :=
            symbol_preservesTokenWindow .rightBrace .yulStatement input
          cases closingResult : symbol .rightBrace .yulStatement input with
          | ok closing next => trivial
          | reject failure rejected =>
              rw [closingResult] at closingShape
              exact closingShape
          | invariant error => trivial
        · have itemShape := statementShape input
          cases itemResult : statement input with
          | ok item next =>
              rw [itemResult] at itemShape
              change (if next.cursor > input.cursor then
                yulBlockItems statement opening fuel (item :: bodyRev) next
                else .invariant (.noProgress .yul next.currentSpan)
                ).PreservesTokenWindow input
              split
              · exact (inductionHypothesis (item :: bodyRev) next).trans
                  itemShape
              · trivial
          | reject failure rejected =>
              rw [itemResult] at itemShape
              exact itemShape
          | invariant error => trivial

/-- Yul-block parsing preserves the nested parser's ordinary token window. -/
theorem yulBlock_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulBlock statement) := by
  intro input
  unfold yulBlock
  have openingShape :=
    symbol_preservesTokenWindow .leftBrace .yulStatement input
  cases openingResult : symbol .leftBrace .yulStatement input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (yulBlockItems_preservesTokenWindow statement statementShape
        opening (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

private theorem closeYulBlock_ok_state_shape (opening : Token)
    (bodyRev : List YulStmt) {input next : State} {body : YulParsedBlock}
    (result : closeYulBlock opening bodyRev input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
      body.span.startByte = opening.span.startByte := by
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      have shape :=
        symbol_ok_state_shape .rightBrace .yulStatement closingResult
      exact ⟨by rw [shape.2], by rw [shape.2]; simp, rfl⟩
  | reject failure rejected => simp [closingResult] at result
  | invariant error => simp [closingResult] at result

private theorem yulBlockItems_ok_state_shape (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) :
    ∀ fuel bodyRev input body next,
      yulBlockItems statement opening fuel bodyRev input = .ok body next →
      next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
        body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result
      unfold yulBlockItems at result
      split at result
      · exact closeYulBlock_ok_state_shape opening bodyRev result
      · split at result
        · cases closingResult : symbol .rightBrace .yulStatement input <;>
            simp [closingResult] at result
        · cases itemResult : statement input with
          | ok item afterItem =>
              simp only [itemResult] at result
              split at result
              · have recursive := inductionHypothesis (item :: bodyRev)
                    afterItem body next result
                exact ⟨recursive.1.trans
                    (statementShape input item afterItem itemResult),
                  Nat.lt_trans (by assumption) recursive.2.1,
                  recursive.2.2⟩
              · contradiction
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result

/-- Successful Yul-block parsing exposes its opening and total progress. -/
theorem yulBlock_ok_state_shape (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body next) :
    ∃ opening, input.peek? = some opening ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
      opening.span.startByte = body.span.startByte := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have recursive := yulBlockItems_ok_state_shape statement statementShape
        opening (afterOpening.remainingCount + 1) [] afterOpening body next
          result
      have openingShape :=
        symbol_ok_state_shape .leftBrace .yulStatement openingResult
      exact ⟨opening, openingShape.1,
        recursive.1.trans (by rw [openingShape.2]),
        Nat.lt_trans (by rw [openingShape.2]; simp) recursive.2.1,
        recursive.2.2.symm⟩
  | reject failure rejected => simp [openingResult] at result
  | invariant error => simp [openingResult] at result

/-- Yul-block success preserves the immutable token carrier. -/
theorem yulBlock_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulBlock statement) := by
  intro input body next result
  exact (yulBlock_ok_state_shape statement statementShape result).choose_spec.2.1

/-- Every successful Yul block consumes both braces. -/
theorem yulBlock_cursor_lt_onSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body next) :
    input.cursor < next.cursor :=
  (yulBlock_ok_state_shape statement statementShape result).choose_spec.2.2.1

/-- Successful Yul-block parsing never rewinds the token cursor. -/
theorem yulBlock_cursorMonotoneOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulBlock statement) := by
  intro input body next result
  exact Nat.le_of_lt (yulBlock_cursor_lt_onSuccess statement statementShape result)

/-- A successful Yul block starts at its opening brace token. -/
theorem yulBlock_startsAtCurrentTokenOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.StartsAtCurrentTokenOnSuccess (yulBlock statement) (·.span) := by
  intro input body next result
  rcases yulBlock_ok_state_shape statement statementShape result with
    ⟨opening, found, _tokens, _progress, start⟩
  exact ⟨opening, found, start⟩

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

private theorem yulNamesTail_preservesTokenWindow (first : YulIdentifier) :
    ∀ fuel last tailRev, Parser.PreservesTokenWindow
      (yulNamesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; change True; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold yulNamesTail
      split
      · have commaShape :=
          symbol_preservesTokenWindow .comma .yulStatement input
        cases commaResult : symbol .comma .yulStatement input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [commaResult] at commaShape
            exact commaShape
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            have nameShape := yulName_preservesTokenWindow afterComma
            cases nameResult : yulName afterComma with
            | invariant error => simp only [nameResult,
                Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [nameResult] at nameShape
                simpa only [commaResult, nameResult, Reply.PreservesTokenWindow]
                  using nameShape.trans commaShape
            | ok name next =>
                rw [nameResult] at nameShape
                simpa only [commaResult, nameResult, Reply.PreservesTokenWindow]
                  using (inductionHypothesis name (name :: tailRev) next).trans
                    (nameShape.trans commaShape)
      · exact ⟨rfl, rfl⟩

/-- Yul-name parsing preserves every ordinary token window. -/
theorem yulNames_preservesTokenWindow :
    Parser.PreservesTokenWindow yulNames := by
  intro input
  unfold yulNames
  have firstShape := yulName_preservesTokenWindow input
  cases firstResult : yulName input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first next =>
      rw [firstResult] at firstShape
      exact (yulNamesTail_preservesTokenWindow first
        (next.remainingCount + 1) first [] next).trans firstShape

/-- Yul-name sequence success never moves the cursor backwards. -/
theorem yulNames_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulNames := by
  intro input names next result
  exact Nat.le_of_lt (yulNames_ok_state_shape result).choose_spec.2.2.2

/-- A successful Yul-name sequence starts at its first name token. -/
theorem yulNames_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulNames (·.span) := by
  intro input names next result
  rcases yulNames_ok_state_shape result with
    ⟨first, found, start, _tokens, _progress⟩
  exact ⟨first, found, start⟩

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

/-- Yul parameter lists preserve every ordinary token window. -/
theorem yulParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow yulParameters := by
  exact delimited_preservesTokenWindow .leftParen .rightParen true
    yulName .yulStatement .yul yulName_preservesTokenWindow

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

/-- A successful Yul parameter list starts at its opening parenthesis. -/
theorem yulParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulParameters (·.span) :=
  delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul

end Solcore.Syntax.Parser
