import Solcore.Syntax.Parser.Blocks
import Solcore.Syntax.DeclarativeCoreBlockGrammar
import Solcore.Syntax.DeclarativeCoreBlockTailTraceGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.State
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ExpressionValidity

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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
