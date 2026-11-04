import Solcore.Syntax.Parser.Blocks
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.State
import Solcore.Syntax.ValidityBasics
import Solcore.Syntax.Validity
import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Soundness of the parsers of blocks and block capture: each success and each rejection has
its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Block
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.BalancedBlockCaptureCompletenessProperties
/-!
Every declarative balanced-brace scan is found by the executable capture.
The proof derives an explicit scan-distance bound before instantiating the
implementation with the active window's remaining-token fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace BlockInternals

private theorem peekOffset?_eq_some_of_tokenAt {state : State}
    {offset : Nat} {token : Token}
    (tokenAt : DeclarativeGrammar.TokenAt state.tokens state.window.endIndex
      (state.cursor + offset) token) :
    state.peekOffset? offset = some token := by
  unfold State.peekOffset?
  simp only [tokenAt.1, ↓reduceIte, tokenAt.2]

private theorem peek?_eq_some_of_tokenAt {state : State} {token : Token}
    (tokenAt : DeclarativeGrammar.TokenAt state.tokens state.window.endIndex
      state.cursor token) :
    state.peek? = some token := by
  unfold State.peek?
  simp only [tokenAt.1, ↓reduceIte, tokenAt.2]

private theorem tail_start_lt_capturedEnd {input : DeclarativeGrammar.Remainder}
    {depth offset : Nat} {closingSpan : SourceSpan} {capturedEnd : Nat}
    (scan : DeclarativeGrammar.BalancedBlockTailScans input depth offset
      closingSpan capturedEnd) :
    input.cursor + offset < capturedEnd := by
  induction scan with
  | close closingToken => omega
  | opening openingToken tail inductionHypothesis => omega
  | nestedClosing closingToken tail inductionHypothesis => omega
  | other tokenAt notOpening notClosing tail inductionHypothesis => omega

private theorem captureBlockTail_complete (state : State)
    (opening : Token) {depth offset : Nat} {closingSpan : SourceSpan}
    {capturedEnd : Nat}
    (scan : DeclarativeGrammar.BalancedBlockTailScans
      state.declarativeRemainder depth offset closingSpan capturedEnd) :
    ∀ fuel,
      capturedEnd ≤ state.cursor + offset + fuel →
      captureBlockTail state opening fuel depth offset = some {
        span := SourceSpan.cover opening.span closingSpan
        window := {
          endIndex := capturedEnd
          endByte := closingSpan.endByte
        }
      } := by
  simp only [State.declarativeRemainder] at scan
  induction scan with
  | @close offset closingSpan closingToken =>
      intro fuel adequate
      have startBefore : state.cursor + offset <
          state.cursor + offset + 1 := by omega
      change state.cursor + offset + 1 ≤
        state.cursor + offset + fuel at adequate
      have fuelPositive : 0 < fuel := by omega
      cases fuel with
      | zero => contradiction
      | succ fuel =>
          have found := peekOffset?_eq_some_of_tokenAt
            (state := state) (offset := offset) (by
              simpa only [State.declarativeRemainder] using closingToken)
          simp [captureBlockTail, found]
  | @opening depth offset capturedEnd openingSpan closingSpan openingToken tail
      inductionHypothesis =>
      intro fuel adequate
      have startBefore := tail_start_lt_capturedEnd tail
      dsimp only at startBefore
      have fuelPositive : 0 < fuel := by
        omega
      cases fuel with
      | zero => contradiction
      | succ fuel =>
          have found := peekOffset?_eq_some_of_tokenAt
            (state := state) (offset := offset) (by
              simpa only [State.declarativeRemainder] using openingToken)
          have recursive := inductionHypothesis fuel (by omega)
          simpa [captureBlockTail, found] using recursive
  | @nestedClosing depth offset capturedEnd nestedSpan closingSpan closingToken
      tail inductionHypothesis =>
      intro fuel adequate
      have startBefore := tail_start_lt_capturedEnd tail
      dsimp only at startBefore
      have fuelPositive : 0 < fuel := by
        omega
      cases fuel with
      | zero => contradiction
      | succ fuel =>
          have found := peekOffset?_eq_some_of_tokenAt
            (state := state) (offset := offset) (by
              simpa only [State.declarativeRemainder] using closingToken)
          have recursive := inductionHypothesis fuel (by omega)
          simpa [captureBlockTail, found] using recursive
  | @other depth offset capturedEnd token closingSpan tokenAt notOpening
      notClosing tail inductionHypothesis =>
      intro fuel adequate
      have startBefore := tail_start_lt_capturedEnd tail
      dsimp only at startBefore
      have fuelPositive : 0 < fuel := by
        omega
      cases fuel with
      | zero => contradiction
      | succ fuel =>
          have found := peekOffset?_eq_some_of_tokenAt
            (state := state) (offset := offset) (by
              simpa only [State.declarativeRemainder] using tokenAt)
          have recursive := inductionHypothesis fuel (by omega)
          rcases token with ⟨tokenSpan, kind⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;> try
                simpa [captureBlockTail, found] using recursive
              case leftBrace => exact False.elim (notOpening rfl)
              case rightBrace => exact False.elim (notClosing rfl)
          | keyword keyword =>
              simpa [captureBlockTail, found] using recursive
          | identifier text =>
              simpa [captureBlockTail, found] using recursive
          | yulIdentifier text =>
              simpa [captureBlockTail, found] using recursive
          | decimalLiteral text =>
              simpa [captureBlockTail, found] using recursive
          | hexadecimalLiteral text =>
              simpa [captureBlockTail, found] using recursive
          | stringLiteral text =>
              simpa [captureBlockTail, found] using recursive
          | yulMetaBacktick text =>
              simpa [captureBlockTail, found] using recursive
          | yulMetaInterpolation text =>
              simpa [captureBlockTail, found] using recursive

/-- The executable capture finds every declarative balanced block exactly. -/
theorem captureBlock?_complete {input : State}
    {declarativeCapture : DeclarativeGrammar.BalancedBlockCapture}
    (grammar : DeclarativeGrammar.BalancedBlockCaptures
      input.declarativeRemainder declarativeCapture) :
    ∃ captured : CapturedBlock,
      captureBlock? input = some captured ∧
      captured.span = declarativeCapture.span ∧
      captured.window.endIndex = declarativeCapture.endIndex ∧
      captured.window.endByte = declarativeCapture.endByte := by
  cases grammar with
  | @captured openingSpan closingSpan capturedEnd openingToken tail =>
      have openingFound := peek?_eq_some_of_tokenAt
        (state := input) (by
          simpa only [State.declarativeRemainder] using openingToken)
      have capturedEndInWindow := tail.endIndex_le
      have adequate : capturedEnd ≤
          input.cursor + 1 + input.remainingCount := by
        simp only [State.declarativeRemainder] at capturedEndInWindow
        unfold State.remainingCount
        omega
      have tailResult := captureBlockTail_complete input
        { span := openingSpan, value := .symbol .leftBrace }
        tail input.remainingCount adequate
      have openingAccepted :
          ((TokenKind.symbol Symbol.leftBrace ==
            TokenKind.symbol Symbol.leftBrace) = true) := by
        rfl
      refine ⟨{
        span := SourceSpan.cover openingSpan closingSpan
        window := {
          endIndex := capturedEnd
          endByte := closingSpan.endByte
        }
      }, ?_, rfl, rfl, rfl⟩
      simpa [captureBlock?, openingFound, openingAccepted] using tailResult

/-- Failure to capture excludes every declarative balanced block at the cursor. -/
theorem captureBlock?_none_absent {input : State}
    (absent : captureBlock? input = none) :
    ¬ ∃ declarativeCapture : DeclarativeGrammar.BalancedBlockCapture,
      DeclarativeGrammar.BalancedBlockCaptures input.declarativeRemainder
        declarativeCapture := by
  rintro ⟨declarativeCapture, grammar⟩
  rcases captureBlock?_complete grammar with
    ⟨captured, present, spanEq, endIndexEq, endByteEq⟩
  rw [absent] at present
  contradiction

end BlockInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedBlockDiagnosticReflectionProperties
/-! Backward diagnostic reflection through balanced block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Block isolation cannot hide an incoming diagnostic.  In the direct branch this
follows from the nested parser contract.  In the captured branch the child
starts with an empty accumulator, its diagnostics are appended to the parent
accumulator, and rejection recovery emits a fresh diagnostic.
-/
theorem isolateBlock_reflectsDiagnosticFreeOnSuccess
    (parser : Parser Block)
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (isolateBlock parser) := by
  intro input body next result diagnosticFree
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact parserReflects input body next result diagnosticFree
  | some captured =>
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.mergeDiagnostics] at diagnosticFree
          exact diagnosticFree.2
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.emit] at diagnosticFree
      | invariant error =>
          simp [childResult] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockOrdinarySuccessSoundnessProperties
/-!
Diagnostic-inclusive executable success soundness for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful block-item loop retains its existing reverse accumulator
and exposes the remaining statements in source order. -/
theorem coreBlockItems_success_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input =
          .ok body output →
      ∃ closingSpan suffix,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          value := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.CoreBlockItemsParses statementOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body output result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev
              result with ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨closingSpan, [], by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (value :: bodyRev)
                        afterStatement body output result with
                      ⟨closingSpan, suffix, bodyEq, tailParsed⟩
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨closingSpan, value :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (statementSuccessSound statementResult) progress
                        tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every successful raw Core block follows the diagnostic-inclusive ordinary
grammar for its exact tail policy. -/
theorem coreBlock_success_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {body : Block}
    (result : coreBlock statement policy input = .ok body output) :
    DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative input.declarativeRemainder body
        output.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_ordinary_sound statement
          statementOrdinary statementSuccessSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨closingSpan, suffix, bodyEq, bodyParsed⟩
      rw [bodyEq]
      exact .parsed opening.span closingSpan
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        bodyParsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockOrdinaryRejectionSoundnessProperties
/-!
Exact executable ordinary-rejection soundness for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected block-item loop records right-brace priority, the forced
closing failure at window end, or the exact rejected statement prefix. -/
theorem coreBlockItems_reject_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input failure rejected,
      coreBlockItems statement opening policy fuel bodyRev input =
          .reject failure rejected →
      DeclarativeGrammar.CoreBlockItemsRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input failure rejected result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input failure rejected result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .statement
              closingPresent with ⟨closing, closingResult⟩
          unfold closeCoreBlock at result
          simp only [bind, closingResult, modifyState, pure] at result
          contradiction
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .statement closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .missingClose
                    (symbol_reject_tokenKindAbsentAt .rightBrace .statement
                      closingResult)
                    (by simpa [State.atEnd, State.declarativeRemainder]
                      using ended)
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have notAtEnd : input.cursor < input.window.endIndex := by
                simpa [State.atEnd] using ended
              have closingAbsent :=
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject statementFailure statementRejected =>
                  simp only [statementResult] at result
                  cases result
                  exact .statementRejected notAtEnd closingAbsent
                    (statementRejectSound statementResult)
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected notAtEnd closingAbsent
                      (statementSuccessSound statementResult) progress
                      (inductionHypothesis (value :: bodyRev) afterStatement
                        failure rejected result)
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every rejected raw Core block follows opening failure or the exact
ordinary-prefix item rejection for its tail policy. -/
theorem coreBlock_reject_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement policy input = .reject failure rejected) :
    DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .statement
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .statement openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .itemsRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        (coreBlockItems_reject_ordinary_sound statement statementOrdinary
          statementRejects statementSuccessSound statementRejectSound opening
          policy (afterOpening.remainingCount + 1) [] afterOpening failure
          rejected result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
/-!
Packaged executable ordinary outcomes for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package diagnostic-inclusive success and exact rejection over supplied
statement outcome callbacks. -/
theorem coreBlock_ordinaryOutcome_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Block},
      coreBlock statement policy input = .ok body output →
        DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
          policy.declarative input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreBlock statement policy input = .reject failure rejected →
        DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
          policy.declarative input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound,
    coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem coreBlock_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (policy : TailExpressionPolicy)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
        policy.declarative)
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative) :=
  DeclarativeGrammar.coreBlockDeterministicOutcomeSpec policy.declarative
    statementOutcomes

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.BalancedBlockCaptureSoundnessProperties
/-!
Executable balanced-brace capture agrees exactly with the parser-independent
token scan.  The public theorem hides the scanner's termination fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace BlockInternals

private theorem tokenKind_eq_leftBrace_of_beq {kind : TokenKind}
    (accepted : (kind == .symbol .leftBrace) = true) :
    kind = .symbol .leftBrace := by
  change instBEqTokenKind.beq kind (.symbol .leftBrace) = true at accepted
  cases kind <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case symbol symbol =>
    change instBEqSymbol.beq symbol .leftBrace = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases symbol <;> first | rfl | cases accepted

private theorem tokenAt_of_peekOffset?_eq_some {state : State}
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    DeclarativeGrammar.TokenAt state.tokens state.window.endIndex
      (state.cursor + offset) token := by
  unfold State.peekOffset? at found
  dsimp only at found
  split at found
  · exact ⟨by assumption, found⟩
  · contradiction

private theorem captureBlockTail_success_sound (state : State)
    (opening : Token) :
    ∀ fuel depth offset captured,
      0 < depth →
      captureBlockTail state opening fuel depth offset = some captured →
      ∃ closingSpan capturedEnd,
        DeclarativeGrammar.BalancedBlockTailScans
          state.declarativeRemainder depth offset closingSpan capturedEnd ∧
        captured = {
          span := SourceSpan.cover opening.span closingSpan
          window := {
            endIndex := capturedEnd
            endByte := closingSpan.endByte
          }
        } := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth offset captured depthPositive result
      contradiction
  | succ fuel inductionHypothesis =>
      intro depth offset captured depthPositive result
      unfold captureBlockTail at result
      cases found : state.peekOffset? offset with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          have tokenAt := tokenAt_of_peekOffset?_eq_some found
          rcases token with ⟨tokenSpan, kind⟩
          have otherCase
              (notOpening : kind ≠ .symbol .leftBrace)
              (notClosing : kind ≠ .symbol .rightBrace)
              (recursive : captureBlockTail state opening fuel depth
                (offset + 1) = some captured) :
              ∃ closingSpan capturedEnd,
                DeclarativeGrammar.BalancedBlockTailScans
                  state.declarativeRemainder depth offset closingSpan
                    capturedEnd ∧
                captured = {
                  span := SourceSpan.cover opening.span closingSpan
                  window := {
                    endIndex := capturedEnd
                    endByte := closingSpan.endByte
                  }
                } := by
            rcases inductionHypothesis depth (offset + 1) captured
                depthPositive recursive with
              ⟨closingSpan, capturedEnd, tail, capturedEq⟩
            exact ⟨closingSpan, capturedEnd,
              .other tokenAt notOpening notClosing tail, capturedEq⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;> try
                exact otherCase (by simp) (by simp) result
              case leftBrace =>
                rcases inductionHypothesis (depth + 1) (offset + 1)
                    captured (by omega) result with
                  ⟨closingSpan, capturedEnd, tail, capturedEq⟩
                exact ⟨closingSpan, capturedEnd,
                  .opening tokenAt tail, capturedEq⟩
              case rightBrace =>
                by_cases atRoot : depth = 1
                · subst depth
                  have capturedEq : captured = {
                      span := SourceSpan.cover opening.span tokenSpan
                      window := {
                        endIndex := state.cursor + offset + 1
                        endByte := tokenSpan.endByte
                      }
                    } := (Option.some.inj (by simpa using result)).symm
                  exact ⟨tokenSpan, state.cursor + offset + 1,
                    .close tokenAt, capturedEq⟩
                · have reducedPositive : 0 < depth - 1 := by omega
                  have recursive : captureBlockTail state opening fuel
                      (depth - 1) (offset + 1) = some captured := by
                    simpa [atRoot] using result
                  rcases inductionHypothesis (depth - 1) (offset + 1)
                      captured reducedPositive recursive with
                    ⟨closingSpan, capturedEnd, tail, capturedEq⟩
                  have tailAtConstructorDepth :
                      DeclarativeGrammar.BalancedBlockTailScans
                        state.declarativeRemainder (depth - 2 + 1)
                          (offset + 1) closingSpan capturedEnd := by
                    simpa only [show depth - 2 + 1 = depth - 1 by omega]
                      using tail
                  have nested :=
                    DeclarativeGrammar.BalancedBlockTailScans.nestedClosing
                      (depth := depth - 2) tokenAt tailAtConstructorDepth
                  have scan :
                      DeclarativeGrammar.BalancedBlockTailScans
                        state.declarativeRemainder depth offset closingSpan
                          capturedEnd := by
                    simpa only [show depth - 2 + 2 = depth by omega]
                      using nested
                  exact ⟨closingSpan, capturedEnd, scan, capturedEq⟩
          | keyword keyword =>
              exact otherCase (by simp) (by simp) result
          | identifier text =>
              exact otherCase (by simp) (by simp) result
          | yulIdentifier text =>
              exact otherCase (by simp) (by simp) result
          | decimalLiteral text =>
              exact otherCase (by simp) (by simp) result
          | hexadecimalLiteral text =>
              exact otherCase (by simp) (by simp) result
          | stringLiteral text =>
              exact otherCase (by simp) (by simp) result
          | yulMetaBacktick text =>
              exact otherCase (by simp) (by simp) result
          | yulMetaInterpolation text =>
              exact otherCase (by simp) (by simp) result

/--
Every executable balanced capture is the exact declarative first matching
brace capture, including its source span and child token/byte window.
-/
theorem captureBlock?_success_sound {input : State}
    {captured : CapturedBlock}
    (result : captureBlock? input = some captured) :
    ∃ declarativeCapture : DeclarativeGrammar.BalancedBlockCapture,
      DeclarativeGrammar.BalancedBlockCaptures input.declarativeRemainder
        declarativeCapture ∧
      captured.span = declarativeCapture.span ∧
      captured.window.endIndex = declarativeCapture.endIndex ∧
      captured.window.endByte = declarativeCapture.endByte := by
  unfold captureBlock? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some opening =>
      simp only [found] at result
      split at result
      next openingIsBrace =>
        rcases opening with ⟨openingSpan, openingKind⟩
        have openingKindEq : openingKind = .symbol .leftBrace :=
          tokenKind_eq_leftBrace_of_beq openingIsBrace
        subst openingKind
        have openingToken := tokenAt_of_peek?_eq_some found
        rcases captureBlockTail_success_sound input
            { span := openingSpan, value := .symbol .leftBrace }
            input.remainingCount 1 1 captured (by omega) result with
          ⟨closingSpan, capturedEnd, tail, capturedEq⟩
        subst captured
        let declarativeCapture :
            DeclarativeGrammar.BalancedBlockCapture := {
          span := SourceSpan.cover openingSpan closingSpan
          endIndex := capturedEnd
          endByte := closingSpan.endByte
        }
        refine ⟨declarativeCapture, ?_, rfl, rfl, rfl⟩
        exact .captured openingToken tail
      next openingIsNotBrace => contradiction

end BlockInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedCoreBlockOrdinaryOutcomeSoundnessProperties
/-! Generic diagnostic-inclusive executable outcomes for block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem captured_child_remainder_eq
    (input : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    (input.enterWindow input.cursor captured.window).declarativeRemainder =
      capture.childRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.enterWindow,
    DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq]

private theorem captured_parent_remainder_eq
    (input child : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    (State.mergeDiagnostics
        ({ input with cursor := captured.window.endIndex } : State)
        child).declarativeRemainder =
      capture.parentRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.mergeDiagnostics,
    DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]

private theorem captured_recovered_remainder_eq
    (input child : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (failure : Failure)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    ((State.mergeDiagnostics
        ({ input with cursor := captured.window.endIndex } : State)
        child).emit failure.toDiagnostic).declarativeRemainder =
      capture.parentRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.mergeDiagnostics, State.emit,
    DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]

/-- Every executable isolation success is an uncaptured raw success, a
captured child success, or recovery of a captured child rejection. -/
theorem isolateBlock_success_ordinary_sound
    (parser : Parser Block)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      parser input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses blockOrdinary
      blockRejects input.declarativeRemainder body
        output.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (blockSuccessSound result)
  | some captured =>
      simp only [captureResult] at result
      rcases BlockInternals.captureBlock?_success_sound captureResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      have childInputEq := captured_child_remainder_eq input captured capture
        endIndexEq
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          have parentOutputEq := captured_parent_remainder_eq input childAfter
            captured capture endIndexEq
          rw [parentOutputEq]
          exact .captured captureParsed (by
            rw [← childInputEq]
            exact blockSuccessSound childResult)
      | reject childFailure childRejected =>
          simp only [childResult] at result
          cases result
          have parentOutputEq := captured_recovered_remainder_eq input
            childRejected captured capture childFailure endIndexEq
          rw [parentOutputEq, spanEq]
          exact .recovered captureParsed (by
            rw [← childInputEq]
            exact blockRejectSound childResult)

/-- An executable isolation rejection is only an uncaptured raw rejection. -/
theorem isolateBlock_reject_ordinary_sound
    (parser : Parser Block)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock parser input = .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockRejects blockRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (blockRejectSound result)
  | some captured =>
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | ok childBody childAfter => simp [childResult] at result
      | reject childFailure childRejected => simp [childResult] at result

/-- Package generic executable isolation success and rejection. -/
theorem isolateBlock_ordinaryOutcome_sound
    (parser : Parser Block)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      parser input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Block},
      isolateBlock parser input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses blockOrdinary
          blockRejects input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock parser input = .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockRejects blockRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨isolateBlock_success_ordinary_sound parser blockOrdinary blockRejects
      blockSuccessSound blockRejectSound,
    isolateBlock_reject_ordinary_sound parser blockRejects blockRejectSound⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockIsolationOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary outcomes for isolated raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful isolated raw Core block follows the capture-aware
ordinary grammar. -/
theorem isolatedCoreBlock_success_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input output : State} {body : Block}
    (result : isolateBlock (coreBlock statement policy) input =
      .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
      (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
        policy.declarative)
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative)
      input.declarativeRemainder body output.declarativeRemainder :=
  isolateBlock_success_ordinary_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)
    result

/-- Every externally visible isolated raw Core block rejection is the exact
uncaptured raw rejection. -/
theorem isolatedCoreBlock_reject_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock (coreBlock statement policy) input =
      .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockRejects
      (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
        policy.declarative)
      input.declarativeRemainder rejected.declarativeRemainder :=
  isolateBlock_reject_ordinary_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)
    result

/-- Package executable success and rejection for isolated raw Core blocks. -/
theorem isolatedCoreBlock_ordinaryOutcome_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Block},
      isolateBlock (coreBlock statement policy) input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
          (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
            policy.declarative)
          (DeclarativeGrammar.CoreBlockRejects statementOrdinary
            statementRejects policy.declarative)
          input.declarativeRemainder body output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock (coreBlock statement policy) input =
          .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockRejects
          (DeclarativeGrammar.CoreBlockRejects statementOrdinary
            statementRejects policy.declarative)
          input.declarativeRemainder rejected.declarativeRemainder) :=
  isolateBlock_ordinaryOutcome_sound (coreBlock statement policy)
    (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative)
    (DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative)
    (coreBlock_success_ordinary_sound statement policy statementOrdinary
      statementSuccessSound)
    (coreBlock_reject_ordinary_sound statement policy statementOrdinary
      statementRejects statementSuccessSound statementRejectSound)

/-- Re-export the deterministic contract for isolated raw Core blocks. -/
theorem isolatedCoreBlock_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (policy : TailExpressionPolicy)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses
        (DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
          policy.declarative)
        (DeclarativeGrammar.CoreBlockRejects statementOrdinary
          statementRejects policy.declarative))
      (DeclarativeGrammar.IsolatedCoreBlockRejects
        (DeclarativeGrammar.CoreBlockRejects statementOrdinary
          statementRejects policy.declarative)) :=
  DeclarativeGrammar.isolatedCoreBlockDeterministicOutcomeSpec
    (coreBlock_ordinaryOutcomeSpec policy statementOutcomes)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockSoundnessProperties
/-!
Diagnostic reflection and exact declarative soundness for raw Core blocks.

This module covers `coreBlock` inside one active token window.  Balanced-block
isolation is intentionally handled by a separate grammar bridge.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Successful block-loop execution recovers the forward suffix appended after its
existing reverse accumulator, together with exact closing-brace recognition.
-/
private theorem coreBlockItems_success_sound_strong
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {statementInput statementNext : State}
      {value : Statement}, statementNext.diagnosticsRev = [] →
      statement statementInput = .ok value statementNext →
      statementParses statementInput.declarativeRemainder value
        statementNext.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body next,
      next.diagnosticsRev = [] →
      coreBlockItems statement opening policy fuel bodyRev input =
        .ok body next →
      ∃ statements closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          value := bodyRev.reverse ++ statements
        } ∧
        DeclarativeGrammar.CoreBlockItemsParses statementParses
          input.declarativeRemainder statements closingSpan
            next.declarativeRemainder ∧
        DeclarativeGrammar.CoreBlockTailsValid policy.declarative
          (bodyRev.reverse ++ statements) ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next diagnosticFree result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next diagnosticFree result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_sound_and_reflects opening policy
              bodyRev diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, tailsValid, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, by simpa using tailsValid,
            inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (value :: bodyRev)
                        afterStatement body next diagnosticFree result with
                      ⟨statements, closingSpan, bodyEq, tailGrammar,
                        tailsValid, afterStatementFree⟩
                    have statementGrammar :=
                      statementSound afterStatementFree statementResult
                    have inputFree := statementReflects input value
                      afterStatement statementResult afterStatementFree
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨value :: statements, closingSpan, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        statementGrammar progress tailGrammar,
                      ?_, inputFree⟩
                    · simpa [List.reverse_cons, List.append_assoc] using bodyEq
                    · simpa [List.reverse_cons, List.append_assoc] using
                        tailsValid
                  · simp only [progress, if_false] at result
                    contradiction

/-- Raw Core-block parsing cannot erase an incoming diagnostic. -/
theorem coreBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (coreBlock statement policy) := by
  intro input body next result diagnosticFree
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      let trivialParses : DeclarativeGrammar.Remainder → Statement →
          DeclarativeGrammar.Remainder → Prop := fun _ _ _ => True
      have trivialSound : ∀ {statementInput statementNext : State}
          {value : Statement}, statementNext.diagnosticsRev = [] →
          statement statementInput = .ok value statementNext →
          trivialParses statementInput.declarativeRemainder value
            statementNext.declarativeRemainder := by
        intro statementInput statementNext value outputFree parsed
        trivial
      rcases coreBlockItems_success_sound_strong trivialParses statement
          statementReflects trivialSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨statements, closingSpan, bodyEq, tailGrammar, tailsValid,
          afterOpeningFree⟩
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .statement input
        opening afterOpening openingResult afterOpeningFree

/--
Every diagnostic-free successful raw Core block follows the exact braced
statement grammar and satisfies its executable tail-semicolon policy.
-/
theorem coreBlock_success_sound
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {statementInput statementNext : State}
      {value : Statement}, statementNext.diagnosticsRev = [] →
      statement statementInput = .ok value statementNext →
      statementParses statementInput.declarativeRemainder value
        statementNext.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : coreBlock statement policy input = .ok body next) :
    DeclarativeGrammar.CoreBlockParses statementParses policy.declarative
      input.declarativeRemainder body next.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_sound_strong statementParses statement
          statementReflects statementSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨statements, closingSpan, bodyEq, bodyGrammar, tailsValid,
          afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.CoreBlockParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        bodyGrammar tailsValid

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedCoreBlockSoundnessProperties
/-!
Exact declarative soundness for balanced block isolation.

The direct branch retains the parent's active window.  The captured branch
runs the supplied block parser in the exact balanced child window and resumes
the parent at the matching closing brace.  A recovered child rejection cannot
produce a diagnostic-free successful result.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Diagnostic-free successful block isolation follows the exact declarative
direct-or-captured relation for any sound inner block parser.
-/
theorem isolateBlock_success_sound
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (parser : Parser Block)
    (parserSound : ∀ {input next : State} {body : Block},
      next.diagnosticsRev = [] →
      parser input = .ok body next →
      blockParses input.declarativeRemainder body
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock parser input = .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses blockParses
      input.declarativeRemainder body next.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (parserSound diagnosticFree result)
  | some captured =>
      simp only [captureResult] at result
      rcases BlockInternals.captureBlock?_success_sound captureResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.mergeDiagnostics, State.emit] at diagnosticFree
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          have childDiagnosticFree : childAfter.diagnosticsRev = [] := by
            simp [State.mergeDiagnostics] at diagnosticFree
            exact diagnosticFree.1
          have childInputEq :
              State.declarativeRemainder
                  (input.enterWindow input.cursor captured.window) =
                capture.childRemainder input.declarativeRemainder := by
            simp [State.declarativeRemainder, State.enterWindow,
              DeclarativeGrammar.BalancedBlockCapture.childRemainder,
              endIndexEq]
          have parentOutputEq :
              State.declarativeRemainder
                  (State.mergeDiagnostics
                    ({ input with cursor := captured.window.endIndex } : State)
                    childAfter) =
                capture.parentRemainder input.declarativeRemainder := by
            simp [State.declarativeRemainder, State.mergeDiagnostics,
              DeclarativeGrammar.BalancedBlockCapture.parentRemainder,
              endIndexEq]
          rw [parentOutputEq]
          exact .captured captureParsed (by
            rw [← childInputEq]
            exact parserSound childDiagnosticFree childResult)

/--
The generic isolated-block contract packages exact declarative soundness with
backward diagnostic reflection from the supplied inner parser.
-/
theorem isolateBlock_success_sound_and_reflects
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (parser : Parser Block)
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser)
    (parserSound : ∀ {input next : State} {body : Block},
      next.diagnosticsRev = [] →
      parser input = .ok body next →
      blockParses input.declarativeRemainder body
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock parser input = .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses blockParses
        input.declarativeRemainder body next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  exact ⟨isolateBlock_success_sound blockParses parser parserSound
      diagnosticFree result,
    isolateBlock_reflectsDiagnosticFreeOnSuccess parser parserReflects
      input body next result diagnosticFree⟩

/-- Exact declarative soundness for an isolated raw Core block. -/
theorem isolatedCoreBlock_success_sound
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] →
      statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock (coreBlock statement policy) input =
      .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses
      (DeclarativeGrammar.CoreBlockParses statementParses
        policy.declarative)
      input.declarativeRemainder body next.declarativeRemainder := by
  exact isolateBlock_success_sound
    (DeclarativeGrammar.CoreBlockParses statementParses policy.declarative)
    (coreBlock statement policy)
    (coreBlock_success_sound statementParses statement policy
      statementReflects statementSound)
    diagnosticFree result

/-- Isolated raw Core blocks also reflect diagnostic freedom to their input. -/
theorem isolatedCoreBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (coreBlock statement policy)) :=
  isolateBlock_reflectsDiagnosticFreeOnSuccess (coreBlock statement policy)
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement policy
      statementReflects)

end Solcore.Syntax.Parser
end
