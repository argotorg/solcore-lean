import Solcore.Syntax.DeclarativeBalancedBlockGrammar
import Solcore.Syntax.Parser.Block

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
