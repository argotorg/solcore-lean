import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent lexical recognition of one balanced braced token window.

The scanner counts only brace tokens.  Every other token is retained as an
opaque step, so the relation fixes the first right brace that returns the
opening depth to zero without depending on statement parsing or parser fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Source range and child-window endpoint selected by balanced capture. -/
structure BalancedBlockCapture where
  span : SourceSpan
  endIndex : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

/--
Successful tail scan from one positive brace depth and relative token offset.
The result endpoint is one past the matching closing brace.
-/
inductive BalancedBlockTailScans (input : Remainder) :
    Nat → Nat → SourceSpan → Nat → Prop where
  | close {offset : Nat} {closingSpan : SourceSpan}
      (closingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := closingSpan
          value := .symbol .rightBrace
        }) :
      BalancedBlockTailScans input 1 offset closingSpan
        (input.cursor + offset + 1)
  | opening {depth offset capturedEnd : Nat}
      {openingSpan closingSpan : SourceSpan}
      (openingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := openingSpan
          value := .symbol .leftBrace
        })
      (tail : BalancedBlockTailScans input (depth + 1) (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input depth offset closingSpan capturedEnd
  | nestedClosing {depth offset capturedEnd : Nat}
      {nestedSpan closingSpan : SourceSpan}
      (closingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := nestedSpan
          value := .symbol .rightBrace
        })
      (tail : BalancedBlockTailScans input (depth + 1) (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input (depth + 2) offset closingSpan capturedEnd
  | other {depth offset capturedEnd : Nat} {token : Token}
      {closingSpan : SourceSpan}
      (tokenAt : TokenAt input.tokens input.endIndex
        (input.cursor + offset) token)
      (notOpening : token.value ≠ .symbol .leftBrace)
      (notClosing : token.value ≠ .symbol .rightBrace)
      (tail : BalancedBlockTailScans input depth (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input depth offset closingSpan capturedEnd

/-- Exact first balanced block capture beginning at the current cursor. -/
inductive BalancedBlockCaptures :
    Remainder → BalancedBlockCapture → Prop where
  | captured {input : Remainder} {openingSpan closingSpan : SourceSpan}
      {capturedEnd : Nat}
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftBrace
      })
      (tail : BalancedBlockTailScans input 1 1 closingSpan capturedEnd) :
      BalancedBlockCaptures input {
        span := SourceSpan.cover openingSpan closingSpan
        endIndex := capturedEnd
        endByte := closingSpan.endByte
      }

namespace BalancedBlockCapture

/-- Parser remainder inside the captured brace window. -/
def childRemainder (input : Remainder)
    (captured : BalancedBlockCapture) : Remainder := {
  tokens := input.tokens
  endIndex := captured.endIndex
  cursor := input.cursor
}

/-- Parent remainder immediately after the captured closing brace. -/
def parentRemainder (input : Remainder)
    (captured : BalancedBlockCapture) : Remainder := {
  input with cursor := captured.endIndex
}

end BalancedBlockCapture

/-- Every successful tail capture ends strictly after its starting cursor. -/
theorem BalancedBlockTailScans.cursor_lt {input : Remainder}
    {depth offset : Nat} {closingSpan : SourceSpan} {capturedEnd : Nat}
    (scan : BalancedBlockTailScans input depth offset closingSpan capturedEnd) :
    input.cursor < capturedEnd := by
  induction scan with
  | close closingToken =>
      rcases closingToken with ⟨inside, found⟩
      omega
  | opening openingToken tail inductionHypothesis => exact inductionHypothesis
  | nestedClosing closingToken tail inductionHypothesis =>
      exact inductionHypothesis
  | other tokenAt notOpening notClosing tail inductionHypothesis =>
      exact inductionHypothesis

/-- A balanced capture endpoint remains inside the original token window. -/
theorem BalancedBlockTailScans.endIndex_le {input : Remainder}
    {depth offset : Nat} {closingSpan : SourceSpan} {capturedEnd : Nat}
    (scan : BalancedBlockTailScans input depth offset closingSpan capturedEnd) :
    capturedEnd ≤ input.endIndex := by
  induction scan with
  | close closingToken =>
      rcases closingToken with ⟨inside, found⟩
      omega
  | opening openingToken tail inductionHypothesis => exact inductionHypothesis
  | nestedClosing closingToken tail inductionHypothesis =>
      exact inductionHypothesis
  | other tokenAt notOpening notClosing tail inductionHypothesis =>
      exact inductionHypothesis

/-- No lexically balanced braced capture begins at this cursor. -/
def BalancedBlockCaptureAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ captured, BalancedBlockCaptures input captured

/--
Exact behavior of the isolation wrapper over an abstract block grammar.

Without a capture the underlying grammar runs in the parent window.  With a
capture it runs in the smaller child window while the parent always resumes
immediately after the captured closing brace.
-/
inductive IsolatedCoreBlockParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Block → Remainder → Prop where
  | direct {input output : Remainder} {body : Syntax.Block}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockParses input body output) :
      IsolatedCoreBlockParses blockParses input body output
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockParses (capture.childRemainder input) body
        childOutput) :
      IsolatedCoreBlockParses blockParses input body
        (capture.parentRemainder input)

end Solcore.Syntax.DeclarativeGrammar
