import Solcore.Syntax.Parser.Primitive

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

private structure CapturedBlock where
  span : SourceSpan
  window : TokenWindow

private def captureBlockTail (state : State) (opening : Token) :
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

private def captureBlock? (state : State) : Option CapturedBlock :=
  match state.peek? with
  | some opening =>
      if opening.value == .symbol .leftBrace then
        captureBlockTail state opening state.remainingCount 1 1
      else
        none
  | none => none

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
