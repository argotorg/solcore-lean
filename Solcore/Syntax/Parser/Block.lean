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

end Solcore.Syntax.Parser
