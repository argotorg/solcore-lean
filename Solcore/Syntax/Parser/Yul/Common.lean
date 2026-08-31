import Solcore.Syntax.Parser.Yul.Expression

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

end Solcore.Syntax.Parser
