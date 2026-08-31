import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse one literal admitted by Core expressions and patterns. -/
def coreLiteral : Parser CoreLiteral := fun state =>
  match state.peek? with
  | some { span, value := .decimalLiteral spelling } =>
      .ok { span, value := .decimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .hexadecimalLiteral spelling } =>
      .ok { span, value := .hexadecimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .stringLiteral spelling } =>
      .ok { span, value := .string spelling }
        { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .coreLiteral, tail := [] } .expression

/-- Preserve `true` and `false` as identifier-shaped builtin values. -/
def booleanIdentifier : Parser Identifier := fun state =>
  match state.peek? with
  | some { span, value := .keyword .trueKw } =>
      .ok { span, value := "true" }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .keyword .falseKw } =>
      .ok { span, value := "false" }
        { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .expression, tail := [] } .expression

def isCoreLiteral (state : State) : Bool :=
  match state.peekKind? with
  | some (.decimalLiteral _)
  | some (.hexadecimalLiteral _)
  | some (.stringLiteral _) => true
  | _ => false

def isBooleanValue (state : State) : Bool :=
  isKeyword state .trueKw || isKeyword state .falseKw

end Solcore.Syntax.Parser
