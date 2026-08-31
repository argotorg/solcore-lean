import Solcore.Syntax.Parser.Function

/-! State and start-token contracts for complete function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Function declarations preserve token windows when block parsing does. -/
theorem functionDecl_preservesTokenWindow_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_preservesTokenWindow
    (functionSignature_preservesTokenWindow location)
  intro signature
  apply Parser.bind_preservesTokenWindow
    (isolateBlock_preservesTokenWindow (block .allow) bodyWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful function parsing preserves the immutable token carrier. -/
theorem functionDecl_preservesTokensOnSuccess_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess (functionDecl location) :=
  (functionDecl_preservesTokenWindow_of_block location bodyWindow
    ).preservesTokensOnSuccess

/-- Function declarations never rewind when block parsing is monotone. -/
theorem functionDecl_cursorMonotoneOnSuccess_of_block
    (location : FunctionLocation)
    (bodyCursor : Parser.CursorMonotoneOnSuccess (block .allow)) :
    Parser.CursorMonotoneOnSuccess (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (functionSignature_cursorMonotoneOnSuccess location)
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow) bodyCursor)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A function declaration starts at its signature's `function` keyword. -/
theorem functionDecl_startsAtCurrentTokenOnSuccess
    (location : FunctionLocation) :
    Parser.StartsAtCurrentTokenOnSuccess (functionDecl location) (·.span) := by
  unfold functionDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (functionSignature_startsAtCurrentTokenOnSuccess location)
  intro signature input declaration final parsed
  simp only [bind] at parsed
  cases bodyResult : isolateBlock (block .allow) input with
  | invariant error => simp [bodyResult] at parsed
  | reject failure rejected => simp [bodyResult] at parsed
  | ok body afterBody =>
      simp only [bodyResult] at parsed
      cases parsed
      rfl

end Solcore.Syntax.Parser
