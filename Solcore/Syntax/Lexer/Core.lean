import Solcore.Syntax.Lexer.Step

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Fuel-bounded executor for successive maximal-munch transitions. -/
def lexLoop (file : SourceFile) : Nat → State → LexResult
  | 0, state =>
      .error {
        span := sourceSpan file state.cursor state.cursor
        kind := .internalFuelExhausted
      }
  | _fuel + 1, state@{ remaining := [] , .. } =>
      .ok (state.finish file)
  | fuel + 1, state =>
      lexLoop file fuel (step file state)

/--
Total canonical lexer. Source errors are accumulated in the successful value;
the exceptional branch is reserved for an unreachable executor invariant.
-/
def lex (file : SourceFile) : LexResult :=
  lexLoop file (fuelBound file) (State.initial file)

end Solcore.Syntax.Lexer
