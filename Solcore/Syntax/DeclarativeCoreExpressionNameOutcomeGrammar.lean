import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLiteralGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Ordinary success and exact rejection for a Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing Boolean-first name grammar includes diagnosed identifiers. -/
abbrev ExpressionNameOrdinaryParses := ExpressionNameParses

/-- Neither Boolean keyword nor an ordinary identifier token starts here. -/
def ExpressionNameAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .trueKw) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .falseKw) ∧
    IdentifierAbsentAt input

/-- Exact non-consuming rejection of the Boolean-first expression-name
parser. -/
inductive ExpressionNameRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (absent : ExpressionNameAbsentAt input) :
      ExpressionNameRejects input input

end Solcore.Syntax.DeclarativeGrammar
