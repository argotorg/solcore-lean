import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeGrammar

/-! Ordinary success and exact rejection for a Core identifier expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing identifier-expression grammar already uses ordinary
Boolean-first expression names. -/
abbrev IdentifierExpressionOrdinaryParses := IdentifierExpressionParses

/-- Exact rejection inherited from the wrapped expression-name parser. -/
inductive IdentifierExpressionRejects : Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : ExpressionNameRejects input rejected) :
      IdentifierExpressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
