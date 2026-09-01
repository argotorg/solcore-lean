import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the guarded Core array-literal
branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The exact array grammar already admits arbitrary ordinary nested element
outcomes. -/
abbrev ArrayLiteralExpressionOrdinaryParses :=
  ArrayLiteralExpressionParses

/-- Exact rejection after the atom dispatcher has selected a present `[`.
The opening evidence excludes the generic delimiter-missing branch while the
delimited trace retains first-element and later-tail priority exactly. -/
inductive ArrayLiteralExpressionRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftBracket
      })
      (valuesRejected : DelimitedListRejects .leftBracket .rightBracket true
        false nestedOrdinary nestedRejects input rejected) :
      ArrayLiteralExpressionRejects nestedOrdinary nestedRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
