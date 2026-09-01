import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the guarded leading-dot Core
constructor branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing optional-arguments grammar admits ordinary nested outcomes
as-is. -/
abbrev OptionalDotConstructorArgumentsOrdinaryParses :=
  OptionalDotConstructorArgumentsParses

/-- Exact rejection of a present leading-dot argument list.  Opening-token
evidence records that the optional parser selected, and committed to, its
parenthesized branch. -/
inductive OptionalDotConstructorArgumentsRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true
        false nestedOrdinary nestedRejects input rejected) :
      OptionalDotConstructorArgumentsRejects nestedOrdinary nestedRejects
        input rejected

/-- The existing exact leading-dot grammar admits ordinary nested outcomes
as-is. -/
abbrev DotConstructorOrdinaryParses := DotConstructorParses

/-- Exact rejection inside the guarded leading-dot constructor branch.  Dot
absence belongs to the enclosing atom dispatcher's failed guard. -/
inductive DotConstructorRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | nameRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : ExpressionNameRejects afterDot rejected) :
      DotConstructorRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected {input afterDot afterName rejected : Remainder}
      {name : Syntax.Identifier} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameOrdinaryParses afterDot name afterName)
      (argumentsRejected : OptionalDotConstructorArgumentsRejects
        nestedOrdinary nestedRejects afterName rejected) :
      DotConstructorRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
