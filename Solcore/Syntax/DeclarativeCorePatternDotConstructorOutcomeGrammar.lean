import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternNameOutcomeGrammar

/-!
Parser-independent ordinary outcomes for a leading-dot Core constructor
pattern.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success through the dot, Boolean-first name, and
transactional optional-argument stages. -/
inductive DotConstructorPatternOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input afterDot afterName output : Remainder}
      {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : PatternNameOrdinaryParses afterDot name afterName)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterName arguments output) :
      DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := SourceSpan.cover dotSpan
          (arguments.map (fun values => values.span) |>.getD name.span)
        value := .constructor (some dotSpan) [] name arguments
      } output

/-- Exact rejection follows parser order: the leading dot is absent, the
committed name rejects after that dot, or the optional-argument stage rejects
after both earlier stages.  The final relation is empty for the concrete
transactional optional parser, but recording it keeps the sequential outcome
shape exact. -/
inductive DotConstructorPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | dotMissing {input : Remainder}
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot)) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input input
  | nameRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (rejectedName : PatternNameRejects afterDot rejected) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected
      {input afterDot afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : PatternNameOrdinaryParses afterDot name afterName)
      (rejectedArguments : OptionalConstructorArgumentsRejects afterName
        rejected) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
