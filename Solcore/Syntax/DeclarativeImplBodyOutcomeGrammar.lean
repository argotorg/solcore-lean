import Solcore.Syntax.DeclarativeImplMethodOutcomeGrammar

/-!
Parser-independent ordinary success and exact rejection for the prioritized
implementation-method body loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive `function` lookahead selecting the method branch. -/
def ImplMethodStartAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span, value := .keyword .functionKw }

/-- Forward ordinary methods ending at the exact closing brace.  The closing
branch has priority, and the method branch records its positive guard and
strict cursor progress independently of the executable fuel bound. -/
inductive ImplMethodTailOrdinaryParses :
    Remainder → List Syntax.ImplMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ImplMethodTailOrdinaryParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.ImplMethod} {methods : List Syntax.ImplMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodParsed : ImplMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tail : ImplMethodTailOrdinaryParses afterMethod methods closingSpan
        output) :
      ImplMethodTailOrdinaryParses input (method :: methods) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward methods. -/
def ImplMethodTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.ImplMethod)
    (output : Remainder) : Prop :=
  ImplMethodTailOrdinaryParses input tail.2 tail.1 output

/-- Exact ordinary rejection of the prioritized implementation-method loop. -/
inductive ImplMethodTailRejects : Remainder → Remainder → Prop where
  | unexpected {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw)) :
      ImplMethodTailRejects input input
  | methodRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodRejected : ImplMethodRejects input rejected) :
      ImplMethodTailRejects input rejected
  | laterRejected {input afterMethod rejected : Remainder}
      {method : Syntax.ImplMethod}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodParsed : ImplMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tailRejected : ImplMethodTailRejects afterMethod rejected) :
      ImplMethodTailRejects input rejected

/-- Exact braces, retained body span, and source-order ordinary methods. -/
inductive ImplBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.ImplMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.ImplMethod} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : ImplMethodTailOrdinaryParses afterOpening methods
        closingSpan output) :
      ImplBodyOrdinaryParses input (SourceSpan.cover openingSpan closingSpan)
        methods output

/-- Single-output adapter retaining the body span and forward methods. -/
def ImplBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.ImplMethod)
    (output : Remainder) : Prop :=
  ImplBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of a complete braced implementation body. -/
inductive ImplBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      ImplBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : ImplMethodTailRejects afterOpening rejected) :
      ImplBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
