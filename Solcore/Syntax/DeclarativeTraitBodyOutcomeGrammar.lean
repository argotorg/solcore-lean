import Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar

/-!
Parser-independent ordinary success and exact rejection for the prioritized
trait-method body loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive `function` lookahead selecting the method branch. -/
def TraitMethodStartAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span, value := .keyword .functionKw }

/-- Forward ordinary methods ending at the exact closing brace.  The closing
branch has priority, and the method branch records its positive guard and
strict cursor progress independently of the executable fuel bound. -/
inductive TraitMethodTailOrdinaryParses :
    Remainder → List Syntax.TraitMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      TraitMethodTailOrdinaryParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.TraitMethod} {methods : List Syntax.TraitMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodParsed : TraitMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tail : TraitMethodTailOrdinaryParses afterMethod methods closingSpan
        output) :
      TraitMethodTailOrdinaryParses input (method :: methods) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward methods. -/
def TraitMethodTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.TraitMethod)
    (output : Remainder) : Prop :=
  TraitMethodTailOrdinaryParses input tail.2 tail.1 output

/-- Exact ordinary rejection of the prioritized trait-method loop. -/
inductive TraitMethodTailRejects : Remainder → Remainder → Prop where
  | unexpected {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw)) :
      TraitMethodTailRejects input input
  | methodRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodRejected : TraitMethodRejects input rejected) :
      TraitMethodTailRejects input rejected
  | laterRejected {input afterMethod rejected : Remainder}
      {method : Syntax.TraitMethod}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodParsed : TraitMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tailRejected : TraitMethodTailRejects afterMethod rejected) :
      TraitMethodTailRejects input rejected

/-- Exact braces, retained body span, and source-order ordinary trait methods. -/
inductive TraitBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.TraitMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.TraitMethod} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : TraitMethodTailOrdinaryParses afterOpening methods
        closingSpan output) :
      TraitBodyOrdinaryParses input (SourceSpan.cover openingSpan closingSpan)
        methods output

/-- Single-output adapter retaining the body span and forward methods. -/
def TraitBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.TraitMethod)
    (output : Remainder) : Prop :=
  TraitBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of a complete braced trait body. -/
inductive TraitBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      TraitBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : TraitMethodTailRejects afterOpening rejected) :
      TraitBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
