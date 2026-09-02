import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for import and export selector
names.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No symbol accepted by the operator-selector collector occurs at one
cursor. -/
def SelectorOperatorPartAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ symbol span,
    SelectorOperatorSymbol symbol ∧
      TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol symbol
      }

/-- Fuel-independent maximal scan of consecutive operator-selector symbols.

The result is in forward source order.  The `done` premise ensures that the
scan cannot stop before another accepted symbol. -/
inductive MaximalSelectorOperatorPartsParses :
    Remainder → List String → Remainder → Prop where
  | done {input : Remainder}
      (partAbsent : SelectorOperatorPartAbsentAt input) :
      MaximalSelectorOperatorPartsParses input [] input
  | next {input output : Remainder} {symbol : Symbol}
      {parts : List String}
      (allowed : SelectorOperatorSymbol symbol)
      (span : SourceSpan)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol symbol
      })
      (tail : MaximalSelectorOperatorPartsParses
        { input with cursor := input.cursor + 1 } parts output) :
      MaximalSelectorOperatorPartsParses input
        (symbol.spelling :: parts) output

/-- Ordinary selector-name success is the existing exact identifier/operator
grammar. -/
abbrev SelectorNameOrdinaryParses := SelectorNameParses

/-- Exact prioritized executable rejection of one selector name. -/
inductive SelectorNameRejects : Remainder → Remainder → Prop where
  | identifierRejected {input rejected : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameRejected : IdentifierRejects input rejected) :
      SelectorNameRejects input rejected
  | emptyOperator {input afterOpening : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (partAbsent : SelectorOperatorPartAbsentAt afterOpening) :
      SelectorNameRejects input afterOpening
  | closingMissing {input afterOpening afterParts : Remainder}
      {parts : List String}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (partsParsed : MaximalSelectorOperatorPartsParses afterOpening parts
        afterParts)
      (partsNonempty : parts ≠ [])
      (closingAbsent : TokenKindAbsentAt afterParts.tokens
        afterParts.endIndex afterParts.cursor (.symbol .rightParen)) :
      SelectorNameRejects input afterParts

end Solcore.Syntax.DeclarativeGrammar
