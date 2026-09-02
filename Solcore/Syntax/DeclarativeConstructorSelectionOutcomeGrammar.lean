import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for export constructor selections.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary constructor-selection success is the existing exact grammar. -/
abbrev ConstructorSelectionOrdinaryParses := ConstructorSelectionParses

/-- Exact prioritized rejection of an all-or-named constructor selection. -/
inductive ConstructorSelectionRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder} (markerSpan : SourceSpan)
      (markerToken : TokenAt input.tokens input.endIndex
        (input.cursor + 1) {
          span := markerSpan
          value := .symbol .star
        })
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      ConstructorSelectionRejects input input
  | closingMissing {input afterOpening afterMarker : Remainder}
      (openingSpan markerSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses (.symbol .star) afterOpening
        markerSpan afterMarker)
      (closingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .rightParen)) :
      ConstructorSelectionRejects input afterMarker
  | namedRejected {input rejected : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        (input.cursor + 1) (.symbol .star))
      (namesRejected : DelimitedListRejects .leftParen .rightParen false false
        IdentifierParses IdentifierRejects input rejected) :
      ConstructorSelectionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
