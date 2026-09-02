import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveTargetOutcomeGrammar

/-!
Parser-independent exact rejection stages for the normal derive-attribute
path.  The successful path remains the established `DeriveAttributeParses`
relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejecting stage of the proof-visible normal derive-attribute
parser.  Diagnostic emission after the closing bracket and the final pure
construction cannot reject. -/
inductive DeriveAttributeValidRejects : Remainder → Remainder → Prop where
  | hashMissing {input : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash)) :
      DeriveAttributeValidRejects input input
  | openingMissing {input afterHash : Remainder} (hashSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingAbsent : TokenKindAbsentAt afterHash.tokens afterHash.endIndex
        afterHash.cursor (.symbol .leftBracket)) :
      DeriveAttributeValidRejects input afterHash
  | markerMissing {input afterHash afterOpening : Remainder}
      (hashSpan openingSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor
        (.identifier ContextualKeyword.derive.spelling)) :
      DeriveAttributeValidRejects input afterOpening
  | targetsRejected
      {input afterHash afterOpening afterMarker rejected : Remainder}
      (hashSpan openingSpan markerSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.derive.spelling) afterOpening
        markerSpan afterMarker)
      (targetsRejected : DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects afterMarker rejected) :
      DeriveAttributeValidRejects input rejected
  | closingMissing
      {input afterHash afterOpening afterMarker afterTargets : Remainder}
      {targets : Syntax.DelimitedList Syntax.DeriveTarget}
      (hashSpan openingSpan markerSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.derive.spelling) afterOpening
        markerSpan afterMarker)
      (targetsParsed : NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses afterMarker targets afterTargets)
      (closingAbsent : TokenKindAbsentAt afterTargets.tokens
        afterTargets.endIndex afterTargets.cursor (.symbol .rightBracket)) :
      DeriveAttributeValidRejects input afterTargets

end Solcore.Syntax.DeclarativeGrammar
