import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar

/-!
Parser-independent exact ordinary outcomes for malformed derive-attribute
recovery.  This file describes only the proof-visible recovery parser, not the
public transactional choice between the normal and recovered paths.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact declaration boundaries at which an unclosed derive attribute stops
without consuming the following declaration or contract closing brace. -/
inductive DeriveAttributeRecoveryDeclarationStartsAt :
    Remainder → Prop where
  | topItem {input : Remainder}
      (starts : ImportTerminatorTopItemStartsAt input) :
      DeriveAttributeRecoveryDeclarationStartsAt input
  | contractField {input : Remainder}
      (starts : ContractFieldStartsAt input) :
      DeriveAttributeRecoveryDeclarationStartsAt input
  | rightBrace {input : Remainder} (span : SourceSpan)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      DeriveAttributeRecoveryDeclarationStartsAt input

/-- Exact nonconsuming stops of the malformed derive-tail scan.  A missing
array slot inside the active window is an unclosed recovery success rather
than a rejection. -/
inductive DeriveAttributeRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      DeriveAttributeRecoveryStops input
  | declaration {input : Remainder}
      (starts : DeriveAttributeRecoveryDeclarationStartsAt input) :
      DeriveAttributeRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      DeriveAttributeRecoveryStops input

/-- Canonical empty-target AST returned by either malformed or unclosed derive
recovery.  Both the outer attribute and its empty target list use the cover
from the original hash through the last retained span. -/
def recoveredDeriveAttributeValue
    (hash last : SourceSpan) : Syntax.DeriveAttribute :=
  let span := SourceSpan.cover hash last
  {
    span
    value := { targets := { span, elements := [] } }
  }

/-- Exact priority-ordered scan after recovery has consumed `#[`.  A current
`]` is consumed before any stop is considered.  Otherwise a stop returns an
unclosed value without consumption, and any remaining current token advances
the scan by one. -/
inductive DeriveAttributeRecoveryTailParses (hash : SourceSpan) :
    SourceSpan → Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | malformed {last : SourceSpan} {input output : Remainder}
      (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBracket) input
        closingSpan output) :
      DeriveAttributeRecoveryTailParses hash last input
        (recoveredDeriveAttributeValue hash closingSpan) output
  | unclosed {last : SourceSpan} {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBracket))
      (stops : DeriveAttributeRecoveryStops input) :
      DeriveAttributeRecoveryTailParses hash last input
        (recoveredDeriveAttributeValue hash last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {value : Syntax.DeriveAttribute}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBracket))
      (continues : ¬ DeriveAttributeRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : DeriveAttributeRecoveryTailParses hash token.span
        { input with cursor := input.cursor + 1 } value output) :
      DeriveAttributeRecoveryTailParses hash last input value output

/-- Exact successful recovery path: consume hash and opening bracket, then run
the malformed tail from the opening bracket's span. -/
inductive DeriveAttributeRecoveredParses :
    Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | recovered {input afterHash afterOpening output : Remainder}
      {value : Syntax.DeriveAttribute}
      (hashSpan openingSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (tail : DeriveAttributeRecoveryTailParses hashSpan openingSpan
        afterOpening value output) :
      DeriveAttributeRecoveredParses input value output

/-- Recovery can reject only before its tail begins: at the initial hash or at
the opening bracket after a consumed hash. -/
inductive DeriveAttributeRecoveredRejects : Remainder → Remainder → Prop where
  | hashMissing {input : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash)) :
      DeriveAttributeRecoveredRejects input input
  | openingMissing {input afterHash : Remainder} (hashSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingAbsent : TokenKindAbsentAt afterHash.tokens afterHash.endIndex
        afterHash.cursor (.symbol .leftBracket)) :
      DeriveAttributeRecoveredRejects input afterHash

end Solcore.Syntax.DeclarativeGrammar
