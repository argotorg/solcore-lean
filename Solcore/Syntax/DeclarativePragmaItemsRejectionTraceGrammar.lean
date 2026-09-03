import Solcore.Syntax.DeclarativePragmaTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent successful prefixes, uncommitted reports, and rejection events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The newly consumed checked names before the first rejecting tail item.
A comma followed by a semicolon is deliberately excluded from rejection. -/
inductive PragmaItemsTailRejectedPrefix :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | identifierRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol .semicolon))
      (itemRejected : IdentifierRejects afterComma rejected) :
      PragmaItemsTailRejectedPrefix input [] rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.Identifier} {consumed : List Syntax.Identifier}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailRejected : PragmaItemsTailRejectedPrefix afterItem consumed rejected) :
      PragmaItemsTailRejectedPrefix input (item :: consumed) rejected

/-- Complete item scanning retains its first item when a later suffix fails. -/
inductive PragmaItemsRejectedPrefix :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | firstIdentifierRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .semicolon))
      (firstRejected : IdentifierRejects input rejected) :
      PragmaItemsRejectedPrefix input [] rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier} {consumed : List Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailRejected : PragmaItemsTailRejectedPrefix afterFirst consumed rejected) :
      PragmaItemsRejectedPrefix input (first :: consumed) rejected

/-- Tail rejection exposes its exact endpoint and uncommitted identifier
report. Only new prefix names contribute diagnostic events; existing names
held by an enclosing accumulator are outside this relation. -/
def PragmaItemsTailTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  ∃ consumed, PragmaItemsTailRejectedPrefix input consumed rejected ∧
    IdentifierListDiagnosticTrace consumed trace ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl rejected diagnostic

/-- Rejected replies do not return a prefix AST, so the independently fixed
successful prefix is hidden while the endpoint, report, and events remain exact. -/
def PragmaItemsTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  ∃ consumed, PragmaItemsRejectedPrefix input consumed rejected ∧
    IdentifierListDiagnosticTrace consumed trace ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl rejected diagnostic

end Solcore.Syntax.DeclarativeGrammar
