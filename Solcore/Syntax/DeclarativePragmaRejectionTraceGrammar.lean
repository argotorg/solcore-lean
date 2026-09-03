import Solcore.Syntax.DeclarativePragmaItemsRejectionTraceGrammar

/-! Exact first-failure pragma traces, separating emitted events from the
uncommitted report. Source and window-end byte remain explicit context. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Each rejecting stage retains only checked-item events already emitted;
the failure report itself is not committed until an enclosing recovery does so. -/
inductive PragmaDeclTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | keywordMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw))
      (reported : RejectAtReports source endByte
        { head := .keyword .pragmaKw, tail := [] } .pragmaDecl input diagnostic) :
      PragmaDeclTraceRejects source endByte input input diagnostic []
  | nameRejected {input afterKeyword rejected : Remainder} {diagnostic : ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected)
      (reported : RejectAtReports source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected diagnostic) :
      PragmaDeclTraceRejects source endByte input rejected diagnostic []
  | itemsRejected {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsRejected : PragmaItemsTraceRejects source endByte afterName rejected diagnostic trace) :
      PragmaDeclTraceRejects source endByte input rejected diagnostic trace
  | semicolonMissing {input afterKeyword afterName afterItems : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
      (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex
        afterItems.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte
        { head := .symbol .semicolon, tail := [] } .pragmaDecl afterItems diagnostic) :
      PragmaDeclTraceRejects source endByte input afterItems diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
