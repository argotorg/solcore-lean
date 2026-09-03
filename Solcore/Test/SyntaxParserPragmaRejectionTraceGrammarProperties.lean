import Solcore.Syntax.DeclarativePragmaRejectionTraceProperties

/-! Independent first-failure reports and protected prior pragma events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaRejectionTraceGrammarProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

example (source : SourceId) (endByte : Nat) {input rejected : Remainder}
    (ordinary : PragmaDeclRejects input rejected) :
    ∃ diagnostic trace, PragmaDeclTraceRejects source endByte input rejected diagnostic trace :=
  ordinary.exists_trace source endByte

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
    PragmaDeclRejects input rejected := traced.ordinary

example {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaDeclTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaDeclTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace :=
  left.result_unique right

example {source : SourceId} {endByte : Nat} {input : Remainder} {diagnostic : ParseDiagnostic}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw))
    (reported : RejectAtReports source endByte { head := .keyword .pragmaKw, tail := [] }
      .pragmaDecl input diagnostic) :
    PragmaDeclTraceRejects source endByte input input diagnostic [] :=
  .keywordMissing absent reported

example {source : SourceId} {endByte : Nat} {input afterKeyword : Remainder}
    {marker : SourceSpan} {diagnostic : ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (absent : IdentifierAbsentAt afterKeyword)
    (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
      .pragmaDecl afterKeyword diagnostic) :
    PragmaDeclTraceRejects source endByte input afterKeyword diagnostic [] :=
  .nameRejected marker keywordParsed (.absent absent) reported

example {source : SourceId} {endByte : Nat} {input afterKeyword afterName rejected : Remainder}
    {marker : SourceSpan} {name : Identifier} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (nameParsed : IdentifierParses afterKeyword name afterName)
    (itemsRejected : PragmaItemsTraceRejects source endByte afterName rejected diagnostic trace) :
    PragmaDeclTraceRejects source endByte input rejected diagnostic trace :=
  .itemsRejected marker keywordParsed nameParsed itemsRejected

example {source : SourceId} {endByte : Nat} {input afterKeyword afterName afterItems : Remainder}
    {marker : SourceSpan} {name : Identifier} {items : List Identifier}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (nameParsed : IdentifierParses afterKeyword name afterName)
    (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
    (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex afterItems.cursor (.symbol .semicolon))
    (reported : RejectAtReports source endByte { head := .symbol .semicolon, tail := [] }
      .pragmaDecl afterItems diagnostic) :
    PragmaDeclTraceRejects source endByte input afterItems diagnostic trace :=
  .semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported

/-- A rejected declaration's already emitted names stay protected; its distinct
uncommitted report is deliberately not inserted into this raw filtering claim. -/
example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  traced.cascadeFilters text lexical

end Solcore.Test.SyntaxParserPragmaRejectionTraceGrammarProperties
