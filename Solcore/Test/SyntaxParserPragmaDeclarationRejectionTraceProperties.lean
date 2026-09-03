import Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceCompletenessProperties

/-! Independent four-stage rejection consumers, without whole-state claims. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaDeclarationRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @pragmaDecl_reject_trace_sound

example {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  pragmaDecl_trace_reject_iff.mpr ⟨failure, output, result, after, report, diagnostics⟩

example {input : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace) :
    ∃ output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_failure_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace :=
  pragmaDecl_trace_reject_failure_iff.mpr ⟨output, result, after, diagnostics⟩

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (traced : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_reject_exact_of_trace result traced

example {input : State} {span : SourceSpan} {found : Option TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.keyword .pragmaKw))
    (current : CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .keyword .pragmaKw, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    (pragmaDecl_trace_reject_failure_iff (trace := [])).mp
      (.keywordMissing absent (.reported current))

example {input : State} {afterKeyword rejected : Remainder}
    {marker span : SourceSpan} {found : Option TokenKind}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (nameRejected : IdentifierRejects afterKeyword rejected)
    (current : CurrentInputAt input.file.id input.window.endByte rejected span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .identifier, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = rejected ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    (pragmaDecl_trace_reject_failure_iff (trace := [])).mp
      (.nameRejected marker keywordParsed nameRejected (.reported current))

example {input : State} {afterKeyword afterName rejected : Remainder}
    {marker nameSpan : SourceSpan} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (rawName : IdentifierParses afterKeyword { span := nameSpan, value := "raw-name" } afterName)
    (itemsRejected : PragmaItemsTraceRejects input.file.id input.window.endByte
      afterName rejected diagnostic trace) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_iff.mp (.itemsRejected marker keywordParsed rawName itemsRejected)

example {input : State} {afterKeyword afterName afterItems : Remainder}
    {marker span : SourceSpan} {found : Option TokenKind}
    {name : Identifier} {items : List Identifier} {trace : List ParseDiagnostic}
    (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (rawName : IdentifierParses afterKeyword name afterName)
    (itemsParsed : PragmaItemsTraceParses afterName items afterItems trace)
    (absent : TokenKindAbsentAt afterItems.tokens afterItems.endIndex
      afterItems.cursor (.symbol .semicolon))
    (current : CurrentInputAt input.file.id input.window.endByte afterItems span found) :
    ∃ output, pragmaDecl input = .reject
        { span, found, expected := { head := .symbol .semicolon, tail := [] }, context := .pragmaDecl }
        output ∧ output.declarativeRemainder = afterItems ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_reject_failure_iff.mp
    (.semicolonMissing marker keywordParsed rawName itemsParsed absent (.reported current))

end Solcore.Test.SyntaxParserPragmaDeclarationRejectionTraceProperties
