import Solcore.Syntax.Parser.PragmaItemsRejectionTraceCompletenessProperties

/-! Consumers of exact item-rejection payloads and retained prefix events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaItemsRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaItemsTailRejectedPrefix.ordinary
example := @PragmaItemsTailRejects.exists_prefix
example := @PragmaItemsRejectedPrefix.ordinary
example := @PragmaItemsRejects.exists_prefix
example := @PragmaItemsTailRejectedPrefix.result_unique
example := @PragmaItemsRejectedPrefix.result_unique
example := @PragmaItemsTailTraceRejects.result_unique
example := @PragmaItemsTraceRejects.result_unique
example := @pragmaItemsTail_reject_trace_sound
example := @pragmaItems_reject_trace_sound

example (itemsRev : List Identifier) {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output,
      pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_reject_iff itemsRev).mp traced

example (itemsRev : List Identifier) {input output : State} {failure : Failure}
    {remainder : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  (pragmaItemsTail_production_trace_reject_iff itemsRev).mpr
    ⟨failure, output, result, after, report, diagnostics⟩

example {input : State} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure output, pragmaItems input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaItems_trace_reject_iff.mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaItems input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (report : failure.toDiagnostic = diagnostic)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace :=
  pragmaItems_trace_reject_iff.mpr ⟨failure, output, result, after, report, diagnostics⟩

example (itemsRev : List Identifier) {input : State} {failure : Failure}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace) :
    ∃ output,
      pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_reject_failure_iff itemsRev).mp traced

example {input output : State} {failure : Failure} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaItems input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace :=
  pragmaItems_trace_reject_failure_iff.mpr ⟨output, result, after, diagnostics⟩

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {span : SourceSpan} {found : Option TokenKind}
    (noSemicolon : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
    (noIdentifier : IdentifierRejects input rejected)
    (current : CurrentInputAt source endByte rejected span found) :
    PragmaItemsTraceRejects source endByte input rejected
      { span, kind := .unexpected found { head := .identifier, tail := [] } .pragmaDecl } [] :=
  ⟨[], .firstIdentifierRejected noSemicolon noIdentifier, .nil, .reported current⟩

example {source : SourceId} {endByte : Nat} {input afterFirst rejected : Remainder}
    (first second failureSpan : SourceSpan) (found : Option TokenKind)
    (noSemicolon : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .semicolon))
    (firstParsed : IdentifierParses input { span := first, value := "a-b" } afterFirst)
    (laterRejected : PragmaItemsTailRejectedPrefix afterFirst
      [{ span := second, value := "c--d" }] rejected)
    (current : CurrentInputAt source endByte rejected failureSpan found) :
    PragmaItemsTraceRejects source endByte input rejected
      { span := failureSpan,
        kind := .unexpected found { head := .identifier, tail := [] } .pragmaDecl }
      [{ span := first, kind := .invalidIdentifierHyphen "a-b" },
        { span := second, kind := .invalidIdentifierHyphen "c--d" }] :=
  ⟨_, .tailRejected noSemicolon firstParsed laterRejected,
    .cons (.hyphen (by change '-' ∈ "a-b".toList; decide))
      (.cons (.hyphen (by change '-' ∈ "c--d".toList; decide)) .nil),
    .reported current⟩

example {source : SourceId} {endByte : Nat} {input afterComma rejected : Remainder}
    {commaSpan : SourceSpan} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (comma : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
    (semicolon : PragmaItemsTokenPresentAt afterComma (.symbol .semicolon)) :
    ¬ PragmaItemsTailTraceRejects source endByte input rejected diagnostic trace := by
  rintro ⟨consumed, rejectedPrefix, _, _⟩
  exact pragmaItemsTailExactOutcomeSpec.successRejectDisjoint rejectedPrefix.ordinary
    ⟨[], afterComma, .trailing commaSpan ⟨commaSpan, comma.1⟩ comma semicolon⟩

example {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (semicolon : PragmaItemsTokenPresentAt input (.symbol .semicolon)) :
    ¬ PragmaItemsTraceRejects source endByte input rejected diagnostic trace := by
  rintro ⟨consumed, rejectedPrefix, _, _⟩
  exact pragmaItemsExactOutcomeSpec.successRejectDisjoint rejectedPrefix.ordinary
    ⟨[], input, .empty semicolon⟩

end Solcore.Test.SyntaxParserPragmaItemsRejectionTraceProperties
