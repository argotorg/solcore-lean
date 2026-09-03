import Solcore.Syntax.Parser.PragmaPrefixBoundaryTraceProperties

/-! Independent prefix order, cursor rewind, and single final-report consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaPrefixBoundaryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @PragmaPrefixBoundaryTraceParses.carrier_stop
example := @PragmaPrefixBoundaryTraceParses.length_lt_remaining
example := @PragmaPrefixBoundaryTraceParses.result_unique
example := @PragmaPrefixBoundaryTraceParses.cascadeFilters
example := @pragmaDecl_success_context_eq
example := @pragmaDecl_reject_context_eq
example := @parseItems_pragmaPrefixBoundary_trace_of_remainingCount_lt

example (fuel : Nat) (itemsRev : List TopItem) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace)
    (adequate : declarations.length < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  parseItems_pragmaPrefixBoundary_trace_of_length_lt fuel itemsRev parsed adequate

example (itemsRev : List TopItem) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  parseItems_production_pragmaPrefixBoundary_trace itemsRev parsed

example (comments : List Comment) {input : State}
    {declarations : List PragmaDecl} {stopped : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder declarations stopped diagnostic trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := (declarations.map wrapPragma).map (attachTopItemComments input.file comments)
        comments
      } output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  sourceFile_pragmaPrefixBoundary_trace comments parsed

example (prior : TopItem) {input : State}
    {first second : PragmaDecl} {afterFirst afterSecond afterKeyword rejected : Remainder}
    {firstTrace secondTrace rejectedTrace : List ParseDiagnostic}
    {marker : SourceSpan} {diagnostic : ParseDiagnostic}
    (firstParsed : PragmaDeclTraceParses input.declarativeRemainder first afterFirst firstTrace)
    (secondParsed : PragmaDeclTraceParses afterFirst second afterSecond secondTrace)
    (recognized : ExactTokenParses (.keyword .pragmaKw) afterSecond marker afterKeyword)
    (lastRejected : PragmaDeclTraceRejects input.file.id input.window.endByte
      afterSecond rejected diagnostic rejectedTrace) :
    ∃ output, parseItems (input.remainingCount + 1) [prior] input =
        .ok [prior, wrapPragma first, wrapPragma second] output ∧
      output.declarativeRemainder = afterSecond ∧
      output.diagnostics = input.diagnostics ++
        (firstTrace ++ secondTrace ++ rejectedTrace ++ [diagnostic]) := by
  have parsed := PragmaPrefixBoundaryTraceParses.cons firstParsed
    (.cons secondParsed (.stopped marker recognized lastRejected))
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_cons, List.map_nil, List.singleton_append, List.append_assoc] using
      parseItems_production_pragmaPrefixBoundary_trace [prior] parsed

example (itemsRev : List TopItem) {input : State}
    {afterKeyword rejected : Remainder} {marker : SourceSpan}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (recognized : ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker afterKeyword)
    (lastRejected : PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected diagnostic trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok itemsRev.reverse output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) := by
  simpa only [List.map_nil, List.append_nil] using
    parseItems_production_pragmaPrefixBoundary_trace itemsRev
      (.stopped marker recognized lastRejected)

example {source : SourceId} {endByte : Nat} {input stopped : Remainder}
    {declarations : List PragmaDecl} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : PragmaPrefixBoundaryTraceParses source endByte input
      declarations stopped diagnostic trace) :
    input.cursor ≤ stopped.cursor ∧ stopped.cursor < input.endIndex :=
  parsed.carrier_stop.2.2

example {input afterKeyword : Remainder} {marker : SourceSpan}
    (recognized : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .pragmaKw)) :
    False :=
  absent ⟨marker, recognized.1⟩

end Solcore.Test.SyntaxParserPragmaPrefixBoundaryTraceProperties
