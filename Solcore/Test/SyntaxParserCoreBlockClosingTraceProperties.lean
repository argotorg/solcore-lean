import Solcore.Syntax.Parser.CoreBlockClosingTraceProperties

/-! Independent tail checks and exact brace-closing diagnostic consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockClosingTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @closeCoreBlock_success_trace_sound
example := @closeCoreBlock_success_diagnostics_eq_of_trace
example := @closeCoreBlock_reject_iff_symbol
example := @closeCoreBlock_reject_reports
example := @closeCoreBlock_reject_reports_iff

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : Remainder} {trace : List ParseDiagnostic}
    (ordinary : ∃ closingSpan,
      ExactTokenParses (.symbol .rightBrace) input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse })
    (checked : CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace) :
    ∃ output, closeCoreBlock opening policy bodyRev input = .ok body output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (closeCoreBlock_trace_success_iff opening policy bodyRev).mp ⟨ordinary, checked⟩

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input output : State} {body : Block} {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : closeCoreBlock opening policy bodyRev input = .ok body output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    (∃ closingSpan,
      ExactTokenParses (.symbol .rightBrace) input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse }) ∧
      CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace :=
  (closeCoreBlock_trace_success_iff opening policy bodyRev).mpr
    ⟨output, result, after, diagnostics⟩

example (first last : SourceSpan) (left right : Expr) :
    CoreBlockTailsDiagnosticTrace .allow
      [{ span := first, value := .expression left false },
        { span := last, value := .expression right false }]
      [{ span := first, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  .cons (first := { span := first, value := .expression left false })
    (.missing (fun impossible => impossible)) .lastAllowed

example (opening : Token) {input : State} {closingSpan : SourceSpan} {remainder : Remainder}
    (first last : SourceSpan) (left right : Expr)
    (closing : ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder closingSpan remainder) :
    ∃ output, closeCoreBlock opening .require
        [{ span := last, value := .expression right false },
          { span := first, value := .expression left false }] input = .ok {
          span := SourceSpan.cover opening.span closingSpan
          value := [{ span := first, value := .expression left false },
            { span := last, value := .expression right false }]
        } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++
        [{ span := first, kind := .constraintViolation .expressionRequiresSemicolon },
          { span := last, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  (closeCoreBlock_trace_success_iff opening .require
    [{ span := last, value := .expression right false },
      { span := first, value := .expression left false }]).mp
    ⟨⟨closingSpan, closing, rfl⟩,
      .cons (first := { span := first, value := .expression left false })
      (.missing (fun impossible => impossible))
      (.lastRequired (.missing (fun impossible => impossible)))⟩

example (opening : Token) {input : State} {closingSpan : SourceSpan} {remainder : Remainder}
    (span : SourceSpan) (expression : Expr)
    (closing : ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder closingSpan remainder) :
    ∃ output, closeCoreBlock opening .allow
        [{ span, value := .expression expression false }] input = .ok {
          span := SourceSpan.cover opening.span closingSpan
          value := [{ span, value := .expression expression false }]
        } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil, List.reverse_cons, List.reverse_nil, List.nil_append] using
    (closeCoreBlock_trace_success_iff opening .allow
      [{ span, value := .expression expression false }] (trace := [])).mp
      ⟨⟨closingSpan, closing, rfl⟩, .lastAllowed⟩

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightBrace))
    (current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder span found) :
    closeCoreBlock opening policy bodyRev input = .reject
      { span, found, expected := { head := .symbol .rightBrace, tail := [] }, context := .statement }
      input :=
  (closeCoreBlock_reject_failure_iff opening policy bodyRev).mp ⟨absent, .reported current⟩

end Solcore.Test.SyntaxParserCoreBlockClosingTraceProperties
