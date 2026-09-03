import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! Independent token absence determines exact uncommitted primitive reports.
No source validity, diagnostic validity, or executable outcome is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem acceptToken_eq_rejectAt_of_absence
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) (kind : TokenKind) {input : State}
    (sound : ∀ {output : State} {token : Token},
      acceptToken expected context accepts input = .ok token output →
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
        { span := token.span, value := kind })
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind) :
    acceptToken expected context accepts input =
      rejectAt input { head := expected, tail := [] } context := by
  unfold acceptToken
  cases found : input.peek? with
  | none => rfl
  | some token =>
      simp only
      split
      next accepted =>
        have result : acceptToken expected context accepts input =
            .ok token { input with cursor := input.cursor + 1 } := by
          simp only [acceptToken, found, accepted, if_true]
        exact False.elim (absent ⟨token.span, sound result⟩)
      next => rfl

/-- An absent hard keyword yields the exact retained-state failure. -/
theorem keyword_eq_rejectAt_of_tokenKindAbsent
    (value : HardKeyword) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword value)) :
    keyword value context input =
      rejectAt input { head := .keyword value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.keyword value) context
    (· == .keyword value) (.keyword value)
    (fun result => (keyword_ok_tokenAt value context result).1) absent

/-- An absent symbol yields the exact retained-state failure. -/
theorem symbol_eq_rejectAt_of_tokenKindAbsent
    (value : Symbol) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.symbol value)) :
    symbol value context input =
      rejectAt input { head := .symbol value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.symbol value) context
    (· == .symbol value) (.symbol value)
    (fun result => (symbol_ok_tokenAt value context result).1) absent

/-- Contextual absence concerns its identifier spelling; the report retains
the contextual expectation rather than replacing it with identifier. -/
theorem contextual_eq_rejectAt_of_tokenKindAbsent
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.identifier value.spelling)) :
    contextual value context input =
      rejectAt input { head := .contextual value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.contextual value) context
    (·.isContextual value) (.identifier value.spelling)
    (fun result => (contextual_ok_tokenAt value context result).1) absent

private theorem exactToken_reject_reports_iff
    (parser : Parser Token) (kind : TokenKind)
    (expected : ParseExpectation) (context : ParseContext) {input : State}
    (complete : ∀ {span : SourceSpan} {after : DeclarativeGrammar.Remainder},
      DeclarativeGrammar.ExactTokenParses kind input.declarativeRemainder span after →
      parser input = .ok { span, value := kind } { input with cursor := input.cursor + 1 })
    (rejects : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind →
      parser input = rejectAt input { head := expected, tail := [] } context)
    {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor kind ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := expected, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, parser input = .reject failure input ∧ failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Token)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure, (rejects absent).trans result, reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
        input.window.endIndex input.cursor kind := by
      rintro ⟨span, present⟩
      have success := complete (after := { input.declarativeRemainder with
        cursor := input.cursor + 1 }) ⟨present, rfl⟩
      rw [success] at result
      contradiction
    refine ⟨absent, (rejectAt_reports_iff (alpha := Token)).mpr ?_⟩
    exact ⟨failure, (rejects absent).symm.trans result, reportEq⟩

/-- Hard-keyword absence and its independently reported payload exactly
characterize rejection, including the unchanged complete input state. -/
theorem keyword_reject_reports_iff
    (value : HardKeyword) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.keyword value) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .keyword value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, keyword value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (keyword value context) (.keyword value) (.keyword value)
    context (keyword_eq_ok_of_exactTokenParses value context)
    (keyword_eq_rejectAt_of_tokenKindAbsent value context)

/-- Symbol absence and its independent report exactly characterize silent rejection. -/
theorem symbol_reject_reports_iff
    (value : Symbol) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol value) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, symbol value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (symbol value context) (.symbol value) (.symbol value)
    context (symbol_eq_ok_of_exactTokenParses value context)
    (symbol_eq_rejectAt_of_tokenKindAbsent value context)

/-- Contextual spelling absence yields the exact contextual report, not an
identifier expectation, while keeping the whole input and diagnostic sequence. -/
theorem contextual_reject_reports_iff
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.identifier value.spelling) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .contextual value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, contextual value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (contextual value context) (.identifier value.spelling)
    (.contextual value) context (contextual_eq_ok_of_exactTokenParses value context)
    (contextual_eq_rejectAt_of_tokenKindAbsent value context)

/-- Arbitrary primitive rejection realizes the independent report and emits
no event, even when the supplied state or earlier diagnostics are invalid. -/
theorem acceptToken_reject_reports
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input rejected : State} {failure : Failure}
    (result : acceptToken expected context accepts input = .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := expected, tail := [] } context input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_reports _ context result
  | some token =>
      simp only [found] at result
      split at result
      · contradiction
      · exact rejectAt_reject_reports _ context result

/-- A rejected keyword preserves the exact existing diagnostic order. -/
theorem keyword_reject_diagnostics_eq
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.keyword value) context (· == .keyword value) result).2

/-- A rejected symbol preserves the exact existing diagnostic order. -/
theorem symbol_reject_diagnostics_eq
    (value : Symbol) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.symbol value) context (· == .symbol value) result).2

/-- A rejected contextual spelling preserves the exact existing diagnostic order. -/
theorem contextual_reject_diagnostics_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.contextual value) context (·.isContextual value) result).2

end Solcore.Syntax.Parser
