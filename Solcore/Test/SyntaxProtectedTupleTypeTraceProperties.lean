import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceProperties
import Solcore.Syntax.Parser.TupleTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Protected tuple child events remain ordered after every incoming diagnostic.
The separate rejection report is not added to this normalization suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedTupleTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_opening_keeps_entire_state (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .symbol .leftParen, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseTupleType nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .leftParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  apply parseTupleType_reject_iff_list.mpr
  simp only [delimited, delimitedWithPolicy, result]

theorem success_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input output report trace}, typeRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (TupleTypeTraceRejects.cascadeFilters successProtected rejectProtected rejection))

end Solcore.Test.SyntaxProtectedTupleTypeTraceProperties
