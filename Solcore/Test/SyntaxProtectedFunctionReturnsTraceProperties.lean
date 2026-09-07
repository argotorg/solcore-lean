import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Optional returns preserve the complete state on absence. Protected child
events survive normalization in order; the terminal report stays uncommitted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedFunctionReturnsTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals

theorem absent_keeps_entire_state (nested : Parser TypeExpr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.returns.spelling)) :
    parseFunctionReturns nested input = .ok none input :=
  parseFunctionReturns_eq_none_of_absent nested absent

theorem success_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {values : Option (DelimitedList TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses typeTrace source endByte input values output trace) :
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
    (rejection : FunctionReturnsTraceRejects typeTrace typeRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

end Solcore.Test.SyntaxProtectedFunctionReturnsTraceProperties
