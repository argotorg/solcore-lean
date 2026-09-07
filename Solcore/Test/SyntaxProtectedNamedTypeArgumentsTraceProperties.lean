import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsTracePrimitiveProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Optional absence bypasses every recursive child. Protected child events
retain their full multiplicity on either selected outcome; the separate final
failure report is deliberately outside this normalization guarantee. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedNamedTypeArgumentsTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem absent_arguments_bypass_every_child (nested : Parser TypeExpr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .less)) :
    parseNamedTypeArguments nested input = .ok none input ∧
      ∀ failure rejected, parseNamedTypeArguments nested input ≠ .reject failure rejected := by
  have result := parseNamedTypeArguments_eq_none_of_absent nested absent
  exact ⟨result, by intro failure rejected; rw [result]; intro impossible; cases impossible⟩

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_arguments_keep_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {values : Option (NonemptyDelimitedList TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_arguments_keep_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxProtectedNamedTypeArgumentsTraceProperties
