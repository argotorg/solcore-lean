import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Independent existence, unique complete events, and protected normalization
for named-type construction. No assumption about canonical source is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeFinishingTrace_exists (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) :
    ∃ trace, NamedTypeFinishingTrace name arguments trace := by
  by_cases spelling : UnqualifiedMappingSpelling name
  · exact ⟨_, .canonicalRequired spelling⟩
  · exact ⟨_, .ordinary spelling⟩

theorem NamedTypeFinishingTrace.trace_unique {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)} {left right : List ParseDiagnostic}
    (leftTrace : NamedTypeFinishingTrace name arguments left)
    (rightTrace : NamedTypeFinishingTrace name arguments right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

theorem NamedTypeFinishingTrace.cascadeFilters {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : NamedTypeFinishingTrace name arguments trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary => exact .nil
  | canonicalRequired => exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

end Solcore.Syntax.DeclarativeGrammar
