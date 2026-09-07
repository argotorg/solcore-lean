import Solcore.Syntax.Parser.NamedTypeFinishingTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Bare, qualified, and other names take distinct diagnostic branches. The
full named range includes any arguments; normalization keeps the full fresh
constraint event even when earlier diagnostics already contain duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedTypeFinishingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem bare_mapping_reports_full_named_span (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments)
      (input.emit {
        span := (namedTypeTraceValue name arguments).span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }) :=
  finishNamedType_eq_ok_of_trace name arguments input (.canonicalRequired ⟨bare, spelling⟩)

theorem mapping_arguments_extend_diagnostic_span (name : QualifiedName)
    (arguments : NonemptyDelimitedList TypeExpr) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    finishNamedType name (some arguments) input = .ok (namedTypeTraceValue name (some arguments))
      (input.emit {
        span := SourceSpan.cover name.span arguments.span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }) :=
  bare_mapping_reports_full_named_span name (some arguments) input bare spelling

theorem qualified_mapping_is_silent (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (qualified : name.value.components.tail ≠ []) :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments) input :=
  finishNamedType_eq_ok_of_trace name arguments input (.ordinary (fun spelling => qualified spelling.1))

theorem other_spelling_is_silent (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (other : name.value.components.head.value ≠ "mapping") :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments) input :=
  finishNamedType_eq_ok_of_trace name arguments input (.ordinary (fun spelling => other spelling.2))

theorem repeated_prior_mapping_reports_are_retained (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    let report : ParseDiagnostic := {
      span := (namedTypeTraceValue name arguments).span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }
    ∃ output, finishNamedType name arguments { input with diagnosticsRev := [report, report] } =
        .ok (namedTypeTraceValue name arguments) output ∧ output.diagnostics = [report, report, report] := by
  dsimp only
  exact ⟨_, bare_mapping_reports_full_named_span name arguments _ bare spelling, rfl⟩

theorem named_type_reports_survive_normalization
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {name : QualifiedName} {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {trace : List ParseDiagnostic} (events : NamedTypeFinishingTrace name arguments trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (events.cascadeFilters _ _)

end Solcore.Test.SyntaxNamedTypeFinishingTraceProperties
