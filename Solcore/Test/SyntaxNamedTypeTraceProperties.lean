import Solcore.Syntax.Parser.NamedTypeTraceProperties
import Solcore.Syntax.Parser.NamedTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Complete raw named-type consumers separate the final spelling constraint
from argument failure. They preserve arbitrary intermediate states/events and
do not assume recursive type execution or dispatcher selection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem no_arguments_bypass_any_child (nested : Parser TypeExpr)
    {input afterName : State} {name : QualifiedName} {trace : List ParseDiagnostic}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (absent : TokenKindAbsentAt afterName.tokens afterName.window.endIndex afterName.cursor (.symbol .less))
    (finished : NamedTypeFinishingTrace name none trace) :
    parseNamedType nested input = .ok (namedTypeTraceValue name none)
      { afterName with diagnosticsRev := trace.reverse ++ afterName.diagnosticsRev } :=
  parseNamedType_success_iff_components.mpr ⟨name, afterName, none, afterName,
    nameResult, parseNamedTypeArguments_eq_none_of_absent nested absent,
    finishNamedType_eq_ok_of_trace name none afterName finished⟩

theorem mapping_constraint_follows_all_argument_events (nested : Parser TypeExpr)
    {input afterName afterArguments : State} {name : QualifiedName}
    {arguments : NonemptyDelimitedList TypeExpr} {nameEvents argumentEvents : List ParseDiagnostic}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (argumentsResult : parseNamedTypeArguments nested afterName = .ok (some arguments) afterArguments)
    (spelling : UnqualifiedMappingSpelling name)
    (nameEq : afterName.diagnostics = input.diagnostics ++ nameEvents)
    (argumentsEq : afterArguments.diagnostics = afterName.diagnostics ++ argumentEvents) :
    ∃ output, parseNamedType nested input = .ok (namedTypeTraceValue name (some arguments)) output ∧
      output = { afterArguments with diagnosticsRev := {
        span := (namedTypeTraceValue name (some arguments)).span
        kind := .constraintViolation .mappingRequiresCanonicalForm } :: afterArguments.diagnosticsRev } ∧
      output.diagnostics = input.diagnostics ++ nameEvents ++ argumentEvents ++ [{
        span := (namedTypeTraceValue name (some arguments)).span
        kind := .constraintViolation .mappingRequiresCanonicalForm }] := by
  refine ⟨_, parseNamedType_success_iff_components.mpr ⟨name, afterName, some arguments, afterArguments,
    nameResult, argumentsResult,
    finishNamedType_eq_ok_of_trace name (some arguments) afterArguments (.canonicalRequired spelling)⟩, rfl, ?_⟩
  simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  change afterArguments.diagnostics ++ [_] = _
  rw [argumentsEq, nameEq]
  rfl

theorem argument_failure_bypasses_finishing (nested : Parser TypeExpr)
    {input afterName rejected : State} {name : QualifiedName} {failure : Failure}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (argumentsResult : parseNamedTypeArguments nested afterName = .reject failure rejected) :
    parseNamedType nested input = .reject failure rejected :=
  parseNamedType_reject_iff_components.mpr (.inr ⟨name, afterName, nameResult, argumentsResult⟩)

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_named_type_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_named_type_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxNamedTypeTraceProperties
