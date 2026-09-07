import Solcore.Syntax.DeclarativeTypeDispatchTraceProperties

/-! Selected trace erasure recovers the older ordinary type layer. Positive
selection eliminates raw missing-prefix failures; named erasure receives the
comptime/mapping exclusions that are absent from the raw named grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TypeDispatchTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.ordinary childOrdinary childWindow
      case comptime => exact raw.ordinary childOrdinary
      case mapping =>
        rcases raw.ordinary_components childOrdinary with
          ⟨markerSpan, openingSpan, arrowSpan, closingSpan, afterMarker, afterOpening, afterKey,
            afterArrow, afterValue, key, value, marker, opening, keyParsed, arrow, valueParsed, closing, rfl⟩
        exact .mapping markerSpan openingSpan arrowSpan closingSpan marker opening arrow closing rfl keyParsed valueParsed
      case proxy => exact raw.ordinary childOrdinary
      case tuple => exact raw.ordinary childOrdinary childWindow
      case named =>
        cases selection with
        | named _ comptimeAbsent mappingAbsent _ _ _ =>
            rcases raw.ordinary_components childOrdinary childWindow with
              ⟨name, afterName, arguments, nameParsed, argumentsParsed, rfl⟩
            exact .named comptimeAbsent mappingAbsent nameParsed (by cases arguments <;> rfl) argumentsParsed

theorem TypeDispatchTraceRejects.ordinary
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeExprCoreRejects ordinaryRejects input rejected := by
  cases rejection with
  | selected branch selection raw =>
      cases selection with
      | function present =>
          rcases present with ⟨span, marker⟩
          exact .function (FunctionTypeTraceRejects.ordinary_of_marker_present
            successErases rejectErases childWindow (afterKeyword := { input with cursor := input.cursor + 1 })
            ⟨marker, rfl⟩ raw)
      | comptime functionAbsent present =>
          rcases present.exact_prefix with ⟨_, _, _, _, marker, opening⟩
          exact .comptime functionAbsent
            (ComptimeTypeTraceRejects.ordinary_of_prefix successErases rejectErases marker opening raw)
      | mapping functionAbsent comptimeAbsent present =>
          rcases present.exact_prefix with ⟨_, _, _, _, marker, opening⟩
          exact .mapping functionAbsent comptimeAbsent
            (MappingTypeTraceRejects.ordinary_of_prefix successErases rejectErases marker opening raw)
      | proxy functionAbsent comptimeAbsent mappingAbsent present =>
          exact .proxy functionAbsent comptimeAbsent mappingAbsent
            (ProxyTypeTraceRejects.ordinary_of_marker_present rejectErases present raw)
      | tuple functionAbsent comptimeAbsent mappingAbsent atAbsent present =>
          exact .tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
            (TupleTypeTraceRejects.ordinary_of_opening_present successErases rejectErases present raw)
      | named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent present =>
          exact .named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent present
            (NamedTypeTraceRejects.ordinary successErases rejectErases raw)
      | final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent identifierAbsent =>
          cases raw
          exact .final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent identifierAbsent

end Solcore.Syntax.DeclarativeGrammar
