import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.NameOperatorDiagnosticReflectionProperties

/-! Diagnostic-freedom reflection for canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExportInternals

private theorem exportPathTail_reflectsDiagnosticFreeOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next result diagnosticFree
      simp [exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next result diagnosticFree
      unfold exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next result
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
                    afterDot component afterComponent componentResult
                      afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl
                  input dot afterDot dotResult afterDotFree
      · unfold finishExportPath at result
        cases result
        exact diagnosticFree

private theorem exportPath_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportPath := by
  intro input value next result diagnosticFree
  unfold exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := exportPathTail_reflectsDiagnosticFreeOnSuccess
        first (afterFirst.remainingCount + 1) first [] afterFirst value next
          result diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl input first
        afterFirst firstResult afterFirstFree

private theorem requireConstructorNames_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireConstructorNames values) := by
  unfold requireConstructorNames
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem constructorSelection_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess constructorSelection := by
  unfold constructorSelection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .exportDecl)
    intro opening
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .exportDecl)
    intro closing
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
        .leftParen .rightParen false (identifier .exportDecl) .exportDecl
          .topLevel
            (identifier_reflectsDiagnosticFreeOnSuccess .exportDecl))
    intro values
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireConstructorNames_reflectsDiagnosticFreeOnSuccess values)
    intro constructors
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem exportName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportName := by
  intro input value next result diagnosticFree
  unfold exportName at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl input
          marker next markerResult diagnosticFree
  · split at result
    · cases selectorResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectorResult] at result
      | reject failure rejected => simp [selectorResult] at result
      | ok selected afterSelected =>
          simp only [selectorResult] at result
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at result
          | operator spelling =>
              simp only [selectedValue] at result
              cases result
              exact operatorSelector_reflectsDiagnosticFreeOnSuccess
                .exportDecl input selected next selectorResult diagnosticFree
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          split at result
          · cases constructorsResult : constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | reject failure rejected => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at result
                cases result
                have afterNameFree :=
                  constructorSelection_reflectsDiagnosticFreeOnSuccess
                    afterName constructors next constructorsResult
                      diagnosticFree
                exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
                  input name afterName nameResult afterNameFree
          · cases result
            exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
              input name next nameResult diagnosticFree

private theorem localExportItem_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess localExportItem := by
  intro input value next result diagnosticFree
  unfold localExportItem at result
  split at result
  · cases pathResult : exportPath input with
    | invariant error => simp [pathResult] at result
    | reject failure rejected => simp [pathResult] at result
    | ok path afterPath =>
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | reject failure rejected => simp [markerResult] at result
            | ok marker afterMarker =>
                simp only [markerResult] at result
                cases result
                have afterDotFree :=
                  symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl
                    afterDot marker next markerResult diagnosticFree
                have afterPathFree :=
                  symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl
                    afterPath dot afterDot dotResult afterDotFree
                exact exportPath_reflectsDiagnosticFreeOnSuccess input path
                  afterPath pathResult afterPathFree
  · cases nameResult : exportName input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact exportName_reflectsDiagnosticFreeOnSuccess input name next
          nameResult diagnosticFree

private theorem exportSelection_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportSelection := by
  intro input value next result diagnosticFree
  unfold exportSelection at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl input
          marker next markerResult diagnosticFree
  · cases itemsResult : delimited .leftBrace .rightBrace true exportName
        .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | reject failure rejected => simp [itemsResult] at result
    | ok items afterItems =>
        simp only [itemsResult] at result
        cases result
        exact delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace
          true exportName .exportDecl .topLevel
            exportName_reflectsDiagnosticFreeOnSuccess input items next
              itemsResult diagnosticFree

private theorem finishExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (value : ExportDeclValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess (finishExport start value) := by
  unfold finishExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .exportDecl)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem localExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (localExport start) := by
  unfold localExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace true
      localExportItem .exportDecl .topLevel
        localExportItem_reflectsDiagnosticFreeOnSuccess)
  intro items
  exact finishExport_reflectsDiagnosticFreeOnSuccess start (.local items)

private theorem pathExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (pathExport start) := by
  unfold pathExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    exportPath_reflectsDiagnosticFreeOnSuccess
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl)
    intro dot
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      exportSelection_reflectsDiagnosticFreeOnSuccess
    intro selection
    exact finishExport_reflectsDiagnosticFreeOnSuccess start
      (.itemsFrom path selection)
  · split
    · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (keyword_reflectsDiagnosticFreeOnSuccess .asKw .exportDecl)
      intro asMarker
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (identifier_reflectsDiagnosticFreeOnSuccess .exportDecl)
      intro alias
      exact finishExport_reflectsDiagnosticFreeOnSuccess start
        (.moduleAs path alias)
    · exact finishExport_reflectsDiagnosticFreeOnSuccess start (.module path)

end Solcore.Syntax.Parser.ExportInternals

namespace Solcore.Syntax.Parser

/-- Export parsing cannot erase an incoming diagnostic. -/
theorem exportDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportDecl := by
  unfold exportDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .exportKw .exportDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · exact ExportInternals.localExport_reflectsDiagnosticFreeOnSuccess
      marker.span
  · exact ExportInternals.pathExport_reflectsDiagnosticFreeOnSuccess
      marker.span

end Solcore.Syntax.Parser
