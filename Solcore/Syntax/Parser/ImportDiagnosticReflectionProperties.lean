import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.NameOperatorDiagnosticReflectionProperties

/-! Diagnostic-freedom reflection for canonical import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImportInternals

private theorem selectedAlias_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedAlias := by
  unfold selectedAlias
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .asKw .importDecl)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (identifier_reflectsDiagnosticFreeOnSuccess .importDecl)
    intro name
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end ImportInternals

private theorem selectedImport_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedImport := by
  unfold selectedImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (selectorName_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro source
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ImportInternals.selectedAlias_reflectsDiagnosticFreeOnSuccess
  intro alias
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

namespace ImportInternals

private theorem requireSelected_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList SelectedImport) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireSelected values) := by
  unfold requireSelected
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem selectedImports_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedImports := by
  unfold selectedImports
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel
      selectedImport_reflectsDiagnosticFreeOnSuccess)
  exact requireSelected_reflectsDiagnosticFreeOnSuccess

private theorem requireSelectorNames_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList SelectorName) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireSelectorNames values) := by
  unfold requireSelectorNames
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem hidingClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess hidingClause := by
  unfold hidingClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .hiding .importDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel
      (selectorName_reflectsDiagnosticFreeOnSuccess .importDecl))
  intro values
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (requireSelectorNames_reflectsDiagnosticFreeOnSuccess values)
  intro names
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem optionalHiding_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalHiding := by
  unfold optionalHiding
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      hidingClause_reflectsDiagnosticFreeOnSuccess
    intro clause
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem terminator_reflectsDiagnosticFreeOnSuccess
    (lastSpan : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (terminator lastSpan) := by
  intro input value next result diagnosticFree
  unfold terminator at result
  split at result
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .semicolon .importDecl
          input semicolon next semicolonResult diagnosticFree
  · split at result
    · cases result
      simp [State.emit] at diagnosticFree
    · simp [rejectAt] at result

private theorem finish_reflectsDiagnosticFreeOnSuccess
    (start last : SourceSpan) (value : ImportDeclValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess (finish start last value) := by
  unfold finish
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (terminator_reflectsDiagnosticFreeOnSuccess last)
  intro endSpan
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem plainImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (plainImport start) := by
  unfold plainImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  exact finish_reflectsDiagnosticFreeOnSuccess start path.span (.plain path)

private theorem namespaceImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (namespaceImport start) := by
  unfold namespaceImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .asKw .importDecl)
  intro asMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro alias
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  exact finish_reflectsDiagnosticFreeOnSuccess start path.span
    (.namespace path alias)

private theorem wildcardImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (wildcardImport start) := by
  unfold wildcardImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalHiding_reflectsDiagnosticFreeOnSuccess
  intro hidden
  exact finish_reflectsDiagnosticFreeOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

private theorem selectiveImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (selectiveImport start) := by
  unfold selectiveImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    selectedImports_reflectsDiagnosticFreeOnSuccess
  intro selection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalHiding_reflectsDiagnosticFreeOnSuccess
  intro hidden
  exact finish_reflectsDiagnosticFreeOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

end ImportInternals

/-- Import parsing cannot erase an incoming diagnostic. -/
theorem importDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess importDecl := by
  unfold importDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .importKw .importDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · split
    · exact ImportInternals.namespaceImport_reflectsDiagnosticFreeOnSuccess
        marker.span
    · exact ImportInternals.wildcardImport_reflectsDiagnosticFreeOnSuccess
        marker.span
  · split
    · exact ImportInternals.selectiveImport_reflectsDiagnosticFreeOnSuccess
        marker.span
    · exact ImportInternals.plainImport_reflectsDiagnosticFreeOnSuccess
        marker.span

end Solcore.Syntax.Parser
