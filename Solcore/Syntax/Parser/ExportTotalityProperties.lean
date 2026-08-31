import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.InvariantFreeProperties

/-! Totality boundary for local, path, and public export dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
The three leaf obligations below are exactly the export-specific work below
public dispatch: path fuel, export-name defenses, and delimited item progress.
-/
structure ExportLeafTotalityContract : Prop where
  exportPathFree : Parser.InvariantFreeOnValid ExportInternals.exportPath
  exportSelectionFree :
    Parser.InvariantFreeOnValid ExportInternals.exportSelection
  localExportItem : ElementTotalityContract ExportInternals.localExportItem

namespace ExportInternals

theorem finishExport_invariantFreeOnValid (start : SourceSpan)
    (value : ExportDeclValue) :
    Parser.InvariantFreeOnValid (finishExport start value) := by
  unfold finishExport
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .exportDecl)
    (symbol_ordinary .semicolon .exportDecl).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover start semicolon.span
    value
  } : ExportDecl)

theorem finishExport_ne_invariant (start : SourceSpan)
    (value : ExportDeclValue) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    finishExport start value input ≠ .invariant error :=
  (finishExport_invariantFreeOnValid start value).ne_invariant
    input inputValid error

theorem localExport_invariantFreeOnValid (contract : ExportLeafTotalityContract)
    (start : SourceSpan) :
    Parser.InvariantFreeOnValid (localExport start) := by
  unfold localExport
  apply Parser.bind_invariantFreeOnValid
    (delimited_validFor LocalExportItem.ValidFor .leftBrace .rightBrace true
      localExportItem .exportDecl .topLevel localExportItem_validFor
      localExportItem_preservesTokensOnSuccess)
  · exact Parser.invariantFreeOnValid_of_ne_invariant
      (delimited_ne_invariant .leftBrace .rightBrace true localExportItem
        .exportDecl .topLevel contract.localExportItem)
  · intro items
    exact finishExport_invariantFreeOnValid start (.local items)

theorem localExport_ordinary (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor) :
    (∃ value next, localExport start input = .ok value next) ∨
    (∃ failure next, localExport start input = .reject failure next) :=
  localExport_invariantFreeOnValid contract start input inputValid

theorem localExport_ne_invariant (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    localExport start input ≠ .invariant error :=
  (localExport_invariantFreeOnValid contract start).ne_invariant
    input inputValid error

theorem pathExport_invariantFreeOnValid (contract : ExportLeafTotalityContract)
    (start : SourceSpan) :
    Parser.InvariantFreeOnValid (pathExport start) := by
  unfold pathExport
  apply Parser.bind_invariantFreeOnValid exportPath_validFor
    contract.exportPathFree
  intro path
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  by_cases dotted : isSymbol state .dot
  · simp only [dotted, if_true]
    apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .dot .exportDecl)
      (symbol_ordinary .dot .exportDecl).invariantFreeOnValid
    intro dot
    apply Parser.bind_invariantFreeOnValid exportSelection_validFor
      contract.exportSelectionFree
    intro selection
    exact finishExport_invariantFreeOnValid start (.itemsFrom path selection)
  · simp only [dotted]
    by_cases aliased : isKeyword state .asKw
    · simp only [aliased, if_true]
      apply Parser.bind_invariantFreeOnValid
        (keyword_validFor .asKw .exportDecl)
        (keyword_ordinary .asKw .exportDecl).invariantFreeOnValid
      intro asKeyword
      apply Parser.bind_invariantFreeOnValid
        (identifier_validFor .exportDecl)
        (identifier_ordinary .exportDecl).invariantFreeOnValid
      intro alias
      exact finishExport_invariantFreeOnValid start (.moduleAs path alias)
    · simp only [aliased]
      exact finishExport_invariantFreeOnValid start (.module path)

theorem pathExport_ordinary (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor) :
    (∃ value next, pathExport start input = .ok value next) ∨
    (∃ failure next, pathExport start input = .reject failure next) :=
  pathExport_invariantFreeOnValid contract start input inputValid

theorem pathExport_ne_invariant (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    pathExport start input ≠ .invariant error :=
  (pathExport_invariantFreeOnValid contract start).ne_invariant
    input inputValid error

end ExportInternals

theorem exportDecl_invariantFreeOnValid (contract : ExportLeafTotalityContract) :
    Parser.InvariantFreeOnValid exportDecl := by
  unfold exportDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .exportKw .exportDecl)
    (keyword_ordinary .exportKw .exportDecl).invariantFreeOnValid
  intro exportKeyword
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  by_cases isLocal : isSymbol state .leftBrace
  · simp only [isLocal, if_true]
    exact ExportInternals.localExport_invariantFreeOnValid contract
      exportKeyword.span
  · simp only [isLocal]
    exact ExportInternals.pathExport_invariantFreeOnValid contract
      exportKeyword.span

theorem exportDecl_ordinary (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, exportDecl input = .ok value next) ∨
    (∃ failure next, exportDecl input = .reject failure next) :=
  exportDecl_invariantFreeOnValid contract input inputValid

theorem exportDecl_ne_invariant (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  (exportDecl_invariantFreeOnValid contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
