import Solcore.Syntax.Parser.ExportPathTotalityProperties
import Solcore.Syntax.Parser.ExportTotalityProperties

/-! Export selection and local-item totality from an export-name contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

theorem exportSelection_invariantFreeOnValid
    (nameContract : ElementTotalityContract exportName) :
    Parser.InvariantFreeOnValid exportSelection := by
  intro input inputValid
  by_cases wildcard : isSymbol input .star
  · rcases (symbol_ordinary .star .exportDecl) input with
      ⟨marker, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨{ span := marker.span, value := .wildcard marker.span },
        next, by simp [exportSelection, wildcard, result]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [exportSelection, wildcard, result]⟩
  · rcases delimited_ordinary .leftBrace .rightBrace true exportName
        .exportDecl .topLevel nameContract input inputValid with
      ⟨items, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨{ span := items.span, value := .selected items }, next, by
        simp [exportSelection, wildcard, result]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [exportSelection, wildcard, result]⟩

theorem exportSelection_ordinary
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor) :
    (∃ selection next, exportSelection input = .ok selection next) ∨
    (∃ failure next, exportSelection input = .reject failure next) :=
  exportSelection_invariantFreeOnValid nameContract input inputValid

theorem exportSelection_ne_invariant
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportSelection input ≠ .invariant error :=
  (exportSelection_invariantFreeOnValid nameContract).ne_invariant
    input inputValid error

theorem localExportItem_invariantFreeOnValid
    (nameContract : ElementTotalityContract exportName) :
    Parser.InvariantFreeOnValid localExportItem := by
  intro input inputValid
  by_cases qualified : isIdentifier input &&
      isSymbol { input with cursor := input.cursor + 1 } .dot
  · rcases exportPath_ordinary input with
      ⟨path, afterPath, pathResult⟩ |
      ⟨failure, rejected, pathResult⟩
    · have pathValid := exportPath_validFor input inputValid
      rw [pathResult] at pathValid
      rcases (symbol_ordinary .dot .exportDecl) afterPath with
        ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
      · have dotValid := symbol_validFor .dot .exportDecl afterPath pathValid.2.1
        rw [dotResult] at dotValid
        rcases (symbol_ordinary .star .exportDecl) afterDot with
          ⟨marker, next, markerResult⟩ |
          ⟨failure, rejected, markerResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover path.span marker.span
              value := .moduleWildcard path marker.span
            }, next, by
              simp [localExportItem, qualified, pathResult, dotResult,
                markerResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp [localExportItem, qualified, pathResult, dotResult,
              markerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp [localExportItem, qualified, pathResult, dotResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [localExportItem, qualified, pathResult]⟩
  · have nameFree := Parser.invariantFreeOnValid_of_ne_invariant
      nameContract.invariantFree
    rcases nameFree input inputValid with
      ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · exact Or.inl ⟨{ span := name.span, value := .name name }, next, by
        simp [localExportItem, qualified, nameResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [localExportItem, qualified, nameResult]⟩

theorem localExportItem_ordinary
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, localExportItem input = .ok item next) ∨
    (∃ failure next, localExportItem input = .reject failure next) :=
  localExportItem_invariantFreeOnValid nameContract input inputValid

theorem localExportItem_ne_invariant
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    localExportItem input ≠ .invariant error :=
  (localExportItem_invariantFreeOnValid nameContract).ne_invariant
    input inputValid error

theorem localExportItem_cursor_lt_onSuccess
    (nameContract : ElementTotalityContract exportName)
    {input next : State} {item : LocalExportItem}
    (result : localExportItem input = .ok item next) :
    input.cursor < next.cursor := by
  unfold localExportItem at result
  split at result
  · cases pathResult : exportPath input with
    | reject failure rejected => simp [pathResult] at result
    | invariant error => simp [pathResult] at result
    | ok path afterPath =>
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | reject failure rejected => simp [dotResult] at result
        | invariant error => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | reject failure rejected => simp [markerResult] at result
            | invariant error => simp [markerResult] at result
            | ok marker final =>
                simp only [markerResult] at result
                have strict := Nat.lt_of_le_of_lt
                  (exportPath_cursorMonotoneOnSuccess input path afterPath
                    pathResult)
                  (Nat.lt_of_lt_of_le
                    (acceptToken_cursor_lt_onSuccess (.symbol .dot) .exportDecl
                      (· == .symbol .dot) dotResult)
                    (symbol_cursorMonotoneOnSuccess .star .exportDecl afterDot
                      marker final markerResult))
                cases result
                exact strict
  · cases nameResult : exportName input with
    | reject failure rejected => simp [nameResult] at result
    | invariant error => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        have strict := nameContract.cursorLtOnSuccess nameResult
        cases result
        exact strict

theorem localExportItem_elementTotalityContract
    (nameContract : ElementTotalityContract exportName) :
    ElementTotalityContract localExportItem := {
  validFor := localExportItem_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := localExportItem_preservesTokenWindow
  cursorLtOnSuccess := localExportItem_cursor_lt_onSuccess nameContract
  invariantFree := fun input inputValid error =>
    localExportItem_ne_invariant nameContract input inputValid error
}

end ExportInternals

theorem exportLeafTotalityContract
    (nameContract : ElementTotalityContract ExportInternals.exportName) :
    ExportLeafTotalityContract := {
  exportSelectionFree :=
    ExportInternals.exportSelection_invariantFreeOnValid nameContract
  localExportItem :=
    ExportInternals.localExportItem_elementTotalityContract nameContract
}

end Solcore.Syntax.Parser
