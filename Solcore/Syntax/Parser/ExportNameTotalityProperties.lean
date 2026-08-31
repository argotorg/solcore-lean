import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.OperatorTotalityProperties

/-! Conditional totality for one exported selector name. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem operatorSelector_value_operator_onSuccess
    (context : ParseContext) {input next : State} {selected : SelectorName}
    (parsed : operatorSelector context input = .ok selected next) :
    ∃ spelling, selected.value = .operator spelling := by
  unfold operatorSelector at parsed
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      cases partsResult : OperatorInternals.operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at parsed
      | reject failure rejected => simp [partsResult] at parsed
      | ok parts afterParts =>
          simp only [partsResult] at parsed
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at parsed
          | reject failure rejected => simp [closingResult] at parsed
          | ok closing final =>
              simp only [closingResult] at parsed
              cases parsed
              exact ⟨String.join parts, rfl⟩

namespace ExportInternals

/--
Export-name dispatch is invariant-free once constructor selections are. The
operator branch cannot reach its defensive identifier/no-progress case because
`operatorSelector` success always constructs an operator selector.
-/
theorem exportName_invariantFreeOnValid
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection) :
    Parser.InvariantFreeOnValid exportName := by
  intro input inputValid
  unfold exportName
  split
  · rcases (symbol_ordinary .star .exportDecl) input with
      ⟨marker, next, markerResult⟩ | ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨{
          span := marker.span
          value := .wildcard marker.span
        }, next, by simp only [markerResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · split
    · rcases (operatorSelector_ordinary .exportDecl) input with
        ⟨selected, next, selectedResult⟩ |
        ⟨failure, rejected, selectedResult⟩
      · rcases operatorSelector_value_operator_onSuccess .exportDecl
          selectedResult with ⟨spelling, selectedShape⟩
        exact Or.inl ⟨{
            span := selected.span
            value := .operator { span := selected.span, value := spelling }
          }, next, by simp only [selectedResult, selectedShape]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [selectedResult]⟩
    · rcases (identifier_ordinary .exportDecl) input with
        ⟨name, afterName, nameResult⟩ |
        ⟨failure, rejected, nameResult⟩
      · have nameValid := identifier_validFor .exportDecl input inputValid
        rw [nameResult] at nameValid
        by_cases present : isSymbol afterName .leftParen
        · rcases constructorSelectionFree afterName nameValid.2.1 with
            ⟨constructors, next, constructorsResult⟩ |
            ⟨failure, rejected, constructorsResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover name.span constructors.span
                value := .identifier name (some constructors)
              }, next, by
                simp only [nameResult, present, if_true, constructorsResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [nameResult, present, if_true, constructorsResult]⟩
        · exact Or.inl ⟨{
              span := name.span
              value := .identifier name none
            }, afterName, by
              have absent : isSymbol afterName .leftParen = false := by
                cases found : isSymbol afterName .leftParen with
                | false => rfl
                | true => exact False.elim (present found)
              simp only [nameResult, absent, Bool.false_eq_true, if_false]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [nameResult]⟩

theorem exportName_ordinary
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection)
    (input : State) (inputValid : input.ValidFor) :
    (∃ name next, exportName input = .ok name next) ∨
      (∃ failure next, exportName input = .reject failure next) :=
  exportName_invariantFreeOnValid constructorSelectionFree input inputValid

theorem exportName_ne_invariant
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportName input ≠ .invariant error :=
  (exportName_invariantFreeOnValid constructorSelectionFree).ne_invariant
    input inputValid error

/-- Every successful export name consumes its leading marker or identifier. -/
theorem exportName_cursor_lt_onSuccess {input next : State}
    {exported : ExportName}
    (parsed : exportName input = .ok exported next) :
    input.cursor < next.cursor := by
  unfold exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact acceptToken_cursor_lt_onSuccess (.symbol .star) .exportDecl
          (· == .symbol .star) markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
              simp only [selectedValue] at parsed
              cases parsed
              exact operatorSelector_cursor_lt_onSuccess .exportDecl
                selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          have nameProgress : input.cursor < afterName.cursor := by
            rw [(identifier_ok_state_shape .exportDecl
              nameResult).choose_spec.2.2.2]
            simp
          split at parsed
          · cases constructorsResult : constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact Nat.lt_of_lt_of_le nameProgress
                  (constructorSelection_cursorMonotoneOnSuccess afterName
                    constructors next constructorsResult)
          · cases parsed
            exact nameProgress

/-- Conditional export-name totality instantiates the generic element API. -/
theorem exportName_elementTotalityContract
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection) :
    ElementTotalityContract exportName := {
  validFor := exportName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := exportName_preservesTokenWindow
  cursorLtOnSuccess := exportName_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    exportName_ne_invariant constructorSelectionFree input inputValid error
}

end ExportInternals

end Solcore.Syntax.Parser
