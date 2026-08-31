import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.ImportProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.OperatorTotalityProperties

/-! Totality for selected-import and hiding-clause parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem pure_ordinary {alpha : Type} (value : alpha) :
    Parser.Ordinary (pure value : Parser alpha) :=
  fun input => Or.inl ⟨value, input, rfl⟩

private theorem getState_ordinary : Parser.Ordinary getState :=
  fun input => Or.inl ⟨input, input, rfl⟩

private theorem bind_ordinary {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstOrdinary : Parser.Ordinary first)
    (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with
    ⟨firstValue, afterFirst, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · rcases nextOrdinary firstValue afterFirst with
      ⟨value, final, nextResult⟩ | ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨value, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- Optional selected-import aliases are ordinary on every input. -/
theorem selectedAlias_ordinary :
    Parser.Ordinary ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply bind_ordinary getState_ordinary
  intro observed
  by_cases present : isKeyword observed .asKw = true
  · simp only [present, if_true]
    apply bind_ordinary (keyword_ordinary .asKw .importDecl)
    intro marker
    apply bind_ordinary (identifier_ordinary .importDecl)
    intro name
    exact pure_ordinary (some name)
  · simp only [present, Bool.false_eq_true, if_false]
    exact pure_ordinary none

theorem selectedAlias_ne_invariant (input : State)
    (error : ParserInvariantError) :
    ImportInternals.selectedAlias input ≠ .invariant error :=
  selectedAlias_ordinary.ne_invariant input error

/-- One selected import is ordinary on every input. -/
theorem selectedImport_ordinary : Parser.Ordinary selectedImport := by
  unfold selectedImport
  apply bind_ordinary (selectorName_ordinary .importDecl)
  intro source
  apply bind_ordinary selectedAlias_ordinary
  intro alias
  exact pure_ordinary _

theorem selectedImport_ne_invariant (input : State)
    (error : ParserInvariantError) :
    selectedImport input ≠ .invariant error :=
  selectedImport_ordinary.ne_invariant input error

/-- A selected import strictly consumes its leading selector. -/
theorem selectedImport_cursor_lt_onSuccess {input next : State}
    {selection : SelectedImport}
    (parsed : selectedImport input = .ok selection next) :
    input.cursor < next.cursor := by
  unfold selectedImport at parsed
  cases sourceResult : selectorName .importDecl input with
  | invariant error =>
      simp only [bind, sourceResult] at parsed
      contradiction
  | reject failure rejected =>
      simp only [bind, sourceResult] at parsed
      contradiction
  | ok source afterSource =>
      simp only [sourceResult, bind] at parsed
      cases aliasResult : ImportInternals.selectedAlias afterSource with
      | invariant error => simp [aliasResult] at parsed
      | reject failure rejected => simp [aliasResult] at parsed
      | ok alias afterAlias =>
          simp only [aliasResult, pure] at parsed
          cases parsed
          exact Nat.lt_of_lt_of_le
            (selectorName_cursor_lt_onSuccess .importDecl sourceResult)
            (selectedAlias_cursorMonotoneOnSuccess afterSource alias next
              aliasResult)

/-- Selected imports instantiate the generic delimited-element boundary. -/
theorem selectedImport_elementTotalityContract :
    ElementTotalityContract selectedImport := {
  validFor := selectedImport_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := selectedImport_preservesTokenWindow
  cursorLtOnSuccess := selectedImport_cursor_lt_onSuccess
  invariantFree := fun input _inputValid error =>
    selectedImport_ne_invariant input error
}

namespace ImportInternals

/-- A successful nonempty selected list makes `requireSelected` ordinary. -/
theorem requireSelected_ordinary_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectedImport}
    (parsed : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input = .ok values afterValues) :
    Parser.Ordinary (requireSelected values) := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess
    .leftBrace .rightBrace selectedImport .importDecl .topLevel parsed
  unfold requireSelected
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact pure_ordinary _

theorem requireSelected_ne_invariant_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectedImport}
    (parsed : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input = .ok values afterValues)
    (state : State) (error : ParserInvariantError) :
    requireSelected values state ≠ .invariant error :=
  (requireSelected_ordinary_of_delimited_success parsed).ne_invariant
    state error

/-- A successful nonempty hiding list makes its shape check ordinary. -/
theorem requireSelectorNames_ordinary_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectorName}
    (parsed : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values afterValues) :
    Parser.Ordinary (requireSelectorNames values) := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess
    .leftBrace .rightBrace (selectorName .importDecl) .importDecl .topLevel
    parsed
  unfold requireSelectorNames
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact pure_ordinary _

theorem requireSelectorNames_ne_invariant_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectorName}
    (parsed : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values afterValues)
    (state : State) (error : ParserInvariantError) :
    requireSelectorNames values state ≠ .invariant error :=
  (requireSelectorNames_ordinary_of_delimited_success parsed).ne_invariant
    state error

/-- Selected-import lists have only ordinary replies on valid input. -/
theorem selectedImports_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ selection next, selectedImports input = .ok selection next) ∨
      (∃ failure next, selectedImports input = .reject failure next) := by
  rcases delimited_ordinary .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel selectedImport_elementTotalityContract input
      inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · rcases requireSelected_ordinary_of_delimited_success valuesResult
      afterValues with
      ⟨selection, next, selectionResult⟩ |
      ⟨failure, rejected, selectionResult⟩
    · exact Or.inl ⟨selection, next, by
        unfold selectedImports
        simp only [bind, valuesResult, selectionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold selectedImports
        simp only [bind, valuesResult, selectionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold selectedImports
      simp only [bind, valuesResult]⟩

theorem selectedImports_invariantFreeOnValid :
    Parser.InvariantFreeOnValid selectedImports :=
  selectedImports_ordinary

theorem selectedImports_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    selectedImports input ≠ .invariant error :=
  selectedImports_invariantFreeOnValid.ne_invariant input inputValid error

/-- Hiding clauses have only ordinary replies on valid input. -/
theorem hidingClause_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, hidingClause input = .ok clause next) ∨
      (∃ failure next, hidingClause input = .reject failure next) := by
  rcases (contextual_ordinary .hiding .importDecl) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := contextual_validFor .hiding .importDecl
      input inputValid
    rw [markerResult] at markerReply
    rcases delimited_ordinary .leftBrace .rightBrace false
        (selectorName .importDecl) .importDecl .topLevel
        (selectorName_elementTotalityContract .importDecl) afterMarker
        markerReply.2.1 with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · rcases requireSelectorNames_ordinary_of_delimited_success valuesResult
        afterValues with
        ⟨names, afterNames, namesResult⟩ |
        ⟨failure, rejected, namesResult⟩
      · refine Or.inl ⟨{
            span := SourceSpan.cover marker.span values.span
            value := { names }
          }, afterNames, ?_⟩
        unfold hidingClause
        simp only [bind, markerResult, valuesResult, namesResult, pure]
      · exact Or.inr ⟨failure, rejected, by
          unfold hidingClause
          simp only [bind, markerResult, valuesResult, namesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold hidingClause
        simp only [bind, markerResult, valuesResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold hidingClause
      simp only [bind, markerResult]⟩

theorem hidingClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid hidingClause :=
  hidingClause_ordinary

theorem hidingClause_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    hidingClause input ≠ .invariant error :=
  hidingClause_invariantFreeOnValid.ne_invariant input inputValid error

/-- Optional hiding dispatch has only ordinary replies on valid input. -/
theorem optionalHiding_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, optionalHiding input = .ok clause next) ∨
      (∃ failure next, optionalHiding input = .reject failure next) := by
  unfold optionalHiding
  simp only [getState, bind]
  split
  · rcases hidingClause_ordinary input inputValid with
      ⟨clause, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨some clause, next, by simp only [result, pure]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [result]⟩
  · exact Or.inl ⟨none, input, rfl⟩

theorem optionalHiding_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalHiding :=
  optionalHiding_ordinary

theorem optionalHiding_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    optionalHiding input ≠ .invariant error :=
  optionalHiding_invariantFreeOnValid.ne_invariant input inputValid error

end ImportInternals

end Solcore.Syntax.Parser
