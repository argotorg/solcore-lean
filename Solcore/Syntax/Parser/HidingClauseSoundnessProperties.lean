import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.PlainImportSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

/-! Success soundness of hiding clauses and their optional boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- `requireSelectorNames` only changes the list carrier, never parser state. -/
theorem requireSelectorNames_success_shape
    {values : DelimitedList SelectorName} {input next : State}
    {names : NonemptyList SelectorName}
    (result : ImportInternals.requireSelectorNames values input =
      .ok names next) :
    next = input ∧ names.toList = values.elements := by
  unfold ImportInternals.requireSelectorNames at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      simp only [pure] at result
      cases result
      exact ⟨rfl, by simp [NonemptyList.toList]⟩

/-- Every hiding clause follows the exact nonempty selector-list grammar. -/
theorem hidingClause_success_sound {input next : State}
    {clause : HidingClause}
    (result : ImportInternals.hidingClause input = .ok clause next) :
    DeclarativeGrammar.HidingClauseParses input.declarativeRemainder clause
      next.declarativeRemainder := by
  unfold ImportInternals.hidingClause at result
  rcases importBind_success_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases importBind_success_components rest with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases importBind_success_components rest with
    ⟨names, afterNames, namesResult, finished⟩
  cases finished
  have markerSound := contextual_ok_tokenAt .hiding .importDecl markerResult
  have valuesGrammar := delimited_nonempty_trailing_success_sound
    .leftBrace .rightBrace (selectorName .importDecl)
    DeclarativeGrammar.SelectorNameParses .importDecl .topLevel
    (selectorName_success_sound .importDecl)
    (selectorName_preservesTokenWindow .importDecl) valuesResult
  have shape := requireSelectorNames_success_shape namesResult
  unfold DeclarativeGrammar.HidingClauseParses
    DeclarativeGrammar.NonemptySelectorListParses
  refine ⟨marker.span, values.span, markerSound.1, ?_, rfl⟩
  rw [shape.1]
  simpa only [markerSound.2, State.declarativeRemainder, State.tokens,
    State.window, State.cursor, shape.2] using valuesGrammar

/-- Hiding-clause grammar soundness composes with source validity. -/
theorem hidingClause_success_sound_and_validFor {input next : State}
    {clause : HidingClause} (inputValid : input.ValidFor)
    (result : ImportInternals.hidingClause input = .ok clause next) :
    DeclarativeGrammar.HidingClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      clause.ValidFor input.file := by
  refine ⟨hidingClause_success_sound result, ?_⟩
  have valid := hidingClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Optional hiding parsing is maximal at its contextual keyword. -/
theorem optionalHiding_success_sound {input next : State}
    {hidden : Option HidingClause}
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    DeclarativeGrammar.OptionalHidingParses input.declarativeRemainder hidden
      next.declarativeRemainder := by
  unfold ImportInternals.optionalHiding at result
  simp only [getState, bind] at result
  split at result
  next present =>
    rcases importBind_success_components result with
      ⟨clause, afterClause, clauseResult, finished⟩
    cases finished
    exact .present (hidingClause_success_sound clauseResult)
  next absent =>
    simp only [pure] at result
    cases result
    have absentFalse : isContextual input .hiding = false := by
      cases found : isContextual input .hiding <;> simp_all
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .hiding absentFalse)

/-- Optional hiding soundness composes with source validity. -/
theorem optionalHiding_success_sound_and_validFor {input next : State}
    {hidden : Option HidingClause} (inputValid : input.ValidFor)
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    DeclarativeGrammar.OptionalHidingParses input.declarativeRemainder hidden
        next.declarativeRemainder ∧
      Option.ValidFor HidingClause.ValidFor input.file hidden := by
  refine ⟨optionalHiding_success_sound result, ?_⟩
  have valid := optionalHiding_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
