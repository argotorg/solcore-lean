import Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties
import Solcore.Syntax.Parser.ExportProperties

/-! Success soundness of canonical constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Requiring constructor names preserves state and forward element order. -/
theorem requireConstructorNames_success_shape
    {values : DelimitedList Identifier}
    {input next : State} {constructors : NonemptyList Identifier}
    (result : ExportInternals.requireConstructorNames values input =
      .ok constructors next) :
    next = input ∧ constructors.toList = values.elements := by
  unfold ExportInternals.requireConstructorNames at result
  cases elements : values.elements with
  | nil => simp [elements] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact ⟨rfl, by simp [NonemptyList.toList]⟩

/-- Every successful constructor selection follows the independent grammar. -/
theorem constructorSelection_success_sound {input next : State}
    {selection : ConstructorSelection}
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    DeclarativeGrammar.ConstructorSelectionParses
      input.declarativeRemainder selection next.declarativeRemainder := by
  by_cases all :
      input.peekOffsetKind? 1 == some (.symbol .star)
  · cases openingResult : symbol .leftParen .exportDecl input with
    | invariant error =>
        simp [ExportInternals.constructorSelection, getState, bind, all,
          openingResult] at result
    | reject failure rejected =>
        simp [ExportInternals.constructorSelection, getState, bind, all,
          openingResult] at result
    | ok opening afterOpening =>
        have openingSound := symbol_ok_tokenAt .leftParen .exportDecl
          openingResult
        cases markerResult : symbol .star .exportDecl afterOpening with
        | invariant error =>
            simp [ExportInternals.constructorSelection, getState, bind, all,
              openingResult, markerResult] at result
        | reject failure rejected =>
            simp [ExportInternals.constructorSelection, getState, bind, all,
              openingResult, markerResult] at result
        | ok marker afterMarker =>
            have markerSound := symbol_ok_tokenAt .star .exportDecl
              markerResult
            cases closingResult : symbol .rightParen .exportDecl afterMarker with
            | invariant error =>
                simp [ExportInternals.constructorSelection, getState, bind,
                  all, openingResult, markerResult, closingResult] at result
            | reject failure rejected =>
                simp [ExportInternals.constructorSelection, getState, bind,
                  all, openingResult, markerResult, closingResult] at result
            | ok closing final =>
                have closingSound := symbol_ok_tokenAt .rightParen .exportDecl
                  closingResult
                simp only [ExportInternals.constructorSelection, getState,
                  bind, all, ↓reduceIte, openingResult, markerResult,
                  closingResult, pure] at result
                cases result
                have markerToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 1) {
                        span := marker.span
                        value := .symbol .star
                      } := by
                  simpa only [openingSound.2, State.tokens, State.window,
                    State.cursor] using markerSound.1
                have closingToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 2) {
                        span := closing.span
                        value := .symbol .rightParen
                      } := by
                  simpa only [markerSound.2, openingSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using
                    closingSound.1
                have grammar :=
                  DeclarativeGrammar.ConstructorSelectionParses.all
                    (input := input.declarativeRemainder)
                    opening.span marker.span closing.span openingSound.1
                    markerToken closingToken
                simpa only [closingSound.2, markerSound.2, openingSound.2,
                  State.declarativeRemainder, State.tokens, State.window,
                  State.cursor, Nat.add_assoc] using grammar
  · have named :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false := by
      cases found : input.peekOffsetKind? 1 == some (.symbol .star) with
      | false => rfl
      | true => exact False.elim (all found)
    cases valuesResult : delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel input with
    | invariant error =>
        simp [ExportInternals.constructorSelection, getState, bind, named,
          valuesResult] at result
    | reject failure rejected =>
        simp [ExportInternals.constructorSelection, getState, bind, named,
          valuesResult] at result
    | ok values afterValues =>
        have valuesGrammar := delimitedNoTrailing_nonempty_success_sound
          .leftParen .rightParen (identifier .exportDecl)
          DeclarativeGrammar.IdentifierParses .exportDecl .topLevel
          (identifier_success_sound .exportDecl)
          (identifier_preservesTokenWindow .exportDecl) valuesResult
        cases constructorsResult :
            ExportInternals.requireConstructorNames values afterValues with
        | invariant error =>
            simp [ExportInternals.constructorSelection, getState, bind, named,
              valuesResult, constructorsResult] at result
        | reject failure rejected =>
            simp [ExportInternals.constructorSelection, getState, bind, named,
              valuesResult, constructorsResult] at result
        | ok constructors afterConstructors =>
            have shape := requireConstructorNames_success_shape
              constructorsResult
            simp only [ExportInternals.constructorSelection, getState, bind,
              named, Bool.false_eq_true, ↓reduceIte, valuesResult,
              constructorsResult, pure] at result
            cases result
            apply DeclarativeGrammar.ConstructorSelectionParses.named
            unfold DeclarativeGrammar.ConstructorNamesParses
            rw [shape.1]
            simpa only [shape.2] using valuesGrammar

/-- Constructor-selection grammar soundness composes with source validity. -/
theorem constructorSelection_success_sound_and_validFor
    {input next : State} {selection : ConstructorSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    DeclarativeGrammar.ConstructorSelectionParses
        input.declarativeRemainder selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨constructorSelection_success_sound result, ?_⟩
  have valid := constructorSelection_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
