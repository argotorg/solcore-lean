import Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

/-! Success soundness of canonical export-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful export name follows its prioritized independent grammar. -/
theorem exportName_success_sound {input next : State} {name : ExportName}
    (result : ExportInternals.exportName input = .ok name next) :
    DeclarativeGrammar.ExportNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold ExportInternals.exportName at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .star .exportDecl markerResult
        simp only [markerResult] at result
        cases result
        have grammar := DeclarativeGrammar.ExportNameParses.wildcard
          (input := input.declarativeRemainder) marker.span markerSound.1
        simpa only [markerSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using grammar
  · have starFalse : isSymbol input .star = false := by
      cases found : isSymbol input .star <;> simp_all
    have starAbsent := symbolAbsentAt_of_isSymbol_eq_false .star starFalse
    split at result
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at result
      | reject failure rejected => simp [selectedResult] at result
      | ok selected afterSelected =>
          have selectedGrammar := operatorSelector_success_sound .exportDecl
            selectedResult
          rcases selected with ⟨selectedSpan, selectedValue⟩
          cases selectedValue with
          | identifier identifier =>
              simp [selectedResult] at result
          | operator spelling =>
              simp only [selectedResult] at result
              cases result
              exact DeclarativeGrammar.ExportNameParses.operator starAbsent
                selectedGrammar
    · have leftParenFalse : isSymbol input .leftParen = false := by
        cases found : isSymbol input .leftParen <;> simp_all
      have leftParenAbsent := symbolAbsentAt_of_isSymbol_eq_false
        .leftParen leftParenFalse
      cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok parsedName afterName =>
          have nameGrammar := identifier_success_sound .exportDecl nameResult
          simp only [nameResult] at result
          split at result
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | reject failure rejected => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                have constructorsGrammar := constructorSelection_success_sound
                  constructorsResult
                simp only [constructorsResult] at result
                cases result
                exact DeclarativeGrammar.ExportNameParses.identifier
                  starAbsent leftParenAbsent nameGrammar
                  (.present constructorsGrammar)
          · have constructorsAbsentBool :
                isSymbol afterName .leftParen = false := by
              cases found : isSymbol afterName .leftParen <;> simp_all
            have constructorsAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen constructorsAbsentBool
            cases result
            exact DeclarativeGrammar.ExportNameParses.identifier
              starAbsent leftParenAbsent nameGrammar
              (.absent constructorsAbsent)

/-- Export-name grammar soundness composes with source validity. -/
theorem exportName_success_sound_and_validFor {input next : State}
    {name : ExportName} (inputValid : input.ValidFor)
    (result : ExportInternals.exportName input = .ok name next) :
    DeclarativeGrammar.ExportNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file := by
  refine ⟨exportName_success_sound result, ?_⟩
  have valid := exportName_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
