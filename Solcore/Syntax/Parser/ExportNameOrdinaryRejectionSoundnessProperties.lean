import Solcore.Syntax.DeclarativeExportNameOutcomeGrammar
import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties

/-! Exact executable rejection reflection for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportNameTokenPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.ExportNameTokenPresentAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .exportDecl present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .exportDecl result).1⟩

/-- Every executable export-name rejection records the exact first failing
operator, identifier, or constructor-selection stage under parser priority. -/
theorem exportName_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportName input = .reject failure rejected) :
    DeclarativeGrammar.ExportNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportName at result
  by_cases starPresent : isSymbol input .star = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl starPresent with
      ⟨marker, markerResult⟩
    simp [starPresent, markerResult] at result
  · have starAbsent : isSymbol input .star = false :=
      Bool.eq_false_iff.mpr starPresent
    simp only [starAbsent, Bool.false_eq_true, if_false] at result
    have starMissing := symbolAbsentAt_of_isSymbol_eq_false .star starAbsent
    by_cases openingPresent : isSymbol input .leftParen = true
    · simp only [openingPresent, if_true] at result
      have openingToken := exportNameTokenPresentAt_of_isSymbol_eq_true
        .leftParen openingPresent
      cases selectorResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectorResult] at result
      | reject selectorFailure selectorRejected =>
          have selectorReply : selectorName .exportDecl input =
              .reject selectorFailure selectorRejected := by
            unfold selectorName
            simp only [openingPresent, if_true]
            exact selectorResult
          have selectorGrammar :=
            selectorName_reject_ordinaryOutcome_sound .exportDecl
              selectorReply
          simp only [selectorResult] at result
          cases result
          exact .operatorRejected starMissing openingToken selectorGrammar
      | ok selector afterSelector =>
          rcases selector with ⟨selectorSpan, selectorValue⟩
          cases selectorValue <;> simp [selectorResult] at result
    · have openingAbsent : isSymbol input .leftParen = false :=
        Bool.eq_false_iff.mpr openingPresent
      simp only [openingAbsent, Bool.false_eq_true, if_false] at result
      have openingMissing := symbolAbsentAt_of_isSymbol_eq_false
        .leftParen openingAbsent
      cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .identifierRejected starMissing openingMissing
            (identifier_reject_sound .exportDecl nameResult)
      | ok name afterName =>
          have nameParsed := identifier_success_sound .exportDecl nameResult
          simp only [nameResult] at result
          by_cases constructorsPresent :
              isSymbol afterName .leftParen = true
          · simp only [constructorsPresent, if_true] at result
            have constructorsToken :=
              exportNameTokenPresentAt_of_isSymbol_eq_true .leftParen
                constructorsPresent
            cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                simp [constructorsResult] at result
            | reject constructorsFailure constructorsRejected =>
                have constructorsGrammar :=
                  constructorSelection_reject_ordinaryOutcome_sound
                    constructorsResult
                simp only [constructorsResult] at result
                cases result
                exact .constructorsRejected starMissing openingMissing
                  nameParsed constructorsToken constructorsGrammar
          · have constructorsAbsent :
                isSymbol afterName .leftParen = false :=
              Bool.eq_false_iff.mpr constructorsPresent
            simp [constructorsAbsent] at result

end Solcore.Syntax.Parser
