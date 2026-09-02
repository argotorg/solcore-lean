import Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.EnumConstructorOrdinarySuccessSoundnessProperties

/-! Exact ordinary-rejection bridges for enum constructors and tuple payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- A rejected optional enum-constructor payload has a positively guarded
opening parenthesis and the exact no-trailing nested type-list rejection. -/
theorem enumConstructorFields_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumConstructorFields input = .reject failure rejected) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold enumConstructorFields getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with
      ⟨opening, openingResult⟩
    simp only [present, if_true] at result
    cases fieldsResult : delimitedNoTrailing .leftParen .rightParen true
        typeExpr .typeExpr .topLevel input with
    | invariant error => simp [fieldsResult] at result
    | ok fields output => simp [fieldsResult, pure] at result
    | reject fieldsFailure fieldsRejected =>
        simp only [fieldsResult] at result
        cases result
        exact .present
          ⟨opening.span,
            (symbol_ok_tokenAt .leftParen .typeExpr openingResult).1⟩
          (delimitedNoTrailing_reject_sound .leftParen .rightParen true
            typeExpr DeclarativeGrammar.TypeExprOrdinaryParses
            DeclarativeGrammar.TypeExprRejects .typeExpr .topLevel
            typeExpr_success_sound typeExpr_reject_sound fieldsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Every rejected enum constructor records its first rejecting stage: the
name, or its positively selected optional tuple payload. -/
theorem enumConstructor_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumConstructor input = .reject failure rejected) :
    DeclarativeGrammar.EnumConstructorRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold enumConstructor at result
  cases nameResult : identifier .topItem input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (identifier_reject_sound .topItem nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      have nameParsed := identifier_success_sound .topItem nameResult
      cases fieldsResult : enumConstructorFields afterName with
      | invariant error => simp [fieldsResult] at result
      | reject fieldsFailure fieldsRejected =>
          simp only [fieldsResult] at result
          cases result
          exact .fieldsRejected nameParsed
            (enumConstructorFields_reject_ordinaryOutcome_sound fieldsResult)
      | ok fields output => simp [fieldsResult, pure] at result

end Solcore.Syntax.Parser.EnumInternals
