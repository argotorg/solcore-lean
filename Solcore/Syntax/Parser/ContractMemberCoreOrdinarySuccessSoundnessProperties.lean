import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ContractFieldOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreSoundnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.FallbackDeclarationOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.TypeAlias

/-! Broad ordinary-success reflection for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

private theorem keywordPresentAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .contractMember present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .contractMember result).1⟩

private theorem enumPresentAt_of_isContextual_eq_true {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem result).1⟩

/-- Every successful executable core member follows its exact broad ordinary
branch, including all positive and earlier-negative dispatch guards. -/
theorem contractMemberCore_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : contractMemberCore input = .ok member output) :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    unfold mapMember at result
    rcases bind_ok_components result with
      ⟨declaration, afterDeclaration, declarationResult, finished⟩
    cases finished
    exact .field
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_success_ordinaryOutcome_sound expression
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        expression_success_ordinary_sound declarationResult)
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    have noField :=
      not_contractFieldStartsAt_of_startsContractField_eq_false fieldAbsentEq
    split at result
    next startsFunction =>
      unfold mapMember at result
      rcases bind_ok_components result with
        ⟨declaration, afterDeclaration, declarationResult, finished⟩
      cases finished
      exact .function noField
        (keywordPresentAt_of_isKeyword_eq_true .functionKw startsFunction)
        (functionDecl_success_ordinaryOutcome_sound .contract
          declarationResult)
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      have noFunction := keywordAbsentAt_of_isKeyword_eq_false .functionKw
        functionAbsentEq
      split at result
      next startsConstructor =>
        unfold mapMember at result
        rcases bind_ok_components result with
          ⟨declaration, afterDeclaration, declarationResult, finished⟩
        cases finished
        exact .constructor noField noFunction
          (keywordPresentAt_of_isKeyword_eq_true .constructorKw
            startsConstructor)
          (constructorDecl_success_ordinaryOutcome_sound declarationResult)
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        have noConstructor := keywordAbsentAt_of_isKeyword_eq_false
          .constructorKw constructorAbsentEq
        split at result
        next startsFallback =>
          unfold mapMember at result
          rcases bind_ok_components result with
            ⟨declaration, afterDeclaration, declarationResult, finished⟩
          cases finished
          exact .fallback noField noFunction noConstructor
            (keywordPresentAt_of_isKeyword_eq_true .fallbackKw startsFallback)
            (fallbackDecl_success_ordinaryOutcome_sound declarationResult)
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          have noFallback := keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
            fallbackAbsentEq
          split at result
          next startsType =>
            unfold mapMember at result
            rcases bind_ok_components result with
              ⟨declaration, afterDeclaration, declarationResult, finished⟩
            cases finished
            exact .typeAlias noField noFunction noConstructor noFallback
              (keywordPresentAt_of_isKeyword_eq_true .typeKw startsType)
              (typeAlias_success_ordinaryOutcome_sound declarationResult)
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            have noType := keywordAbsentAt_of_isKeyword_eq_false .typeKw
              typeAbsentEq
            split at result
            next startsEnum =>
              unfold mapMember at result
              rcases bind_ok_components result with
                ⟨declaration, afterDeclaration, declarationResult, finished⟩
              cases finished
              exact .enum noField noFunction noConstructor noFallback noType
                (enumPresentAt_of_isContextual_eq_true startsEnum)
                (enumDecl_success_ordinaryOutcome_sound none declarationResult)
            next enumAbsent =>
              simp [rejectedContractMember, rejectAt] at result

end ContractInternals
end Solcore.Syntax.Parser
