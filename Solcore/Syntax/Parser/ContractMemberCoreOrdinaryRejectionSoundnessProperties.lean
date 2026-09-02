import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractFieldOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreSoundnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.EnumDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryOutcomeSoundnessProperties

/-! Exact broad rejection reflection for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

private theorem mapMember_reject_result {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    {input rejected : State} {failure : Failure}
    (result : mapMember parser wrap input = .reject failure rejected) :
    parser input = .reject failure rejected := by
  unfold mapMember at result
  cases parserResult : parser input with
  | ok value output => simp [bind, parserResult, pure] at result
  | reject innerFailure innerRejected =>
      simp only [bind, parserResult] at result
      cases result
      rfl
  | invariant error => simp [bind, parserResult] at result

private theorem keywordPresent_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .contractMember present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .contractMember parsed).1⟩

private theorem enumPresent_of_isContextual_eq_true {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem parsed).1⟩

/-- Every executable core-member rejection records the selected committed
branch and that branch's exact final rejection remainder. -/
theorem contractMemberCore_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractMemberCore input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    exact .fieldRejected
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_reject_ordinaryOutcome_sound expression
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        DeclarativeGrammar.CoreExpressionPublicRejects
        expression_success_ordinary_sound expression_reject_ordinary_sound
        (mapMember_reject_result (contractField expression) wrapField result))
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    have fieldAbsentGrammar :=
      not_contractFieldStartsAt_of_startsContractField_eq_false fieldAbsentEq
    split at result
    next startsFunction =>
      exact .functionRejected fieldAbsentGrammar
        (keywordPresent_of_isKeyword_eq_true .functionKw startsFunction)
        (functionDecl_reject_ordinaryOutcome_sound .contract
          (mapMember_reject_result (functionDecl .contract)
            wrapContractFunction result))
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      have functionAbsentGrammar :=
        keywordAbsentAt_of_isKeyword_eq_false .functionKw functionAbsentEq
      split at result
      next startsConstructor =>
        exact .constructorRejected fieldAbsentGrammar functionAbsentGrammar
          (keywordPresent_of_isKeyword_eq_true .constructorKw
            startsConstructor)
          (constructorDecl_reject_ordinaryOutcome_sound
            (mapMember_reject_result constructorDecl wrapConstructor result))
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        have constructorAbsentGrammar :=
          keywordAbsentAt_of_isKeyword_eq_false .constructorKw
            constructorAbsentEq
        split at result
        next startsFallback =>
          exact .fallbackRejected fieldAbsentGrammar functionAbsentGrammar
            constructorAbsentGrammar
            (keywordPresent_of_isKeyword_eq_true .fallbackKw startsFallback)
            (fallbackDecl_reject_ordinaryOutcome_sound
              (mapMember_reject_result fallbackDecl wrapFallback result))
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          have fallbackAbsentGrammar :=
            keywordAbsentAt_of_isKeyword_eq_false .fallbackKw fallbackAbsentEq
          split at result
          next startsType =>
            exact .typeAliasRejected fieldAbsentGrammar functionAbsentGrammar
              constructorAbsentGrammar fallbackAbsentGrammar
              (keywordPresent_of_isKeyword_eq_true .typeKw startsType)
              (typeAlias_reject_ordinaryOutcome_sound
                (mapMember_reject_result typeAlias wrapContractTypeAlias
                  result))
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            have typeAbsentGrammar :=
              keywordAbsentAt_of_isKeyword_eq_false .typeKw typeAbsentEq
            split at result
            next startsEnum =>
              exact .enumRejected fieldAbsentGrammar functionAbsentGrammar
                constructorAbsentGrammar fallbackAbsentGrammar
                typeAbsentGrammar
                (enumPresent_of_isContextual_eq_true startsEnum)
                (enumDecl_reject_ordinaryOutcome_sound none
                  (mapMember_reject_result (enumDecl none) wrapContractEnum
                    result))
            next enumAbsent =>
              have enumAbsentEq : isContextual input .enum = false :=
                Bool.eq_false_iff.mpr enumAbsent
              have enumAbsentGrammar :=
                contextualAbsentAt_of_isContextual_eq_false .enum enumAbsentEq
              unfold rejectedContractMember rejectAt at result
              cases result
              exact .unrecognized fieldAbsentGrammar functionAbsentGrammar
                constructorAbsentGrammar fallbackAbsentGrammar
                typeAbsentGrammar enumAbsentGrammar

end ContractInternals
end Solcore.Syntax.Parser
