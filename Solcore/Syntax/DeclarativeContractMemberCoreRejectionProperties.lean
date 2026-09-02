import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeContractFieldOutcomeProperties
import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties

/-! Rejection exclusion for broad attribute-free contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_present {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False := by
  exact absent present

/-- Exact selected-branch rejection excludes every broad ordinary success. -/
theorem ContractMemberCoreRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ContractMemberCoreRejects input rejected) :
    ¬ ∃ member output,
      ContractMemberCoreOrdinaryParses input member output := by
  rintro ⟨member, output, successful⟩
  cases rejection with
  | fieldRejected rejectedFieldPresent rejectedField =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact (contractFieldDeterministicOutcomeSpec
            coreExpressionPublicOutcomeSpec).successRejectDisjoint
              rejectedField ⟨_, _, successfulField⟩
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact successfulFieldAbsent rejectedFieldPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact successfulFieldAbsent rejectedFieldPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact successfulFieldAbsent rejectedFieldPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact successfulFieldAbsent rejectedFieldPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact successfulFieldAbsent rejectedFieldPresent
  | functionRejected rejectedFieldAbsent rejectedFunctionPresent
        rejectedFunction =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact functionDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedFunction ⟨_, _, successfulFunction⟩
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present successfulFunctionAbsent
            rejectedFunctionPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present successfulFunctionAbsent
            rejectedFunctionPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present successfulFunctionAbsent
            rejectedFunctionPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present successfulFunctionAbsent
            rejectedFunctionPresent
  | constructorRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorPresent rejectedConstructor =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact constructorDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedConstructor ⟨_, _, successfulConstructor⟩
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present successfulConstructorAbsent
            rejectedConstructorPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present successfulConstructorAbsent
            rejectedConstructorPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present successfulConstructorAbsent
            rejectedConstructorPresent
  | fallbackRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackPresent rejectedFallback =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact fallbackDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedFallback ⟨_, _, successfulFallback⟩
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present successfulFallbackAbsent
            rejectedFallbackPresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present successfulFallbackAbsent
            rejectedFallbackPresent
  | typeAliasRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypePresent
        rejectedType =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact typeAliasDeclDeterministicOutcomeSpec.successRejectDisjoint
            rejectedType ⟨_, _, successfulType⟩
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present successfulTypeAbsent
            rejectedTypePresent
  | enumRejected rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypeAbsent
        rejectedEnumPresent rejectedEnum =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present rejectedTypeAbsent
            successfulTypePresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact (enumDeclDeterministicOutcomeSpec none).successRejectDisjoint
            rejectedEnum ⟨_, _, successfulEnum⟩
  | unrecognized rejectedFieldAbsent rejectedFunctionAbsent
        rejectedConstructorAbsent rejectedFallbackAbsent rejectedTypeAbsent
        rejectedEnumAbsent =>
      cases successful with
      | field successfulFieldPresent successfulField =>
          exact rejectedFieldAbsent successfulFieldPresent
      | function successfulFieldAbsent successfulFunctionPresent
            successfulFunction =>
          exact absent_conflicts_present rejectedFunctionAbsent
            successfulFunctionPresent
      | constructor successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorPresent successfulConstructor =>
          exact absent_conflicts_present rejectedConstructorAbsent
            successfulConstructorPresent
      | fallback successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackPresent
            successfulFallback =>
          exact absent_conflicts_present rejectedFallbackAbsent
            successfulFallbackPresent
      | typeAlias successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypePresent successfulType =>
          exact absent_conflicts_present rejectedTypeAbsent
            successfulTypePresent
      | enum successfulFieldAbsent successfulFunctionAbsent
            successfulConstructorAbsent successfulFallbackAbsent
            successfulTypeAbsent successfulEnumPresent successfulEnum =>
          exact absent_conflicts_present rejectedEnumAbsent
            successfulEnumPresent

end Solcore.Syntax.DeclarativeGrammar
