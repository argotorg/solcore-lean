import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeContractFieldOutcomeProperties
import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties

/-! Output functionality for broad attribute-free contract-member success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent
    {input : Remainder} {kind : TokenKind}
    (present : ContractMemberCoreTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- Broad attribute-free contract-member success has one final remainder. -/
theorem ContractMemberCoreOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | field leftFieldPresent leftFieldParsed =>
      cases rightParsed with
      | field rightFieldPresent rightFieldParsed =>
          exact (contractFieldDeterministicOutcomeSpec
            coreExpressionPublicOutcomeSpec).successOutputUnique
              leftFieldParsed rightFieldParsed
      | function rightFieldAbsent _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | constructor rightFieldAbsent _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | fallback rightFieldAbsent _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | typeAlias rightFieldAbsent _ _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
      | enum rightFieldAbsent _ _ _ _ _ _ =>
          exact False.elim (rightFieldAbsent leftFieldPresent)
  | function leftFieldAbsent leftFunctionPresent leftFunctionParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ _ rightFunctionParsed =>
          exact functionDeclDeterministicOutcomeSpec.successOutputUnique
            leftFunctionParsed rightFunctionParsed
      | constructor _ rightFunctionAbsent _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | fallback _ rightFunctionAbsent _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | typeAlias _ rightFunctionAbsent _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
      | enum _ rightFunctionAbsent _ _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent leftFunctionPresent rightFunctionAbsent)
  | constructor leftFieldAbsent leftFunctionAbsent leftConstructorPresent
        leftConstructorParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ _ rightConstructorParsed =>
          exact constructorDeclDeterministicOutcomeSpec.successOutputUnique
            leftConstructorParsed rightConstructorParsed
      | fallback _ _ rightConstructorAbsent _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
      | typeAlias _ _ rightConstructorAbsent _ _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
      | enum _ _ rightConstructorAbsent _ _ _ _ =>
          exact False.elim (present_conflicts_absent leftConstructorPresent
            rightConstructorAbsent)
  | fallback leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackPresent leftFallbackParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ _ rightFallbackParsed =>
          exact fallbackDeclDeterministicOutcomeSpec.successOutputUnique
            leftFallbackParsed rightFallbackParsed
      | typeAlias _ _ _ rightFallbackAbsent _ _ =>
          exact False.elim (present_conflicts_absent leftFallbackPresent
            rightFallbackAbsent)
      | enum _ _ _ rightFallbackAbsent _ _ _ =>
          exact False.elim (present_conflicts_absent leftFallbackPresent
            rightFallbackAbsent)
  | typeAlias leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackAbsent leftTypePresent leftTypeParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ rightFallbackPresent _ =>
          exact False.elim (present_conflicts_absent rightFallbackPresent
            leftFallbackAbsent)
      | typeAlias _ _ _ _ _ rightTypeParsed =>
          exact typeAliasDeclDeterministicOutcomeSpec.successOutputUnique
            leftTypeParsed rightTypeParsed
      | enum _ _ _ _ rightTypeAbsent _ _ =>
          exact False.elim
            (present_conflicts_absent leftTypePresent rightTypeAbsent)
  | enum leftFieldAbsent leftFunctionAbsent leftConstructorAbsent
        leftFallbackAbsent leftTypeAbsent leftEnumPresent leftEnumParsed =>
      cases rightParsed with
      | field rightFieldPresent _ =>
          exact False.elim (leftFieldAbsent rightFieldPresent)
      | function _ rightFunctionPresent _ =>
          exact False.elim
            (present_conflicts_absent rightFunctionPresent leftFunctionAbsent)
      | constructor _ _ rightConstructorPresent _ =>
          exact False.elim (present_conflicts_absent rightConstructorPresent
            leftConstructorAbsent)
      | fallback _ _ _ rightFallbackPresent _ =>
          exact False.elim (present_conflicts_absent rightFallbackPresent
            leftFallbackAbsent)
      | typeAlias _ _ _ _ rightTypePresent _ =>
          exact False.elim
            (present_conflicts_absent rightTypePresent leftTypeAbsent)
      | enum _ _ _ _ _ _ rightEnumParsed =>
          exact (enumDeclDeterministicOutcomeSpec none).successOutputUnique
            leftEnumParsed rightEnumParsed

end Solcore.Syntax.DeclarativeGrammar
