import Solcore.Syntax.DeclarativeContractBodyExactnessProperties
import Solcore.Syntax.DeclarativeContractDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeGenericParametersExactnessProperties

/-! Exactness transport through complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem contractDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact contract-body outcome makes a declaration fix its complete AST. -/
theorem ContractDeclOrdinaryParses.value_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          have bodyEq := bodyOutcomes.successValueUnique
            (show ContractBodyOrdinaryOutcomeParses _ (_, _) _ from leftBody)
            (show ContractBodyOrdinaryOutcomeParses _ (_, _) _ from rightBody)
          cases bodyEq
          rfl

/-- Under an exact body contract, declaration success fixes its AST and final
remainder. -/
theorem ContractDeclOrdinaryParses.result_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Under an exact body contract, declaration rejection has one endpoint. -/
theorem ContractDeclRejects.output_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input left right : Remainder}
    (leftRejected : ContractDeclRejects input left)
    (rightRejected : ContractDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [contractDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      bodyOutcomes.rejectOutputUnique]

/-- An exact complete contract body lifts to exact declaration outcomes. -/
theorem contractDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects where
  toDeterministicOutcomeSpec := contractDeclDeterministicOutcomeSpec
  successValueUnique :=
    ContractDeclOrdinaryParses.value_unique_of_body bodyOutcomes
  rejectOutputUnique := ContractDeclRejects.output_unique_of_body bodyOutcomes

/-- Exact attribute-free member outcomes lift through derive attachment,
recovery, the body loop, and the complete contract declaration. -/
theorem contractDeclExactOutcomeSpecOfCore
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfBody
    (contractBodyExactOutcomeSpecOfCore coreOutcomes)

end Solcore.Syntax.DeclarativeGrammar
