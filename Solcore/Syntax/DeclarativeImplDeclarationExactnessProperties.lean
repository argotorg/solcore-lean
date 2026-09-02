import Solcore.Syntax.DeclarativeGenericParametersExactnessProperties
import Solcore.Syntax.DeclarativeImplBodyExactnessProperties
import Solcore.Syntax.DeclarativeImplDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeImplDefaultMarkerExactnessProperties
import Solcore.Syntax.DeclarativeImplHeadArgumentsExactnessProperties
import Solcore.Syntax.DeclarativeWhereClauseExactnessProperties

/-! Exactness transport through complete implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact implementation-body contract makes a declaration fix its AST. -/
theorem ImplDeclOrdinaryParses.value_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftDefault leftMarkerSpan leftMarker leftGenerics leftName
      leftArguments leftWhere leftBody =>
      cases rightParsed with
      | parsed rightDefault rightMarkerSpan rightMarker rightGenerics
          rightName rightArguments rightWhere rightBody =>
          rcases leftDefault.result_unique rightDefault with
            ⟨defaultEq, afterDefaultEq⟩
          subst defaultEq
          subst afterDefaultEq
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases implHeadArgumentsExactOutcomeSpec.successResultUnique
              leftArguments rightArguments with
            ⟨argumentsEq, afterArgumentsEq⟩
          subst argumentsEq
          subst afterArgumentsEq
          rcases optionalWhereClauseExactOutcomeSpec.successResultUnique
              leftWhere rightWhere with ⟨whereEq, afterWhereEq⟩
          subst whereEq
          subst afterWhereEq
          have bodyEq := bodyOutcomes.successValueUnique
            (show ImplBodyOrdinaryOutcomeParses _ (_, _) _ from leftBody)
            (show ImplBodyOrdinaryOutcomeParses _ (_, _) _ from rightBody)
          cases bodyEq
          rfl

/-- Under an exact implementation-body contract, declaration success fixes
its AST and final remainder. -/
theorem ImplDeclOrdinaryParses.result_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_impl_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- An exact implementation body makes declaration rejection fix its first
failing endpoint. -/
theorem ImplDeclRejects.output_unique_of_impl_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects)
    {input left right : Remainder}
    (leftRejected : ImplDeclRejects input left)
    (rightRejected : ImplDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [
      OptionalImplDefaultMarkerOrdinaryParses.output_unique,
      implDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      implHeadArgumentsExactOutcomeSpec.successOutputUnique,
      implHeadArgumentsExactOutcomeSpec.successRejectDisjoint,
      implHeadArgumentsExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successRejectDisjoint,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique,
      bodyOutcomes.rejectOutputUnique]

/-- An exact complete implementation body lifts to exact declaration
outcomes. -/
theorem implDeclExactOutcomeSpecOfImplBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ImplBodyOrdinaryOutcomeParses ImplBodyRejects) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses
      ImplDeclRejects where
  toDeterministicOutcomeSpec := implDeclDeterministicOutcomeSpec
  successValueUnique :=
    ImplDeclOrdinaryParses.value_unique_of_impl_body bodyOutcomes
  rejectOutputUnique :=
    ImplDeclRejects.output_unique_of_impl_body bodyOutcomes

/-- An exact isolated `.allow` Core body lifts through methods, the complete
implementation body, and the implementation declaration. -/
theorem implDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfImplBody
    (implBodyExactOutcomeSpecOfBody bodyOutcomes)

/-- With an exact isolated method body, implementation declaration success
fixes its AST and final remainder. -/
theorem ImplDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (implDeclExactOutcomeSpecOfBody bodyOutcomes).successResultUnique leftParsed
    rightParsed

/-- With an exact isolated method body, implementation declaration rejection
fixes its endpoint. -/
theorem ImplDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : ImplDeclRejects input left)
    (rightRejected : ImplDeclRejects input right) : left = right :=
  (implDeclExactOutcomeSpecOfBody bodyOutcomes).rejectOutputUnique leftRejected
    rightRejected

/-- Fixed-fuel Core-statement exactness supplies exact implementation
declaration outcomes. -/
theorem implDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfImplBody
    (implBodyExactOutcomeSpecOfStatementFuel statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
