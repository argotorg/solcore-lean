import Solcore.Syntax.DeclarativeContractEntryModifierExactnessProperties
import Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties

/-!
Exactness transport through constructor declarations.

The remaining premises are exact recovery-aware parameters and exact isolated
`.require` Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem constructor_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Constructor success has one exact AST whenever its parameter and body
children have exact outcomes. -/
theorem ConstructorDeclOrdinaryParses.value_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightModifiers
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          cases markerSpanEq
          cases afterMarkerEq
          rcases parameterOutcomes.successResultUnique leftParameters
              rightParameters with ⟨parametersEq, afterParametersEq⟩
          cases parametersEq
          cases afterParametersEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨payableEq, afterModifiersEq⟩
          cases payableEq
          cases afterModifiersEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          cases bodyEq
          rfl

/-- Under exact child contracts, constructor success fixes its AST and final
remainder. -/
theorem ConstructorDeclOrdinaryParses.result_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_children parameterOutcomes
      bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Constructor rejection has one endpoint whenever its parameter and body
children have exact outcomes. -/
theorem ConstructorDeclRejects.output_unique_of_exact_children
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejects : ConstructorDeclRejects input left)
    (rightRejects : ConstructorDeclRejects input right) : left = right := by
  cases leftRejects with
  | markerMissing leftMarkerAbsent =>
      cases rightRejects with
      | markerMissing => rfl
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          exact False.elim
            (constructor_absent_conflicts_exact leftMarkerAbsent rightMarker)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          exact False.elim
            (constructor_absent_conflicts_exact leftMarkerAbsent rightMarker)
  | parametersRejected leftMarkerSpan leftMarker leftParameters =>
      cases rightRejects with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (constructor_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact parameterOutcomes.rejectOutputUnique leftParameters
            rightParameters
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (parameterOutcomes.successRejectDisjoint leftParameters
              ⟨_, _, rightParameters⟩)
  | bodyRejected leftMarkerSpan leftMarker leftParameters leftModifiers
      leftBody =>
      cases rightRejects with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (constructor_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (parameterOutcomes.successRejectDisjoint rightParameters
              ⟨_, _, leftParameters⟩)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          have afterParametersEq := parameterOutcomes.successOutputUnique
            leftParameters rightParameters
          cases afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          cases afterModifiersEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- Exact parameter and isolated-body contracts lift to the complete broad
constructor outcome. -/
theorem constructorDeclExactOutcomeSpecOfChildren
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      FunctionParametersOrdinaryParses FunctionParametersRejects)
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects where
  toDeterministicOutcomeSpec := constructorDeclDeterministicOutcomeSpec
  successValueUnique :=
    ConstructorDeclOrdinaryParses.value_unique_of_exact_children
      parameterOutcomes bodyOutcomes
  rejectOutputUnique :=
    ConstructorDeclRejects.output_unique_of_exact_children
      parameterOutcomes bodyOutcomes

/-- Once named-parameter exactness is instantiated, an exact isolated body is
the sole remaining premise for exact constructor outcomes. -/
theorem constructorDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfChildren
    functionParametersExactOutcomeSpec bodyOutcomes

/-- With an exact isolated body, constructor success fixes its AST and final
remainder. -/
theorem ConstructorDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (constructorDeclExactOutcomeSpecOfBody bodyOutcomes).successResultUnique
    leftParsed rightParsed

/-- With an exact isolated body, constructor rejection fixes its endpoint. -/
theorem ConstructorDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejects : ConstructorDeclRejects input left)
    (rightRejects : ConstructorDeclRejects input right) : left = right :=
  (constructorDeclExactOutcomeSpecOfBody bodyOutcomes).rejectOutputUnique
    leftRejects rightRejects

/-- Fixed-fuel Core statement exactness discharges the complete constructor
body and therefore the constructor itself. -/
theorem constructorDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)

end Solcore.Syntax.DeclarativeGrammar
