import Solcore.Syntax.DeclarativeImplBodyOutcomeProperties
import Solcore.Syntax.DeclarativeImplMethodExactnessProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exactness transport through prioritized implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implBody_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem implBody_absent_conflicts_present {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent present

/-- Exact method outcomes make a method tail fix its methods, closing span,
and final remainder. -/
theorem ImplMethodTailOrdinaryParses.result_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ∀ {input : Remainder} {leftMethods rightMethods : List Syntax.ImplMethod}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ImplMethodTailOrdinaryParses input leftMethods leftClosing afterLeft →
      ImplMethodTailOrdinaryParses input rightMethods rightClosing afterRight →
      leftMethods = rightMethods ∧ leftClosing = rightClosing ∧
        afterLeft = afterRight := by
  intro input leftMethods rightMethods leftClosing rightClosing afterLeft
    afterRight leftParsed
  induction leftParsed generalizing rightMethods rightClosing afterRight with
  | close leftClosing leftToken =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨closingEq, outputEq⟩
          exact ⟨rfl, closingEq, outputEq⟩
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (implBody_absent_conflicts_exact rightClosingAbsent leftToken)
  | next leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim
            (implBody_absent_conflicts_exact leftClosingAbsent rightToken)
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          rcases methodOutcomes.successResultUnique leftMethod rightMethod with
            ⟨methodEq, afterMethodEq⟩
          subst methodEq
          subst afterMethodEq
          rcases inductionHypothesis rightTail with
            ⟨methodsEq, closingEq, outputEq⟩
          subst methodsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- Exact method outcomes fix the paired method-tail value. -/
theorem ImplMethodTailOrdinaryOutcomeParses.value_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodTailOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ImplMethodTailOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases left with ⟨leftClosing, leftMethods⟩
  rcases right with ⟨rightClosing, rightMethods⟩
  rcases leftParsed.result_unique methodOutcomes rightParsed with
    ⟨methodsEq, closingEq, outputEq⟩
  subst methodsEq
  subst closingEq
  rfl

/-- Exact method outcomes fix every rejecting method-tail endpoint. -/
theorem ImplMethodTailRejects.output_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input left right : Remainder}
    (leftRejected : ImplMethodTailRejects input left)
    (rightRejected : ImplMethodTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | unexpected leftClosingAbsent leftFunctionAbsent =>
      cases rightRejected with
      | unexpected => rfl
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (implBody_absent_conflicts_present leftFunctionAbsent
              rightFunctionPresent)
  | methodRejected leftClosingAbsent leftFunctionPresent leftMethod =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (implBody_absent_conflicts_present rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact methodOutcomes.rejectOutputUnique leftMethod rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (methodOutcomes.successRejectDisjoint leftMethod
              ⟨_, _, rightMethod⟩)
  | laterRejected leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (implBody_absent_conflicts_present rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (methodOutcomes.successRejectDisjoint rightMethod
              ⟨_, _, leftMethod⟩)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          have afterMethodEq :=
            methodOutcomes.successOutputUnique leftMethod rightMethod
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- Exact method outcomes lift through the prioritized method-tail loop. -/
theorem implMethodTailExactOutcomeSpecOfMethod
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ExactDeterministicOutcomeSpec ImplMethodTailOrdinaryOutcomeParses
      ImplMethodTailRejects where
  toDeterministicOutcomeSpec := implMethodTailDeterministicOutcomeSpec
  successValueUnique :=
    ImplMethodTailOrdinaryOutcomeParses.value_unique methodOutcomes
  rejectOutputUnique := ImplMethodTailRejects.output_unique methodOutcomes

/-- Exact method outcomes make a complete implementation body fix its span,
methods, and final remainder. -/
theorem ImplBodyOrdinaryParses.result_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : ImplBodyOrdinaryParses input rightSpan rightMethods
      afterRight) :
    leftSpan = rightSpan ∧ leftMethods = rightMethods ∧
      afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftOpeningToken leftTail =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightOpeningToken rightTail =>
          rcases leftOpeningToken.result_unique rightOpeningToken with
            ⟨openingEq, afterOpeningEq⟩
          subst openingEq
          subst afterOpeningEq
          rcases leftTail.result_unique methodOutcomes rightTail with
            ⟨methodsEq, closingEq, outputEq⟩
          subst methodsEq
          subst closingEq
          exact ⟨rfl, rfl, outputEq⟩

/-- Exact method outcomes fix the paired complete-body value. -/
theorem ImplBodyOrdinaryOutcomeParses.value_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ImplBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases left with ⟨leftSpan, leftMethods⟩
  rcases right with ⟨rightSpan, rightMethods⟩
  rcases leftParsed.result_unique methodOutcomes rightParsed with
    ⟨spanEq, methodsEq, outputEq⟩
  subst spanEq
  subst methodsEq
  rfl

/-- Exact method outcomes fix complete implementation-body rejection. -/
theorem ImplBodyRejects.output_unique
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects)
    {input left right : Remainder}
    (leftRejected : ImplBodyRejects input left)
    (rightRejected : ImplBodyRejects input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | tailRejected rightSpan rightOpening rightTail =>
          exact False.elim
            (implBody_absent_conflicts_exact leftOpeningAbsent rightOpening)
  | tailRejected leftSpan leftOpening leftTail =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (implBody_absent_conflicts_exact rightOpeningAbsent leftOpening)
      | tailRejected rightSpan rightOpening rightTail =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftTail.output_unique methodOutcomes rightTail

/-- Exact method outcomes lift through a complete implementation body. -/
theorem implBodyExactOutcomeSpecOfMethod
    (methodOutcomes : ExactDeterministicOutcomeSpec
      ImplMethodOrdinaryParses ImplMethodRejects) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects where
  toDeterministicOutcomeSpec := implBodyDeterministicOutcomeSpec
  successValueUnique :=
    ImplBodyOrdinaryOutcomeParses.value_unique methodOutcomes
  rejectOutputUnique := ImplBodyRejects.output_unique methodOutcomes

/-- An exact isolated `.allow` Core body lifts through every implementation
method and therefore through the complete implementation body. -/
theorem implBodyExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects :=
  implBodyExactOutcomeSpecOfMethod
    (implMethodExactOutcomeSpecOfBody bodyOutcomes)

/-- Fixed-fuel Core-statement exactness supplies exact implementation-body
outcomes. -/
theorem implBodyExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects :=
  implBodyExactOutcomeSpecOfMethod
    (implMethodExactOutcomeSpecOfStatementFuel statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
