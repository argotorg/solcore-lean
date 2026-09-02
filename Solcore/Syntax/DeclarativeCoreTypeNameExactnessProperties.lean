import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact qualified-name outcomes used by recursive Core named types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One maximal dotted identifier tail has one exact component list. -/
theorem DottedIdentifierTailParses.value_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {left right : List Syntax.Identifier} {leftFinish rightFinish : Nat},
      DottedIdentifierTailParses tokens endIndex cursor left leftFinish →
      DottedIdentifierTailParses tokens endIndex cursor right rightFinish →
      left = right := by
  intro tokens endIndex cursor left right leftFinish rightFinish leftParsed
  induction leftParsed generalizing right rightFinish with
  | done cursor leftDotAbsent =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot rightComponent rightTail =>
          exact False.elim (leftDotAbsent ⟨rightDotSpan, rightDot⟩)
  | @next cursor leftFinish leftComponent leftComponents leftDotSpan leftDot
      leftComponentToken leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | done cursor rightDotAbsent =>
          exact False.elim (rightDotAbsent ⟨leftDotSpan, leftDot⟩)
      | @next _ rightFinish rightComponent rightComponents rightDotSpan
          rightDot rightComponentToken rightTail =>
          have componentTokenEq :=
            leftComponentToken.token_unique rightComponentToken
          have componentEq : leftComponent = rightComponent := by
            cases leftComponent
            cases rightComponent
            simp_all
          have tailEq := inductionHypothesis rightTail
          subst componentEq
          subst tailEq
          rfl

/-- One qualified-name success has one exact located component sequence. -/
theorem QualifiedNameParses.value_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftTokensEq, leftEndIndexEq, leftFirst, leftTail, leftSpanEq⟩
  rcases rightParsed with
    ⟨rightTokensEq, rightEndIndexEq, rightFirst, rightTail, rightSpanEq⟩
  have firstTokenEq := leftFirst.token_unique rightFirst
  have tailEq := leftTail.value_unique rightTail
  cases left with
  | mk leftSpan leftValue =>
      cases leftValue with
      | mk leftComponents =>
          cases leftComponents with
          | mk leftHead leftRest =>
              cases right with
              | mk rightSpan rightValue =>
                  cases rightValue with
                  | mk rightComponents =>
                      cases rightComponents with
                      | mk rightHead rightRest =>
                          cases leftHead
                          cases rightHead
                          simp_all

/-- One qualified-name success fixes its value and final remainder. -/
theorem QualifiedNameParses.result_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A dotted qualified-name tail rejection has one failing endpoint. -/
theorem TypeQualifiedNameTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeQualifiedNameTailRejects input left)
    (rightRejected : TypeQualifiedNameTailRejects input right) :
    left = right := by
  induction leftRejected generalizing right with
  | componentRejected leftDotSpan leftDot leftComponent =>
      cases rightRejected with
      | componentRejected rightDotSpan rightDot rightComponent =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact leftComponent.output_unique rightComponent
      | laterRejected rightDotSpan rightDot rightComponent rightTail =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint leftComponent
              ⟨_, _, rightComponent⟩)
  | laterRejected leftDotSpan leftDot leftComponent leftTail
        inductionHypothesis =>
      cases rightRejected with
      | componentRejected rightDotSpan rightDot rightComponent =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint rightComponent
              ⟨_, _, leftComponent⟩)
      | laterRejected rightDotSpan rightDot rightComponent rightTail =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          rcases leftComponent.result_unique rightComponent with
            ⟨componentEq, afterComponentEq⟩
          subst componentEq
          subst afterComponentEq
          exact inductionHypothesis rightTail

/-- A complete qualified-name rejection has one failing endpoint. -/
theorem TypeQualifiedNameRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeQualifiedNameRejects input left)
    (rightRejected : TypeQualifiedNameRejects input right) :
    left = right := by
  cases leftRejected with
  | firstRejected leftFirst =>
      cases rightRejected with
      | firstRejected rightFirst => exact leftFirst.output_unique rightFirst
      | tailRejected rightFirst rightTail =>
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint leftFirst
              ⟨_, _, rightFirst⟩)
  | tailRejected leftFirst leftTail =>
      cases rightRejected with
      | firstRejected rightFirst =>
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint rightFirst
              ⟨_, _, leftFirst⟩)
      | tailRejected rightFirst rightTail =>
          rcases leftFirst.result_unique rightFirst with
            ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Qualified names have fully functional success and rejection outcomes. -/
theorem typeQualifiedNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec QualifiedNameParses
      TypeQualifiedNameRejects where
  toDeterministicOutcomeSpec := {
    successOutputUnique := QualifiedNameParses.output_unique
    successRejectDisjoint := TypeQualifiedNameRejects.disjointQualified
  }
  successValueUnique := QualifiedNameParses.value_unique
  rejectOutputUnique := TypeQualifiedNameRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
