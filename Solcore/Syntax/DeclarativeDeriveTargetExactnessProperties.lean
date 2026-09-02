import Solcore.Syntax.DeclarativeDeriveTargetOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Full value and rejection-endpoint functionality for derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- One ordinary or diagnosed derive component has one exact value. -/
theorem DeriveComponentParses.value_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | identifier leftIdentifier =>
      cases rightParsed with
      | identifier rightIdentifier =>
          exact leftIdentifier.value_unique rightIdentifier
      | reserved keyword allowed span token =>
          have impossible := leftIdentifier.1.token_unique token
          cases impossible
  | reserved leftKeyword leftAllowed leftSpan leftToken =>
      cases rightParsed with
      | identifier rightIdentifier =>
          have impossible := leftToken.token_unique rightIdentifier.1
          cases impossible
      | reserved rightKeyword rightAllowed rightSpan rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          have spanEq : leftSpan = rightSpan :=
            congrArg (fun token : Token => token.span) tokenEq
          have kindEq : leftKeyword = rightKeyword :=
            TokenKind.keyword.inj
              (congrArg (fun token : Token => token.value) tokenEq)
          subst spanEq
          subst kindEq
          rfl

/-- One derive component fixes both its exact value and final remainder. -/
theorem DeriveComponentParses.result_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A rejected derive component has one exact nonconsuming endpoint. -/
theorem DeriveComponentRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveComponentRejects input left)
    (rightRejects : DeriveComponentRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Derive components have fully functional success and rejection outcomes. -/
theorem deriveComponentExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveComponentParses
      DeriveComponentRejects where
  toDeterministicOutcomeSpec := deriveComponentDeterministicOutcomeSpec
  successValueUnique := DeriveComponentParses.value_unique
  rejectOutputUnique := DeriveComponentRejects.output_unique

/-- A maximal dotted derive tail has one exact component list. -/
theorem DeriveTargetTailParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftDotAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot _ _ =>
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightDot)
  | next leftDotSpan leftDot leftComponent leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightDotAbsent =>
          exact False.elim
            (absent_conflicts_token rightDotAbsent leftDot)
      | next rightDotSpan rightDot rightComponent rightTail =>
          have componentEq :=
            leftComponent.value_unique rightComponent
          have afterComponentEq :=
            leftComponent.output_unique rightComponent
          subst componentEq
          subst afterComponentEq
          have tailEq := inductionHypothesis rightTail
          subst tailEq
          rfl

/-- A maximal dotted tail fixes its component list and final remainder. -/
theorem DeriveTargetTailParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A dotted-tail rejection has one exact first failing endpoint. -/
theorem DeriveTargetTailRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveTargetTailRejects input left)
    (rightRejects : DeriveTargetTailRejects input right) : left = right := by
  induction leftRejects generalizing right with
  | componentRejected leftDotSpan leftDot leftComponentRejects =>
      cases rightRejects with
      | componentRejected rightDotSpan rightDot rightComponentRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact leftComponentRejects.output_unique rightComponentRejects
      | laterRejected rightDotSpan rightDot rightComponent
            rightTailRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              leftComponentRejects ⟨_, _, rightComponent⟩)
  | laterRejected leftDotSpan leftDot leftComponent leftTailRejects
        inductionHypothesis =>
      cases rightRejects with
      | componentRejected rightDotSpan rightDot rightComponentRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              rightComponentRejects ⟨_, _, leftComponent⟩)
      | laterRejected rightDotSpan rightDot rightComponent
            rightTailRejects =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          rcases leftComponent.result_unique rightComponent with
            ⟨componentEq, afterComponentEq⟩
          subst componentEq
          subst afterComponentEq
          exact inductionHypothesis rightTailRejects

/-- Dotted tails have fully functional success and rejection outcomes. -/
theorem deriveTargetTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveTargetTailParses
      DeriveTargetTailRejects where
  toDeterministicOutcomeSpec := deriveTargetTailDeterministicOutcomeSpec
  successValueUnique := DeriveTargetTailParses.value_unique
  rejectOutputUnique := DeriveTargetTailRejects.output_unique

/-- A complete dotted derive target has one exact AST value. -/
theorem DeriveTargetParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftFirst, leftAfterFirst, leftComponents, leftFirstParsed,
      leftTail, leftShape⟩
  rcases rightParsed with
    ⟨rightFirst, rightAfterFirst, rightComponents, rightFirstParsed,
      rightTail, rightShape⟩
  rcases leftFirstParsed.result_unique rightFirstParsed with
    ⟨firstEq, afterFirstEq⟩
  subst firstEq
  subst afterFirstEq
  have componentsEq := leftTail.value_unique rightTail
  subst componentsEq
  exact leftShape.trans rightShape.symm

/-- A complete target fixes its exact AST value and final remainder. -/
theorem DeriveTargetParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A complete derive-target rejection has one exact failing endpoint. -/
theorem DeriveTargetRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveTargetRejects input left)
    (rightRejects : DeriveTargetRejects input right) : left = right := by
  cases leftRejects with
  | firstRejected leftComponentRejects =>
      cases rightRejects with
      | firstRejected rightComponentRejects =>
          exact leftComponentRejects.output_unique rightComponentRejects
      | tailRejected rightFirst rightTailRejects =>
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              leftComponentRejects ⟨_, _, rightFirst⟩)
  | tailRejected leftFirst leftTailRejects =>
      cases rightRejects with
      | firstRejected rightComponentRejects =>
          exact False.elim
            (deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
              rightComponentRejects ⟨_, _, leftFirst⟩)
      | tailRejected rightFirst rightTailRejects =>
          rcases leftFirst.result_unique rightFirst with
            ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          exact leftTailRejects.output_unique rightTailRejects

/-- Complete derive targets have exact deterministic ordinary outcomes. -/
theorem deriveTargetExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveTargetParses DeriveTargetRejects where
  toDeterministicOutcomeSpec := deriveTargetDeterministicOutcomeSpec
  successValueUnique := DeriveTargetParses.value_unique
  rejectOutputUnique := DeriveTargetRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
