import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeDeriveTargetOutcomeGrammar

/-! Deterministic and exclusive ordinary outcomes for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- One ordinary or diagnosed derive component has one final remainder. -/
theorem DeriveComponentParses.output_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveComponentParses input left afterLeft)
    (rightParsed : DeriveComponentParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | identifier leftIdentifier =>
      cases rightParsed with
      | identifier rightIdentifier =>
          exact IdentifierParses.output_unique leftIdentifier rightIdentifier
      | reserved keyword allowed span token =>
          have impossible := tokenAt_unique leftIdentifier.1 token
          cases impossible
  | reserved keyword allowed span token =>
      cases rightParsed with
      | identifier rightIdentifier =>
          have impossible := tokenAt_unique token rightIdentifier.1
          cases impossible
      | reserved => rfl

/-- Exact derive-component rejection excludes every component success. -/
theorem DeriveComponentRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveComponentRejects input rejected) :
    ¬ ∃ component output, DeriveComponentParses input component output := by
  rintro ⟨component, output, successful⟩
  cases rejection with
  | unavailable reservedAbsent identifierRejected =>
      cases successful with
      | identifier identifierParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            identifierRejected ⟨_, _, identifierParsed⟩
      | reserved keyword allowed span token =>
          exact absent_conflicts_token (reservedAbsent keyword allowed) token

/-- Derive components form a deterministic broad ordinary outcome. -/
theorem deriveComponentDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveComponentParses DeriveComponentRejects where
  successOutputUnique := DeriveComponentParses.output_unique
  successRejectDisjoint := DeriveComponentRejects.disjointOrdinary

/-- A maximal dotted derive-target tail has one final remainder. -/
theorem DeriveTargetTailParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetTailParses input left afterLeft)
    (rightParsed : DeriveTargetTailParses input right afterRight) :
    afterLeft = afterRight := by
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
          have afterComponentEq :=
            DeriveComponentParses.output_unique leftComponent rightComponent
          subst afterComponentEq
          exact inductionHypothesis rightTail

/-- Exact dotted-tail rejection excludes every maximal tail success. -/
theorem DeriveTargetTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveTargetTailRejects input rejected) :
    ¬ ∃ components output,
      DeriveTargetTailParses input components output := by
  induction rejection with
  | componentRejected dotSpan dotParsed componentRejected =>
      rintro ⟨components, output, successful⟩
      cases successful with
      | done dotAbsent =>
          exact absent_conflicts_token dotAbsent dotParsed.1
      | next successfulDotSpan successfulDot componentParsed tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          exact deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
            componentRejected ⟨_, _, componentParsed⟩
  | laterRejected dotSpan dotParsed rejectedComponent tailRejected
      inductionHypothesis =>
      rintro ⟨components, output, successful⟩
      cases successful with
      | done dotAbsent =>
          exact absent_conflicts_token dotAbsent dotParsed.1
      | next successfulDotSpan successfulDot successfulComponent
          successfulTail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          have afterComponentEq := DeriveComponentParses.output_unique
            rejectedComponent successfulComponent
          subst afterComponentEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Dotted derive-target tails form a deterministic broad ordinary outcome. -/
theorem deriveTargetTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveTargetTailParses
      DeriveTargetTailRejects where
  successOutputUnique := DeriveTargetTailParses.output_unique
  successRejectDisjoint := DeriveTargetTailRejects.disjointOrdinary

/-- A complete dotted derive target has one final remainder. -/
theorem DeriveTargetParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveTarget}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveTargetParses input left afterLeft)
    (rightParsed : DeriveTargetParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftFirst, leftAfterFirst, leftComponents, leftFirstParsed,
      leftTail, leftShape⟩
  rcases rightParsed with
    ⟨rightFirst, rightAfterFirst, rightComponents, rightFirstParsed,
      rightTail, rightShape⟩
  have afterFirstEq := DeriveComponentParses.output_unique leftFirstParsed
    rightFirstParsed
  subst afterFirstEq
  exact DeriveTargetTailParses.output_unique leftTail rightTail

/-- Exact derive-target rejection excludes every complete target success. -/
theorem DeriveTargetRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveTargetRejects input rejected) :
    ¬ ∃ target output, DeriveTargetParses input target output := by
  rintro ⟨target, output, successful⟩
  rcases successful with
    ⟨first, afterFirst, components, firstParsed, tail, shape⟩
  cases rejection with
  | firstRejected componentRejected =>
      exact deriveComponentDeterministicOutcomeSpec.successRejectDisjoint
        componentRejected ⟨_, _, firstParsed⟩
  | tailRejected rejectedFirst tailRejected =>
      have afterFirstEq := DeriveComponentParses.output_unique rejectedFirst
        firstParsed
      subst afterFirstEq
      exact deriveTargetTailDeterministicOutcomeSpec.successRejectDisjoint
        tailRejected ⟨_, _, tail⟩

/-- Complete derive targets form a deterministic broad ordinary outcome. -/
theorem deriveTargetDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveTargetParses DeriveTargetRejects where
  successOutputUnique := DeriveTargetParses.output_unique
  successRejectDisjoint := DeriveTargetRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
