import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Capture functionality and deterministic outcomes for balanced Core block
isolation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A balanced tail scan selects one closing span and endpoint. -/
theorem BalancedBlockTailScans.output_unique
    {input : Remainder} {depth offset : Nat}
    {leftClosing rightClosing : SourceSpan} {leftEnd rightEnd : Nat}
    (leftScan : BalancedBlockTailScans input depth offset leftClosing leftEnd)
    (rightScan : BalancedBlockTailScans input depth offset rightClosing
      rightEnd) : leftClosing = rightClosing ∧ leftEnd = rightEnd := by
  induction leftScan generalizing rightClosing rightEnd with
  | close leftToken =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
          exact ⟨rfl, rfl⟩
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotClosing kindEq.symm)
  | opening leftToken leftTail inductionHypothesis =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | opening rightToken rightTail =>
          exact inductionHypothesis rightTail
      | nestedClosing rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotOpening kindEq.symm)
  | nestedClosing leftToken leftTail inductionHypothesis =>
      cases rightScan with
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          cases tokenEq
      | nestedClosing rightToken rightTail =>
          exact inductionHypothesis rightTail
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (rightNotClosing kindEq.symm)
  | other leftToken leftNotOpening leftNotClosing leftTail
        inductionHypothesis =>
      cases rightScan with
      | close rightToken =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotClosing kindEq)
      | opening rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotOpening kindEq)
      | nestedClosing rightToken rightTail =>
          have tokenEq := tokenAt_unique leftToken rightToken
          have kindEq := congrArg (fun token => token.value) tokenEq
          exact False.elim (leftNotClosing kindEq)
      | other rightToken rightNotOpening rightNotClosing rightTail =>
          exact inductionHypothesis rightTail

/-- A balanced capture at one input has one exact span and endpoint. -/
theorem BalancedBlockCaptures.output_unique {input : Remainder}
    {left right : BalancedBlockCapture}
    (leftParsed : BalancedBlockCaptures input left)
    (rightParsed : BalancedBlockCaptures input right) : left = right := by
  cases leftParsed with
  | captured leftOpening leftTail =>
      cases rightParsed with
      | captured rightOpening rightTail =>
          have openingEq := tokenAt_unique leftOpening rightOpening
          rcases leftTail.output_unique rightTail with
            ⟨closingEq, endEq⟩
          cases openingEq
          cases closingEq
          cases endEq
          rfl

/-- Ordinary isolated-block success has one final parent remainder. -/
theorem IsolatedCoreBlockOrdinaryParses.output_unique
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input left afterLeft)
    (rightParsed : IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | direct leftAbsent leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact blockOutcomes.successOutputUnique leftBody rightBody
      | captured rightCapture rightBody =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
      | recovered rightCapture rightRejected =>
          exact False.elim (leftAbsent ⟨_, rightCapture⟩)
  | captured leftCapture leftBody =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
  | recovered leftCapture leftRejected =>
      cases rightParsed with
      | direct rightAbsent rightBody =>
          exact False.elim (rightAbsent ⟨_, leftCapture⟩)
      | captured rightCapture rightBody =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl
      | recovered rightCapture rightRejected =>
          have captureEq := leftCapture.output_unique rightCapture
          cases captureEq
          rfl

/-- An externally visible isolation rejection excludes every ordinary
isolated-block success. -/
theorem IsolatedCoreBlockRejects.disjointOrdinary
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input rejected : Remainder}
    (rejection : IsolatedCoreBlockRejects blockRejects input rejected) :
    ¬ ∃ body output,
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        output := by
  rintro ⟨body, output, successful⟩
  cases rejection with
  | direct captureAbsent bodyRejected =>
      cases successful with
      | direct otherAbsent bodyParsed =>
          exact blockOutcomes.successRejectDisjoint bodyRejected
            ⟨_, _, bodyParsed⟩
      | captured captureParsed bodyParsed =>
          exact captureAbsent ⟨_, captureParsed⟩
      | recovered captureParsed otherRejected =>
          exact captureAbsent ⟨_, captureParsed⟩

/-- Lift deterministic raw-block outcomes through balanced isolation and
captured child-rejection recovery. -/
theorem isolatedCoreBlockDeterministicOutcomeSpec
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects) :
    DeterministicOutcomeSpec
      (IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects)
      (IsolatedCoreBlockRejects blockRejects) where
  successOutputUnique :=
    IsolatedCoreBlockOrdinaryParses.output_unique blockOutcomes
  successRejectDisjoint :=
    IsolatedCoreBlockRejects.disjointOrdinary blockOutcomes

end Solcore.Syntax.DeclarativeGrammar
