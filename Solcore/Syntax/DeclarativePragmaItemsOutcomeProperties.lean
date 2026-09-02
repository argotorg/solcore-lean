import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativePragmaItemsOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : PragmaItemsTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- A pragma-item suffix has one successful final remainder. -/
theorem PragmaItemsTailOrdinaryParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => rfl
      | trailing _ rightCommaPresent _ _ =>
          exact False.elim
            (present_conflicts_absent rightCommaPresent leftCommaAbsent)
      | next _ rightCommaPresent _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent rightCommaPresent leftCommaAbsent)
  | trailing leftCommaSpan leftCommaPresent leftComma leftSemicolon =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (present_conflicts_absent leftCommaPresent rightCommaAbsent)
      | trailing _ _ rightComma rightSemicolon =>
          exact exactToken_output_unique leftComma rightComma
      | next _ _ rightComma rightSemicolonAbsent rightItem rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (present_conflicts_absent leftSemicolon rightSemicolonAbsent)
  | next leftCommaSpan leftCommaPresent leftComma leftSemicolonAbsent
      leftItem leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (present_conflicts_absent leftCommaPresent rightCommaAbsent)
      | trailing _ _ rightComma rightSemicolon =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (present_conflicts_absent rightSemicolon leftSemicolonAbsent)
      | next _ _ rightComma rightSemicolonAbsent rightItem rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterItemEq := IdentifierParses.output_unique leftItem rightItem
          subst afterItemEq
          exact inductionHypothesis rightTail

/-- Exact pragma-tail rejection excludes every successful suffix. -/
theorem PragmaItemsTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : PragmaItemsTailRejects input rejected) :
    ¬ ∃ items output,
      PragmaItemsTailOrdinaryParses input items output := by
  induction rejection with
  | identifierRejected rejectedCommaSpan rejectedCommaPresent rejectedComma
      rejectedSemicolonAbsent itemRejected =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done successfulCommaAbsent =>
          exact present_conflicts_absent rejectedCommaPresent
            successfulCommaAbsent
      | trailing _ _ successfulComma successfulSemicolon =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact present_conflicts_absent successfulSemicolon
            rejectedSemicolonAbsent
      | next _ _ successfulComma successfulSemicolonAbsent itemParsed tail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            itemRejected ⟨_, _, itemParsed⟩
  | laterRejected rejectedCommaSpan rejectedCommaPresent rejectedComma
      rejectedSemicolonAbsent rejectedItem tailRejected inductionHypothesis =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done successfulCommaAbsent =>
          exact present_conflicts_absent rejectedCommaPresent
            successfulCommaAbsent
      | trailing _ _ successfulComma successfulSemicolon =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact present_conflicts_absent successfulSemicolon
            rejectedSemicolonAbsent
      | next _ _ successfulComma successfulSemicolonAbsent successfulItem
          successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterItemEq := IdentifierParses.output_unique rejectedItem
            successfulItem
          subst afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Deterministic broad outcomes for pragma-item suffixes. -/
theorem pragmaItemsTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaItemsTailOrdinaryParses
      PragmaItemsTailRejects where
  successOutputUnique := PragmaItemsTailOrdinaryParses.output_unique
  successRejectDisjoint := PragmaItemsTailRejects.disjointOrdinary

/-- A complete pragma-item scan has one successful final remainder. -/
theorem PragmaItemsOrdinaryParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | empty leftSemicolon =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightSemicolonAbsent rightFirst rightTail =>
          exact False.elim
            (present_conflicts_absent leftSemicolon rightSemicolonAbsent)
  | nonempty leftSemicolonAbsent leftFirst leftTail =>
      cases rightParsed with
      | empty rightSemicolon =>
          exact False.elim
            (present_conflicts_absent rightSemicolon leftSemicolonAbsent)
      | nonempty rightSemicolonAbsent rightFirst rightTail =>
          have afterFirstEq := IdentifierParses.output_unique leftFirst
            rightFirst
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Exact complete pragma-item rejection excludes every successful scan. -/
theorem PragmaItemsRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : PragmaItemsRejects input rejected) :
    ¬ ∃ items output, PragmaItemsOrdinaryParses input items output := by
  rintro ⟨items, output, successful⟩
  cases rejection with
  | firstIdentifierRejected semicolonAbsent firstRejected =>
      cases successful with
      | empty semicolonPresent =>
          exact present_conflicts_absent semicolonPresent semicolonAbsent
      | nonempty successfulSemicolonAbsent firstParsed tailParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            firstRejected ⟨_, _, firstParsed⟩
  | tailRejected semicolonAbsent rejectedFirst tailRejected =>
      cases successful with
      | empty semicolonPresent =>
          exact present_conflicts_absent semicolonPresent semicolonAbsent
      | nonempty successfulSemicolonAbsent successfulFirst successfulTail =>
          have afterFirstEq := IdentifierParses.output_unique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact pragmaItemsTailDeterministicOutcomeSpec.successRejectDisjoint
            tailRejected ⟨_, _, successfulTail⟩

/-- Deterministic broad outcomes for the complete pragma-item scan. -/
theorem pragmaItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaItemsOrdinaryParses PragmaItemsRejects where
  successOutputUnique := PragmaItemsOrdinaryParses.output_unique
  successRejectDisjoint := PragmaItemsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
