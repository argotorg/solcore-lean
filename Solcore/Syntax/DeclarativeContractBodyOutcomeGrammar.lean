import Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeGrammar
import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeGrammar

/-!
Broad ordinary outcomes for contract bodies.  The member loop preserves source
order, rewinds a rejected member to its original cursor, and recovers only when
that cursor is not a declaration boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A rejected derive-aware member retains its failed cursor while preserving
the token carrier and active window needed for the body-loop rewind. -/
def ContractMemberRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, ContractMemberRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Forward-order contract members ending at the exact closing brace.

The closing branch has priority.  Otherwise a member either succeeds with
strict progress, or its window-preserving rejection is rewound and recovered
from the original cursor when no recovery boundary is present. -/
inductive ContractMemberTailOrdinaryParses :
    Remainder → List Syntax.ContractMember → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ContractMemberTailOrdinaryParses input [] closingSpan output
  | direct {input afterMember output : Remainder}
      {member : Syntax.ContractMember} {members : List Syntax.ContractMember}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberParsed : ContractMemberOrdinaryParses input member afterMember)
      (progress : input.cursor < afterMember.cursor)
      (tail : ContractMemberTailOrdinaryParses afterMember members
        closingSpan output) :
      ContractMemberTailOrdinaryParses input (member :: members) closingSpan
        output
  | recovered {input afterRecovery output : Remainder}
      {member : Syntax.ContractMember} {members : List Syntax.ContractMember}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (recoveryParsed : ContractMemberRecoveryParses input member
        afterRecovery)
      (tail : ContractMemberTailOrdinaryParses afterRecovery members
        closingSpan output) :
      ContractMemberTailOrdinaryParses input (member :: members) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward members. -/
def ContractMemberTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.ContractMember)
    (output : Remainder) : Prop :=
  ContractMemberTailOrdinaryParses input tail.2 tail.1 output

/-- Exact first rejection of the prioritized contract-member body loop. -/
inductive ContractMemberTailRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberTailRejects input input
  | memberAtBoundary {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryPresent : ContractMemberRecoveryBoundaryStartsAt input) :
      ContractMemberTailRejects input input
  | recoveryRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (rejectedRecovery : ContractMemberRecoveryRejects input rejected) :
      ContractMemberTailRejects input rejected
  | laterDirect {input afterMember rejected : Remainder}
      {member : Syntax.ContractMember}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberParsed : ContractMemberOrdinaryParses input member afterMember)
      (progress : input.cursor < afterMember.cursor)
      (tailRejected : ContractMemberTailRejects afterMember rejected) :
      ContractMemberTailRejects input rejected
  | laterRecovered {input afterRecovery rejected : Remainder}
      {member : Syntax.ContractMember}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (recoveryParsed : ContractMemberRecoveryParses input member
        afterRecovery)
      (tailRejected : ContractMemberTailRejects afterRecovery rejected) :
      ContractMemberTailRejects input rejected

/-- Exact braces, covered span, and source-order broad contract members. -/
inductive ContractBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.ContractMember →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {members : List Syntax.ContractMember}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (membersParsed : ContractMemberTailOrdinaryParses afterOpening members
        closingSpan output) :
      ContractBodyOrdinaryParses input
        (SourceSpan.cover openingSpan closingSpan) members output

/-- Single-output adapter retaining the body span and forward members. -/
def ContractBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.ContractMember)
    (output : Remainder) : Prop :=
  ContractBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of the opening brace or the subsequent member loop. -/
inductive ContractBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      ContractBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : ContractMemberTailRejects afterOpening rejected) :
      ContractBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
