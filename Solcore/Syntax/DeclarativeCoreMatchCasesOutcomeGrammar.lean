import Solcore.Syntax.DeclarativeCoreMatchComponentOutcomeGrammar

/-!
Parser-independent ordinary success and exact rejection for the maximal Core
match-case sequence.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Maximal forward-order sequence of diagnostic-inclusive Core match cases. -/
inductive MatchCasesOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → List Syntax.MatchCase → Remainder → Prop where
  | done {input : Remainder}
      (caseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .caseKw)) :
      MatchCasesOrdinaryParses statementOrdinary patternOrdinary input [] input
  | next {input afterCase output : Remainder} {arm : Syntax.MatchCase}
      {arms : List Syntax.MatchCase}
      (armParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
        input arm afterCase)
      (progress : input.cursor < afterCase.cursor)
      (tail : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
        afterCase arms output) :
      MatchCasesOrdinaryParses statementOrdinary patternOrdinary input
        (arm :: arms) output

/-- Exact rejection after a guarded Core match-case iteration.

The positive `case` evidence on `firstRejected` prevents the standalone arm
relation's marker-missing alternative from creating a false list rejection.
-/
inductive MatchCasesRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (casePresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span, value := .keyword .caseKw
        })
      (armRejected : MatchCaseRejects statementOrdinary statementRejects
        patternOrdinary patternRejects input rejected) :
      MatchCasesRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected
  | laterRejected {input afterCase rejected : Remainder}
      {arm : Syntax.MatchCase}
      (armParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
        input arm afterCase)
      (progress : input.cursor < afterCase.cursor)
      (tailRejected : MatchCasesRejects statementOrdinary statementRejects
        patternOrdinary patternRejects afterCase rejected) :
      MatchCasesRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
