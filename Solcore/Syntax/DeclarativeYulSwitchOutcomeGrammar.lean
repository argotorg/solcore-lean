import Solcore.Syntax.DeclarativeYulBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulSwitchGrammar

/-!
Parser-independent ordinary successes and exact rejection traces for inline-
Yul switch arms, case lists, optional defaults, and complete switches.

The executable empty-case branch is an ordinary diagnosed `.error` success,
not a rejection.  Its span and final remainder are retained exactly.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary case-arm success uses ordinary recursive statements. -/
abbrev YulCaseArmOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulCaseArmParses statementOrdinary

/-- Exact sequential rejection stage of one `case` arm. -/
inductive YulCaseArmRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .caseKw)) :
      YulCaseArmRejects statementOrdinary statementRejects input input
  | literalMissing {input afterMarker : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalAbsent : ¬ YulLiteralStartsAt afterMarker) :
      YulCaseArmRejects statementOrdinary statementRejects input afterMarker
  | bodyRejected {input afterMarker afterLiteral rejected : Remainder}
      {literal : Syntax.YulLiteral} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalParsed : YulLiteralParses afterMarker literal afterLiteral)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterLiteral rejected) :
      YulCaseArmRejects statementOrdinary statementRejects input rejected

/-- Ordinary case-list success is the existing forward maximal list grammar. -/
abbrev YulCaseListOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulCaseListParses statementOrdinary

/-- Exact rejection in a case-list iteration.

`firstRejected` records the loop guard separately.  This rules out the
standalone arm relation's marker-missing branch at a guarded iteration.
-/
inductive YulCaseListRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (casePresent : ∃ span, TokenAt input.tokens input.endIndex input.cursor
        { span, value := .keyword .caseKw })
      (armRejected : YulCaseArmRejects statementOrdinary statementRejects
        input rejected) :
      YulCaseListRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterArm rejected : Remainder}
      {arm : Syntax.YulCase}
      (armParsed : YulCaseArmOrdinaryParses statementOrdinary input arm
        afterArm)
      (progress : input.cursor < afterArm.cursor)
      (tailRejected : YulCaseListRejects statementOrdinary statementRejects
        afterArm rejected) :
      YulCaseListRejects statementOrdinary statementRejects input rejected

/-- Ordinary optional-default success uses ordinary recursive statements. -/
abbrev OptionalYulDefaultOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  OptionalYulDefaultParses statementOrdinary

/-- The guarded optional default can reject only in its braced body. -/
inductive OptionalYulDefaultRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterMarker rejected) :
      OptionalYulDefaultRejects statementOrdinary statementRejects input
        rejected

/-- Every ordinary complete-switch success, including the diagnosed empty-
case `.error` result. -/
inductive YulSwitchStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | nonempty {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {head : Syntax.YulCase}
      {tail : List Syntax.YulCase} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee (head :: tail) afterCases)
      (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
        afterCases defaultSpan defaultBody output) :
      YulSwitchStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span (head :: tail) defaultSpan)
        value := .switch scrutinee { head, tail } defaultBody
      } output
  | empty {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee [] afterCases)
      (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
        afterCases defaultSpan defaultBody output) :
      YulSwitchStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span [] defaultSpan)
        value := .error
      } output

/-- Exact sequential rejection stage of a complete switch. -/
inductive YulSwitchStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .switchKw)) :
      YulSwitchStatementRejects statementOrdinary statementRejects input input
  | scrutineeRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeRejected : YulExpressionRejects afterMarker rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected
  | casesRejected {input afterMarker afterScrutinee rejected : Remainder}
      {scrutinee : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesRejected : YulCaseListRejects statementOrdinary statementRejects
        afterScrutinee rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected
  | defaultRejected
      {input afterMarker afterScrutinee afterCases rejected : Remainder}
      {scrutinee : Syntax.YulExpr} {cases : List Syntax.YulCase}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListOrdinaryParses statementOrdinary
        afterScrutinee cases afterCases)
      (defaultRejected : OptionalYulDefaultRejects statementOrdinary
        statementRejects afterCases rejected) :
      YulSwitchStatementRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
