import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.Grammar.YulFuel

/-!
Declarative grammar of statements and Core blocks.

Main declarations: `CoreBlockOrdinaryParses`, `CoreBlockRejects`,
`IfStatementOrdinaryParses`,
`WhileStatementOrdinaryParses`, `MatchCasesOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementGrammar
/-! Parser-independent grammar for clean Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming conversion of parsed scrutinees to a nonempty carrier. -/
inductive RequireScrutineesParses :
    DelimitedList Syntax.Expr → Remainder →
      NonemptyDelimitedList Syntax.Expr → Remainder → Prop where
  | parsed {input : Remainder} {span : SourceSpan}
      {head : Syntax.Expr} {tail : List Syntax.Expr} :
      RequireScrutineesParses { span, elements := head :: tail } input {
        span
        elements := { head, tail }
      } input

/-- One exact `case pattern { ... }` arm. -/
inductive MatchCaseParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (patternParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.MatchCase → Remainder → Prop where
  | parsed {input afterMarker afterPattern output : Remainder}
      {pattern : Syntax.Pattern} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternParsed : patternParses afterMarker pattern afterPattern)
      (bodyParsed : CoreBlockParses statementParses .require afterPattern body
        output) :
      MatchCaseParses statementParses patternParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { pattern, body }
      } output

/-- Maximal, forward-order sequence of explicit `case` arms. -/
inductive MatchCasesParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (patternParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → List Syntax.MatchCase → Remainder → Prop where
  | done {input : Remainder}
      (caseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .caseKw)) :
      MatchCasesParses statementParses patternParses input [] input
  | next {input afterCase output : Remainder} {arm : Syntax.MatchCase}
      {arms : List Syntax.MatchCase}
      (armParsed : MatchCaseParses statementParses patternParses input arm
        afterCase)
      (progress : input.cursor < afterCase.cursor)
      (tail : MatchCasesParses statementParses patternParses afterCase arms
        output) :
      MatchCasesParses statementParses patternParses input (arm :: arms)
        output

/-- Prioritized optional `default { ... }` body. -/
inductive OptionalDefaultBodyParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop) :
    Remainder → Option Syntax.Block → Remainder → Prop where
  | absent {input : Remainder}
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalDefaultBodyParses statementParses input none input
  | present {input afterMarker output : Remainder} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyParsed : CoreBlockParses statementParses .require afterMarker body
        output) :
      OptionalDefaultBodyParses statementParses input (some body) output

/-- Pure arity used by the executable match validator. -/
def matchPatternArity (scrutineeCount : Nat) (pattern : Syntax.Pattern) : Nat :=
  if scrutineeCount > 1 then
    match pattern.value with
    | .tuple elements => elements.elements.length
    | _ => 1
  else
    1

/-- Every explicit case has exactly the scrutinee arity. -/
def MatchCaseAritiesValid (scrutineeCount : Nat)
    (cases : List Syntax.MatchCase) : Prop :=
  ∀ arm ∈ cases,
    matchPatternArity scrutineeCount arm.value.pattern = scrutineeCount

/-- Clean arms exclude the executable missing-arm diagnostic branch. -/
def MatchArmsPresent (cases : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) : Prop :=
  (cases.isEmpty && defaultBody.isNone) = false

/-- Exact diagnostic-free grammar of a complete Core `match` statement. -/
inductive MatchStatementParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (patternParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterValues afterScrutinees afterOpening
      afterCases afterDefault output : Remainder}
      {values : DelimitedList Syntax.Expr}
      {scrutinees : NonemptyDelimitedList Syntax.Expr}
      {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .matchKw) input markerSpan
        afterMarker)
      (valuesParsed : NonemptyTrailingDelimitedListParses .leftParen
        .rightParen expressionParses afterMarker values afterValues)
      (scrutineesRequired : RequireScrutineesParses values afterValues
        scrutinees afterScrutinees)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) afterScrutinees
        openingSpan afterOpening)
      (casesParsed : MatchCasesParses statementParses patternParses
        afterOpening cases afterCases)
      (defaultParsed : OptionalDefaultBodyParses statementParses afterCases
        defaultBody afterDefault)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) afterDefault
        closingSpan output)
      (aritiesValid : MatchCaseAritiesValid
        scrutinees.elements.toList.length cases)
      (armsPresent : MatchArmsPresent cases defaultBody) :
      MatchStatementParses statementParses expressionParses patternParses
        input {
          span := SourceSpan.cover markerSpan closingSpan
          value := .matchWith scrutinees {
            span := SourceSpan.cover openingSpan closingSpan
            value := { cases, defaultBody }
          }
        } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementControlGrammar
/-!
Parser-independent grammar for Core block, terminated-control, while, and if
statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A Core block retained as one statement. -/
inductive BlockStatementParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input output : Remainder} {body : Syntax.Block}
      (bodyParsed : blockParses input body output) :
      BlockStatementParses blockParses input {
        span := body.span
        value := .block body.value
      } output

/-- Exact keyword-plus-semicolon grammar shared by `break` and `continue`. -/
inductive TerminatedControlStatementParses
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        afterMarker)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterMarker
        semicolonSpan output) :
      TerminatedControlStatementParses keyword statementValue input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := statementValue
      } output

/-- Prioritized optional `else` body. -/
inductive OptionalElseBodyParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Option Syntax.Block → Remainder → Prop where
  | absent {input : Remainder}
      (elseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .elseKw)) :
      OptionalElseBodyParses blockParses input none input
  | present {input afterMarker output : Remainder} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .elseKw) input markerSpan
        afterMarker)
      (bodyParsed : blockParses afterMarker body output) :
      OptionalElseBodyParses blockParses input (some body) output

/-- Exact canonical Core `while` statement grammar. -/
inductive WhileStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterCondition afterClosing output :
        Remainder}
      {condition : Syntax.Expr} {body : Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionParses afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (bodyParsed : blockParses afterClosing body output) :
      WhileStatementParses expressionParses blockParses input {
        span := SourceSpan.cover markerSpan body.span
        value := .whileLoop condition body
      } output

/-- Exact canonical Core `if` statement grammar with prioritized optional
`else`. -/
inductive IfStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterCondition afterClosing
        afterThen output : Remainder}
      {condition : Syntax.Expr} {thenBody : Syntax.Block}
      {elseBody : Option Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionParses afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenParsed : blockParses afterClosing thenBody afterThen)
      (elseParsed : OptionalElseBodyParses blockParses afterThen elseBody
        output) :
      IfStatementParses expressionParses blockParses input {
        span := SourceSpan.cover markerSpan
          (elseBody.map (fun body => body.span) |>.getD thenBody.span)
        value := .ifThen condition thenBody elseBody
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
/-!
Parser-independent ordinary success and exact rejection for raw Core blocks.

Ordinary success deliberately omits `CoreBlockTailsValid`: the executable tail
validator reports violations with diagnostics while retaining the successful
block, token window, and cursor.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success of a raw Core block.  The policy is retained
to identify the executable parser, but diagnostic tail validation does not
change the accepted syntax value or remainder. -/
inductive CoreBlockOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (policy : CoreBlockTailPolicy) :
    Remainder → Syntax.Block → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {body : List Syntax.Statement} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsParses statementOrdinary afterOpening body
        closingSpan output) :
      CoreBlockOrdinaryParses statementOrdinary policy input {
        span := SourceSpan.cover openingSpan closingSpan
        value := body
      } output

/-- Exact rejection after a Core block opening brace has been consumed. -/
inductive CoreBlockItemsRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | missingClose {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      CoreBlockItemsRejects statementOrdinary statementRejects input input
  | statementRejected {input rejected : Remainder}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementRejected : statementRejects input rejected) :
      CoreBlockItemsRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.Statement}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementOrdinary input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : CoreBlockItemsRejects statementOrdinary statementRejects
        afterStatement rejected) :
      CoreBlockItemsRejects statementOrdinary statementRejects input rejected

/-- Exact rejection of a complete raw Core block. -/
inductive CoreBlockRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (policy : CoreBlockTailPolicy) : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      CoreBlockRejects statementOrdinary statementRejects policy input input
  | itemsRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (itemsRejected : CoreBlockItemsRejects statementOrdinary statementRejects
        afterOpening rejected) :
      CoreBlockRejects statementOrdinary statementRejects policy input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementIfOutcomeGrammar
/-! Ordinary successes and exact rejections for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive optional-else success over raw Core blocks. -/
abbrev OptionalElseBodyOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  OptionalElseBodyParses
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- A present optional `else` rejects exactly through its required body. -/
inductive OptionalElseBodyRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .elseKw) input markerSpan
        afterMarker)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterMarker rejected) :
      OptionalElseBodyRejects statementOrdinary statementRejects input rejected

/-- Diagnostic-inclusive complete Core `if` success. -/
abbrev IfStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  IfStatementParses expressionOrdinary
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact first rejection stage of one canonical Core `if` statement. -/
inductive IfStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .ifKw)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input input
  | openingMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterMarker
  | conditionRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionRejected : expressionRejects afterOpening rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterCondition : Remainder}
      {condition : Syntax.Expr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .rightParen)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterCondition
  | thenRejected
      {input afterMarker afterOpening afterCondition afterClosing rejected :
        Remainder}
      {condition : Syntax.Expr}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | elseRejected
      {input afterMarker afterOpening afterCondition afterClosing afterThen
        rejected : Remainder}
      {condition : Syntax.Expr} {thenBody : Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterClosing thenBody afterThen)
      (elseRejected : OptionalElseBodyRejects statementOrdinary
        statementRejects afterThen rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeGrammar
/-! Ordinary outcomes for Core block and terminated-control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev TerminatedControlStatementOrdinaryParses :=
  TerminatedControlStatementParses

/-- Exact marker or semicolon rejection of `break` and `continue`. -/
inductive TerminatedControlStatementRejects (keyword : HardKeyword) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword keyword)) :
      TerminatedControlStatementRejects keyword input input
  | semicolonMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        afterMarker)
      (semicolonAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .semicolon)) :
      TerminatedControlStatementRejects keyword input afterMarker

/-- Diagnostic-inclusive block statement success. -/
abbrev BlockStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop) :=
  BlockStatementParses
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact raw-block rejection propagated through `blockStatement`. -/
abbrev BlockStatementRejects
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :=
  CoreBlockRejects statementOrdinary statementRejects .require

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeGrammar
/-! Ordinary success and exact rejection for canonical Core `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive `while` success with an ordinary condition and raw
required-policy Core block. -/
abbrev WhileStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  WhileStatementParses expressionOrdinary
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact first-failing stage of a canonical Core `while` statement.  The
marker remains an identifier token because `while` is contextual. -/
inductive WhileStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.while.spelling)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input input
  | openingMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterMarker
  | conditionRejected
      {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (rejectedCondition : expressionRejects afterOpening rejected) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterCondition : Remainder}
      {condition : Syntax.Expr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .rightParen)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterCondition
  | bodyRejected
      {input afterMarker afterOpening afterCondition afterClosing rejected :
        Remainder}
      {condition : Syntax.Expr}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (rejectedBody : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchComponentOutcomeGrammar
/-!
Diagnostic-inclusive ordinary success and exact rejection for Core match
components.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One ordinary `case pattern { ... }` arm.  Raw block-tail diagnostics do
not remove the successful syntax value. -/
inductive MatchCaseOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.MatchCase → Remainder → Prop where
  | parsed {input afterMarker afterPattern output : Remainder}
      {pattern : Syntax.Pattern} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternParsed : patternOrdinary afterMarker pattern afterPattern)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterPattern body output) :
      MatchCaseOrdinaryParses statementOrdinary patternOrdinary input {
        span := SourceSpan.cover markerSpan body.span
        value := { pattern, body }
      } output

/-- Exact first failing stage of one Core match case. -/
inductive MatchCaseRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .caseKw)) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input input
  | patternRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternRejected : patternRejects afterMarker rejected) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected
  | bodyRejected {input afterMarker afterPattern rejected : Remainder}
      {pattern : Syntax.Pattern} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (patternParsed : patternOrdinary afterMarker pattern afterPattern)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterPattern rejected) :
      MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects input rejected

/-- Prioritized optional `default` success, including raw block-tail
diagnostics. -/
inductive OptionalDefaultBodyOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :
    Remainder → Option Syntax.Block → Remainder → Prop where
  | absent {input : Remainder}
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalDefaultBodyOrdinaryParses statementOrdinary input none input
  | present {input afterMarker output : Remainder} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterMarker body output) :
      OptionalDefaultBodyOrdinaryParses statementOrdinary input (some body)
        output

/-- A present optional `default` rejects only through its raw body. -/
inductive OptionalDefaultBodyRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterMarker rejected) :
      OptionalDefaultBodyRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeGrammar
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssemblyStatementGrammar
/-!
Parser-independent bridge grammar for a Core `assembly` statement whose
braced Yul body is supplied by an abstract relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact Core wrapper around an abstract Yul body grammar. -/
inductive AssemblyStatementParses
    (yulBodyParses :
      Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {bodySpan : SourceSpan} {body : List Syntax.YulStmt}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .assemblyKw) input
        markerSpan afterMarker)
      (bodyParsed : yulBodyParses afterMarker bodySpan body output) :
      AssemblyStatementParses yulBodyParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .assembly body
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeBalancedBlockGrammar
/-!
Parser-independent lexical recognition of one balanced braced token window.

The scanner counts only brace tokens.  Every other token is retained as an
opaque step, so the relation fixes the first right brace that returns the
opening depth to zero without depending on statement parsing or parser fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Source range and child-window endpoint selected by balanced capture. -/
structure BalancedBlockCapture where
  span : SourceSpan
  endIndex : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

/--
Successful tail scan from one positive brace depth and relative token offset.
The result endpoint is one past the matching closing brace.
-/
inductive BalancedBlockTailScans (input : Remainder) :
    Nat → Nat → SourceSpan → Nat → Prop where
  | close {offset : Nat} {closingSpan : SourceSpan}
      (closingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := closingSpan
          value := .symbol .rightBrace
        }) :
      BalancedBlockTailScans input 1 offset closingSpan
        (input.cursor + offset + 1)
  | opening {depth offset capturedEnd : Nat}
      {openingSpan closingSpan : SourceSpan}
      (openingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := openingSpan
          value := .symbol .leftBrace
        })
      (tail : BalancedBlockTailScans input (depth + 1) (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input depth offset closingSpan capturedEnd
  | nestedClosing {depth offset capturedEnd : Nat}
      {nestedSpan closingSpan : SourceSpan}
      (closingToken : TokenAt input.tokens input.endIndex
        (input.cursor + offset) {
          span := nestedSpan
          value := .symbol .rightBrace
        })
      (tail : BalancedBlockTailScans input (depth + 1) (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input (depth + 2) offset closingSpan capturedEnd
  | other {depth offset capturedEnd : Nat} {token : Token}
      {closingSpan : SourceSpan}
      (tokenAt : TokenAt input.tokens input.endIndex
        (input.cursor + offset) token)
      (notOpening : token.value ≠ .symbol .leftBrace)
      (notClosing : token.value ≠ .symbol .rightBrace)
      (tail : BalancedBlockTailScans input depth (offset + 1)
        closingSpan capturedEnd) :
      BalancedBlockTailScans input depth offset closingSpan capturedEnd

/-- Exact first balanced block capture beginning at the current cursor. -/
inductive BalancedBlockCaptures :
    Remainder → BalancedBlockCapture → Prop where
  | captured {input : Remainder} {openingSpan closingSpan : SourceSpan}
      {capturedEnd : Nat}
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftBrace
      })
      (tail : BalancedBlockTailScans input 1 1 closingSpan capturedEnd) :
      BalancedBlockCaptures input {
        span := SourceSpan.cover openingSpan closingSpan
        endIndex := capturedEnd
        endByte := closingSpan.endByte
      }

namespace BalancedBlockCapture

/-- Parser remainder inside the captured brace window. -/
def childRemainder (input : Remainder)
    (captured : BalancedBlockCapture) : Remainder := {
  tokens := input.tokens
  endIndex := captured.endIndex
  cursor := input.cursor
}

/-- Parent remainder immediately after the captured closing brace. -/
def parentRemainder (input : Remainder)
    (captured : BalancedBlockCapture) : Remainder := {
  input with cursor := captured.endIndex
}

end BalancedBlockCapture

/-- Every successful tail capture ends strictly after its starting cursor. -/
theorem BalancedBlockTailScans.cursor_lt {input : Remainder}
    {depth offset : Nat} {closingSpan : SourceSpan} {capturedEnd : Nat}
    (scan : BalancedBlockTailScans input depth offset closingSpan capturedEnd) :
    input.cursor < capturedEnd := by
  induction scan with
  | close closingToken =>
      rcases closingToken with ⟨inside, found⟩
      omega
  | opening openingToken tail inductionHypothesis => exact inductionHypothesis
  | nestedClosing closingToken tail inductionHypothesis =>
      exact inductionHypothesis
  | other tokenAt notOpening notClosing tail inductionHypothesis =>
      exact inductionHypothesis

/-- A balanced capture endpoint remains inside the original token window. -/
theorem BalancedBlockTailScans.endIndex_le {input : Remainder}
    {depth offset : Nat} {closingSpan : SourceSpan} {capturedEnd : Nat}
    (scan : BalancedBlockTailScans input depth offset closingSpan capturedEnd) :
    capturedEnd ≤ input.endIndex := by
  induction scan with
  | close closingToken =>
      rcases closingToken with ⟨inside, found⟩
      omega
  | opening openingToken tail inductionHypothesis => exact inductionHypothesis
  | nestedClosing closingToken tail inductionHypothesis =>
      exact inductionHypothesis
  | other tokenAt notOpening notClosing tail inductionHypothesis =>
      exact inductionHypothesis

/-- No lexically balanced braced capture begins at this cursor. -/
def BalancedBlockCaptureAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ captured, BalancedBlockCaptures input captured

/--
Exact behavior of the isolation wrapper over an abstract block grammar.

Without a capture the underlying grammar runs in the parent window.  With a
capture it runs in the smaller child window while the parent always resumes
immediately after the captured closing brace.
-/
inductive IsolatedCoreBlockParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Block → Remainder → Prop where
  | direct {input output : Remainder} {body : Syntax.Block}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockParses input body output) :
      IsolatedCoreBlockParses blockParses input body output
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockParses (capture.childRemainder input) body
        childOutput) :
      IsolatedCoreBlockParses blockParses input body
        (capture.parentRemainder input)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeGrammar
/-!
Parser-independent ordinary outcomes for balanced Core block isolation.

When no balanced capture exists, the underlying block outcome is exposed in
the parent window.  A balanced capture runs the block outcome in its child
window and always resumes the parent after the matching closing brace;
ordinary child rejection is recovered as an empty block.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success of a balanced isolated block. -/
inductive IsolatedCoreBlockOrdinaryParses
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop)
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Block → Remainder → Prop where
  | direct {input output : Remainder} {body : Syntax.Block}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockOrdinary input body output) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        output
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockOrdinary (capture.childRemainder input) body
        childOutput) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        (capture.parentRemainder input)
  | recovered {input childRejected : Remainder}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyRejected : blockRejects (capture.childRemainder input)
        childRejected) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input {
        span := capture.span
        value := []
      } (capture.parentRemainder input)

/-- Exact external rejection of isolation: only an uncaptured underlying
block rejection escapes the wrapper. -/
inductive IsolatedCoreBlockRejects
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | direct {input rejected : Remainder}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyRejected : blockRejects input rejected) :
      IsolatedCoreBlockRejects blockRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar
/-!
Parser-independent grammar for the shared optional suffixes and the canonical
Core `let` and `return` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized optional statement semicolon. -/
inductive OptionalStatementSemicolonParses :
    Remainder → Option SourceSpan → Remainder → Prop where
  | absent {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      OptionalStatementSemicolonParses input none input
  | present {input output : Remainder} (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      OptionalStatementSemicolonParses input (some semicolonSpan) output

/-- Optional return value, where a current semicolon commits to no value. -/
inductive OptionalReturnValueParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option Syntax.Expr → Remainder → Prop where
  | absent {input : Remainder} (semicolonSpan : SourceSpan)
      (semicolonCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := semicolonSpan
        value := .symbol .semicolon
      }) :
      OptionalReturnValueParses expressionParses input none input
  | present {input output : Remainder} {value : Syntax.Expr}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (valueParsed : expressionParses input value output) :
      OptionalReturnValueParses expressionParses input (some value) output

/-- Prioritized optional `: Type` annotation on a Core `let`. -/
inductive OptionalLetTypeParses :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OptionalLetTypeParses input none input
  | present {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output) :
      OptionalLetTypeParses input (some type) output

/-- Prioritized optional `= Expr` initializer on a Core `let`. -/
inductive OptionalLetInitializerParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option Syntax.Expr → Remainder → Prop where
  | absent {input : Remainder}
      (equalAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .equal)) :
      OptionalLetInitializerParses expressionParses input none input
  | present {input afterEqual output : Remainder} {value : Syntax.Expr}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (valueParsed : expressionParses afterEqual value output) :
      OptionalLetInitializerParses expressionParses input (some value) output

/-- Exact semicolon-terminated Core `let` statement grammar. -/
inductive LetStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterName afterType afterInitializer output :
        Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerParses expressionParses
        afterType initializer afterInitializer)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer semicolonSpan output) :
      LetStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .letDecl name type initializer
      } output

/-- Exact semicolon-terminated Core `return` statement grammar. -/
inductive ReturnStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterValue output : Remainder}
      {value : Option Syntax.Expr} (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (valueParsed : OptionalReturnValueParses expressionParses afterMarker
        value afterValue)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterValue
        semicolonSpan output) :
      ReturnStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt value
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssignmentStatementGrammar
/-!
Parser-independent grammar for Core assignment and expression statements.

The grammar retains the parser's `~=` priority, maximal optional assignment
tail, optional semicolon, exact source spans, and the diagnostic-free rule that
every assignment has a semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Parser-independent payload of an assignment suffix. -/
inductive CoreAssignmentTail where
  | value (operator : Located ValueAssignOp) (right : Expr)
  | bitNot (operator : SourceSpan)
  deriving Repr, BEq

/-- Exact tokens of one value-assignment operator: one token, or the two
adjacent tokens of `<<=` and `>>=`, as `ValueAssignOp.at?` decodes them. -/
def ValueAssignOperatorParses (input : Remainder)
    (operator : Located ValueAssignOp) (output : Remainder) : Prop :=
  ValueAssignOp.at? input.tokens input.endIndex input.cursor = some operator ∧
    output = { input with cursor := input.cursor + operator.value.tokenCount }

/-- No value-assignment operator occurs at the current cursor. -/
def ValueAssignOperatorAbsentAt (input : Remainder) : Prop :=
  ValueAssignOp.at? input.tokens input.endIndex input.cursor = none

namespace ValueAssignOperatorParses

/-- The decoded operator fixes its span, its value and the remainder. -/
theorem unique {input leftOutput rightOutput : Remainder}
    {left right : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input left leftOutput)
    (rightParsed : ValueAssignOperatorParses input right rightOutput) :
    left = right ∧ leftOutput = rightOutput := by
  have same : left = right := Option.some.inj (leftParsed.1.symm.trans rightParsed.1)
  subst same
  exact ⟨rfl, leftParsed.2.trans rightParsed.2.symm⟩

/-- A decoded operator excludes absence. -/
theorem not_absent {input output : Remainder} {operator : Located ValueAssignOp}
    (parsed : ValueAssignOperatorParses input operator output)
    (absent : ValueAssignOperatorAbsentAt input) : False := by
  unfold ValueAssignOperatorAbsentAt at absent
  rw [parsed.1] at absent
  contradiction

end ValueAssignOperatorParses

/-- Neither assignment-tail form starts at the current cursor. -/
def AssignmentTailAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .tildeEqual) ∧
    ValueAssignOperatorAbsentAt input

/-- Exact prioritized grammar for one assignment suffix. -/
inductive AssignmentTailParses
    (expressionParses : Remainder → Expr → Remainder → Prop) :
    Remainder → CoreAssignmentTail → Remainder → Prop where
  | bitNot {input output : Remainder} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .tildeEqual) input
        operatorSpan output) :
      AssignmentTailParses expressionParses input (.bitNot operatorSpan)
        output
  | value {input afterOperator output : Remainder}
      {operator : Located ValueAssignOp} {right : Expr}
      (tildeEqualAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .tildeEqual))
      (operatorParsed : ValueAssignOperatorParses input operator afterOperator)
      (rightParsed : expressionParses afterOperator right output) :
      AssignmentTailParses expressionParses input (.value operator right)
        output

/-- Maximal optional assignment suffix. -/
inductive OptionalAssignmentTailParses
    (expressionParses : Remainder → Expr → Remainder → Prop) :
    Remainder → Option CoreAssignmentTail → Remainder → Prop where
  | absent {input : Remainder} (tailAbsent : AssignmentTailAbsentAt input) :
      OptionalAssignmentTailParses expressionParses input none input
  | present {input output : Remainder} {tail : CoreAssignmentTail}
      (tailParsed : AssignmentTailParses expressionParses input tail output) :
      OptionalAssignmentTailParses expressionParses input (some tail) output

/-- Pure final span of one assignment suffix. -/
def assignmentEnd : CoreAssignmentTail → SourceSpan
  | .value _ right => right.span
  | .bitNot operator => operator

/-- Pure final span selected before constructing the covering statement span. -/
def statementEnd (left : Expr) (tail : Option CoreAssignmentTail)
    (semicolon : Option SourceSpan) : SourceSpan :=
  match semicolon, tail with
  | some marker, _ => marker
  | none, some value => assignmentEnd value
  | none, none => left.span

/--
Diagnostic-free construction of the statement payload.  Assignment cases
intentionally require `some semicolon`; the executable missing-semicolon
success emits a diagnostic and therefore has no constructor here.
-/
inductive AssignmentOrExpressionBuilds :
    Expr → Option CoreAssignmentTail → Option SourceSpan → Statement → Prop
    where
  | expression (left : Expr) (semicolon : Option SourceSpan) :
      AssignmentOrExpressionBuilds left none semicolon {
        span := SourceSpan.cover left.span (statementEnd left none semicolon)
        value := .expression left semicolon.isSome
      }
  | value (left right : Expr) (operator : Located ValueAssignOp)
      (semicolon : SourceSpan) :
      AssignmentOrExpressionBuilds left (some (.value operator right))
        (some semicolon) {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.value operator right)) (some semicolon))
          value := .assignValue left operator right
        }
  | bitNot (left : Expr) (operator semicolon : SourceSpan) :
      AssignmentOrExpressionBuilds left (some (.bitNot operator))
        (some semicolon) {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.bitNot operator)) (some semicolon))
          value := .assignBitNot left operator
        }

/-- Exact diagnostic-free Core assignment-or-expression statement grammar. -/
def AssignmentOrExpressionStatementParses
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (input : Remainder) (statement : Statement) (output : Remainder) : Prop :=
  ∃ left afterLeft tail afterTail semicolon,
    expressionParses input left afterLeft ∧
      OptionalAssignmentTailParses expressionParses afterLeft tail afterTail ∧
      OptionalStatementSemicolonParses afterTail semicolon output ∧
      AssignmentOrExpressionBuilds left tail semicolon statement

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeGrammar
/-!
Parser-independent ordinary outcomes for a Core assignment-or-expression
statement.  Ordinary success includes the executable parser's diagnosed
missing-semicolon assignment cases; the existing clean grammar remains the
diagnostic-free subset.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Statement construction after all ordinary suffix stages have succeeded.
Unlike the clean builder, assignment cases also allow an absent semicolon. -/
inductive AssignmentOrExpressionOrdinaryBuilds :
    Syntax.Expr → Option CoreAssignmentTail → Option SourceSpan →
      Syntax.Statement → Prop where
  | expression (left : Syntax.Expr) (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left none semicolon {
        span := SourceSpan.cover left.span (statementEnd left none semicolon)
        value := .expression left semicolon.isSome
      }
  | value (left right : Syntax.Expr) (operator : Located ValueAssignOp)
      (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left
        (some (.value operator right)) semicolon {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.value operator right)) semicolon)
          value := .assignValue left operator right
        }
  | bitNot (left : Syntax.Expr) (operator : SourceSpan)
      (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left (some (.bitNot operator))
        semicolon {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.bitNot operator)) semicolon)
          value := .assignBitNot left operator
        }

/-- Exact ordinary success of the Core assignment/expression fallback. -/
def AssignmentOrExpressionStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (statement : Syntax.Statement)
    (output : Remainder) : Prop :=
  ∃ left afterLeft tail afterTail semicolon,
    expressionOrdinary input left afterLeft ∧
      OptionalAssignmentTailParses expressionOrdinary afterLeft tail
        afterTail ∧
      OptionalStatementSemicolonParses afterTail semicolon output ∧
      AssignmentOrExpressionOrdinaryBuilds left tail semicolon statement

/-- Exact rejection trace of the Core assignment/expression fallback.
Only the initial expression and a committed value-assignment right operand
can reject; `~=` and both optional suffixes otherwise complete immediately. -/
inductive AssignmentOrExpressionStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | leftRejected {input rejected : Remainder}
      (leftRejected : expressionRejects input rejected) :
      AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects input rejected
  | rightRejected
      {input afterLeft afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located ValueAssignOp}
      (leftParsed : expressionOrdinary input left afterLeft)
      (tildeEqualAbsent : TokenKindAbsentAt afterLeft.tokens
        afterLeft.endIndex afterLeft.cursor (.symbol .tildeEqual))
      (operatorParsed : ValueAssignOperatorParses afterLeft operator
        afterOperator)
      (rightRejected : expressionRejects afterOperator rejected) :
      AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementGrammar
/-!
Parser-independent grammar for Core `for` header items, item lists, and the
complete statement.

The grammar records the language priorities at each decision: `let` before an
expression item, the stop symbol before the first item, and comma before a tail
stop.  In particular, there is no derivation for a comma immediately followed
by the stop symbol.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Final source span of a Core `for`-header `let` item. -/
def forLetEnd (name : Syntax.Identifier) (type : Option Syntax.TypeExpr)
    (initializer : Option Syntax.Expr) : SourceSpan :=
  initializer.map (fun value => value.span) |>.getD
    (type.map (fun value => value.span) |>.getD name.span)

/-- Exact grammar of one `let` item in a Core `for` header. -/
inductive ForLetItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.ForItem → Remainder → Prop where
  | parsed {input afterMarker afterName afterType output : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerParses expressionParses
        afterType initializer output) :
      ForLetItemParses expressionParses input {
        span := SourceSpan.cover markerSpan (forLetEnd name type initializer)
        value := .letDecl name type initializer
      } output

/-- Pure construction of a non-`let` Core `for` item. -/
inductive ForAssignmentOrExpressionBuilds :
    Syntax.Expr → Option CoreAssignmentTail → Syntax.ForItem → Prop where
  | expression (left : Syntax.Expr) :
      ForAssignmentOrExpressionBuilds left none {
        span := left.span
        value := .expression left
      }
  | value (left right : Syntax.Expr) (operator : Located ValueAssignOp) :
      ForAssignmentOrExpressionBuilds left (some (.value operator right)) {
        span := SourceSpan.cover left.span right.span
        value := .assignValue left operator right
      }
  | bitNot (left : Syntax.Expr) (operator : SourceSpan) :
      ForAssignmentOrExpressionBuilds left (some (.bitNot operator)) {
        span := SourceSpan.cover left.span operator
        value := .assignBitNot left operator
      }

/-- Exact maximal assignment-or-expression item grammar. -/
def ForAssignmentOrExpressionParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (item : Syntax.ForItem) (output : Remainder) : Prop :=
  ∃ left afterLeft tail,
    expressionParses input left afterLeft ∧
      OptionalAssignmentTailParses expressionParses afterLeft tail output ∧
      ForAssignmentOrExpressionBuilds left tail item

/-- Prioritized public Core `for` item grammar. -/
inductive ForItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.ForItem → Remainder → Prop where
  | letItem {input output : Remainder} {item : Syntax.ForItem}
      (parsed : ForLetItemParses expressionParses input item output) :
      ForItemParses expressionParses input item output
  | assignmentOrExpression {input output : Remainder}
      {item : Syntax.ForItem}
      (letAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw))
      (parsed : ForAssignmentOrExpressionParses expressionParses input item
        output) :
      ForItemParses expressionParses input item output

/-!
`ForItemsTailParses` describes the remaining forward suffix independently of
any accumulator representation.
-/
inductive ForItemsTailParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (stop : Symbol) : Remainder → List Syntax.ForItem → Remainder → Prop where
  | done {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma)) :
      ForItemsTailParses expressionParses stop input [] input
  | next {input afterComma afterItem output : Remainder}
      {item : Syntax.ForItem} {items : List Syntax.ForItem}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemParsed : ForItemParses expressionParses afterComma item afterItem)
      (progress : afterComma.cursor < afterItem.cursor)
      (tail : ForItemsTailParses expressionParses stop afterItem items output) :
      ForItemsTailParses expressionParses stop input (item :: items) output

/-- Exact public comma-separated item-list grammar with a prioritized stop. -/
inductive ForItemsParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (stop : Symbol) : Remainder → List Syntax.ForItem → Remainder → Prop where
  | empty {input : Remainder} (stopSpan : SourceSpan)
      (stopCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := stopSpan
        value := .symbol stop
      }) :
      ForItemsParses expressionParses stop input [] input
  | nonempty {input afterFirst output : Remainder}
      {first : Syntax.ForItem} {items : List Syntax.ForItem}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstParsed : ForItemParses expressionParses input first afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tail : ForItemsTailParses expressionParses stop afterFirst items output) :
      ForItemsParses expressionParses stop input (first :: items) output

/-- Exact header, body, spans, and AST of a canonical Core `for` statement. -/
inductive ForStatementParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost afterClosing output :
        Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      {body : Syntax.Block}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsParses expressionParses .semicolon
        afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionParses afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsParses expressionParses .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyParsed : CoreBlockParses statementParses .require afterClosing body
        output) :
      ForStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan body.span
        value := .forLoop (SourceSpan.cover openingSpan closingSpan)
          initializer condition post body
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerGrammar
/-! Exact parser-independent grammar for one ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered decision points in the executable Core statement dispatcher. -/
inductive StatementLayerStage where
  | letGuard
  | returnGuard
  | matchGuard
  | forGuard
  | whileGuard
  | ifGuard
  | assemblyGuard
  | blockGuard
  | breakGuard
  | continueGuard
  | fallback

/--
Evidence that every guard before the indexed dispatcher stage is absent.
Each transition adds exactly the token-kind absence checked by the executable
lookahead chain.
-/
inductive StatementLayerPrefixAbsent (input : Remainder) :
    StatementLayerStage → Prop where
  | start : StatementLayerPrefixAbsent input .letGuard
  | afterLet
      (prior : StatementLayerPrefixAbsent input .letGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw)) :
      StatementLayerPrefixAbsent input .returnGuard
  | afterReturn
      (prior : StatementLayerPrefixAbsent input .returnGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .returnKw)) :
      StatementLayerPrefixAbsent input .matchGuard
  | afterMatch
      (prior : StatementLayerPrefixAbsent input .matchGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .matchKw)) :
      StatementLayerPrefixAbsent input .forGuard
  | afterFor
      (prior : StatementLayerPrefixAbsent input .forGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .forKw)) :
      StatementLayerPrefixAbsent input .whileGuard
  | afterWhile
      (prior : StatementLayerPrefixAbsent input .whileGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.while.spelling)) :
      StatementLayerPrefixAbsent input .ifGuard
  | afterIf
      (prior : StatementLayerPrefixAbsent input .ifGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .ifKw)) :
      StatementLayerPrefixAbsent input .assemblyGuard
  | afterAssembly
      (prior : StatementLayerPrefixAbsent input .assemblyGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .assemblyKw)) :
      StatementLayerPrefixAbsent input .blockGuard
  | afterBlock
      (prior : StatementLayerPrefixAbsent input .blockGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBrace)) :
      StatementLayerPrefixAbsent input .breakGuard
  | afterBreak
      (prior : StatementLayerPrefixAbsent input .breakGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .breakKw)) :
      StatementLayerPrefixAbsent input .continueGuard
  | afterContinue
      (prior : StatementLayerPrefixAbsent input .continueGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .continueKw)) :
      StatementLayerPrefixAbsent input .fallback

/-- Exact clean grammar for the complete prioritized statement dispatcher. -/
inductive StatementLayerParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (patternParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (yulBodyParses : Remainder → SourceSpan → List Syntax.YulStmt →
      Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | letBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .letGuard)
      (parsed : LetStatementParses expressionParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | returnBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .returnGuard)
      (parsed : ReturnStatementParses expressionParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | matchBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .matchGuard)
      (parsed : MatchStatementParses statementParses expressionParses
        patternParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | forBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .forGuard)
      (parsed : ForStatementParses statementParses expressionParses input value
        output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | whileBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .whileGuard)
      (parsed : WhileStatementParses expressionParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | ifBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .ifGuard)
      (parsed : IfStatementParses expressionParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | assemblyBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .assemblyGuard)
      (parsed : AssemblyStatementParses yulBodyParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | blockBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .blockGuard)
      (parsed : BlockStatementParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | breakBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .breakGuard)
      (parsed : TerminatedControlStatementParses .breakKw .breakStmt input
        value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | continueBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .continueGuard)
      (parsed : TerminatedControlStatementParses .continueKw .continueStmt
        input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | fallbackBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (parsed : AssignmentOrExpressionStatementParses expressionParses input
        value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeGrammar
/-! Ordinary outcomes for canonical Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev OptionalReturnValueOrdinaryParses := OptionalReturnValueParses
abbrev OptionalLetInitializerOrdinaryParses := OptionalLetInitializerParses
abbrev LetStatementOrdinaryParses := LetStatementParses
abbrev ReturnStatementOrdinaryParses := ReturnStatementParses

/-- A present optional let type rejects exactly when its type rejects. -/
inductive OptionalLetTypeRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterColon rejected : Remainder}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (rejectedType : typeRejects afterColon rejected) :
      OptionalLetTypeRejects typeRejects input rejected

/-- A present optional initializer rejects exactly when its expression
rejects. -/
inductive OptionalLetInitializerRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input afterEqual rejected : Remainder}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (rejectedExpression : expressionRejects afterEqual rejected) :
      OptionalLetInitializerRejects expressionRejects input rejected

/-- A non-semicolon return value rejects exactly through its expression. -/
inductive OptionalReturnValueRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (rejectedExpression : expressionRejects input rejected) :
      OptionalReturnValueRejects expressionRejects input rejected

/-- Exact rejection stage of one canonical Core `let` statement. -/
inductive LetStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (rejectedName : IdentifierRejects afterMarker rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | typeRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (rejectedType : OptionalLetTypeRejects typeRejects afterName rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | initializerRejected
      {input afterMarker afterName afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (rejectedInitializer : OptionalLetInitializerRejects expressionRejects
        afterType rejected) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | semicolonRejected
      {input afterMarker afterName afterType afterInitializer : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerOrdinaryParses
        expressionOrdinary afterType initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor
          (.symbol .semicolon)) :
      LetStatementRejects expressionOrdinary expressionRejects typeRejects
        input afterInitializer

/-- Exact rejection stage of one canonical Core `return` statement. -/
inductive ReturnStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .returnKw)) :
      ReturnStatementRejects expressionOrdinary expressionRejects input input
  | valueRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (rejectedValue : OptionalReturnValueRejects expressionRejects
        afterMarker rejected) :
      ReturnStatementRejects expressionOrdinary expressionRejects input
        rejected
  | semicolonRejected {input afterMarker afterValue : Remainder}
      {value : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (valueParsed : OptionalReturnValueOrdinaryParses expressionOrdinary
        afterMarker value afterValue)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens
        afterValue.endIndex afterValue.cursor (.symbol .semicolon)) :
      ReturnStatementRejects expressionOrdinary expressionRejects input
        afterValue

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemOutcomeGrammar
/-!
Diagnostic-inclusive ordinary success and exact rejection for one Core
`for`-header item.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev ForLetItemOrdinaryParses := ForLetItemParses

/-- Exact first rejection stage of a Core `for`-header `let` item. -/
inductive ForLetItemRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | typeRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeRejected : OptionalLetTypeRejects typeRejects afterName rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | initializerRejected
      {input afterMarker afterName afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerRejected : OptionalLetInitializerRejects expressionRejects
        afterType rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected

abbrev ForAssignmentOrExpressionOrdinaryParses :=
  ForAssignmentOrExpressionParses

/-- The fallback item has the same two rejection stages as the terminal
assignment/expression parser before its optional semicolon stage. -/
abbrev ForAssignmentOrExpressionRejects :=
  AssignmentOrExpressionStatementRejects

abbrev ForItemOrdinaryParses := ForItemParses

/-- Exact rejection of the let-prioritized public Core `for` item. -/
inductive ForItemRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | letItem {input rejected : Remainder} {markerSpan : SourceSpan}
      (markerCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .keyword .letKw
      })
      (itemRejected : ForLetItemRejects expressionOrdinary expressionRejects
        typeRejects input rejected) :
      ForItemRejects expressionOrdinary expressionRejects typeRejects input
        rejected
  | assignmentOrExpression {input rejected : Remainder}
      (letAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw))
      (itemRejected : ForAssignmentOrExpressionRejects expressionOrdinary
        expressionRejects input rejected) :
      ForItemRejects expressionOrdinary expressionRejects typeRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemsOutcomeGrammar
/-!
Diagnostic-inclusive ordinary success and exact rejection for Core `for`
header item lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary forward suffix after an already parsed Core `for` item. -/
abbrev ForItemsTailOrdinaryParses := ForItemsTailParses

/-- Exact rejection of the comma-led tail, including the committed comma
immediately followed by the enclosing stop symbol. -/
inductive ForItemsTailRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (stop : Symbol) : Remainder → Remainder → Prop where
  | stopAfterComma {input afterComma : Remainder}
      (commaSpan stopSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopCurrent : TokenAt afterComma.tokens afterComma.endIndex
        afterComma.cursor { span := stopSpan, value := .symbol stop }) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        afterComma
  | itemRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemRejected : ForItemRejects expressionOrdinary expressionRejects
        TypeExprRejects afterComma rejected) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.ForItem} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemParsed : ForItemOrdinaryParses expressionOrdinary afterComma item
        afterItem)
      (progress : afterComma.cursor < afterItem.cursor)
      (tailRejected : ForItemsTailRejects expressionOrdinary expressionRejects
        stop afterItem rejected) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        rejected

/-- Ordinary public Core `for` header item list. -/
abbrev ForItemsOrdinaryParses := ForItemsParses

/-- Exact rejection of the public stop-prioritized item list. -/
inductive ForItemsRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (stop : Symbol) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstRejected : ForItemRejects expressionOrdinary expressionRejects
        TypeExprRejects input rejected) :
      ForItemsRejects expressionOrdinary expressionRejects stop input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.ForItem}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstParsed : ForItemOrdinaryParses expressionOrdinary input first
        afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tailRejected : ForItemsTailRejects expressionOrdinary expressionRejects
        stop afterFirst rejected) :
      ForItemsRejects expressionOrdinary expressionRejects stop input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementOutcomeGrammar
/-! Diagnostic-inclusive ordinary success and exact rejection for Core `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Complete ordinary Core `for` success, including diagnosed recursive body
outcomes. -/
inductive ForStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterInitializer
      afterFirstSemicolon afterCondition afterSecondSemicolon afterPost
      afterClosing output : Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      {body : Syntax.Block}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterClosing body output) :
      ForStatementOrdinaryParses statementOrdinary expressionOrdinary input {
        span := SourceSpan.cover markerSpan body.span
        value := .forLoop (SourceSpan.cover openingSpan closingSpan)
          initializer condition post body
      } output

/-- Exact first rejected stage of a complete Core `for` statement. -/
inductive ForStatementRejects
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .forKw)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input input
  | openingMissing {input afterMarker : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterMarker
  | initializerRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerRejected : ForItemsRejects expressionOrdinary
        expressionRejects .semicolon afterOpening rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | firstSemicolonMissing
      {input afterMarker afterOpening afterInitializer : Remainder}
      {initializer : List Syntax.ForItem} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor
          (.symbol .semicolon)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterInitializer
  | conditionRejected
      {input afterMarker afterOpening afterInitializer afterSemicolon
        rejected : Remainder}
      {initializer : List Syntax.ForItem}
      (markerSpan openingSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer semicolonSpan afterSemicolon)
      (conditionRejected : expressionRejects afterSemicolon rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | secondSemicolonMissing
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition : Remainder}
      {initializer : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (semicolonAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .semicolon)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterCondition
  | postRejected
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon rejected : Remainder}
      {initializer : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan :
        SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postRejected : ForItemsRejects expressionOrdinary expressionRejects
        .rightParen afterSecondSemicolon rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost : Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan :
        SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingAbsent : TokenKindAbsentAt afterPost.tokens afterPost.endIndex
        afterPost.cursor (.symbol .rightParen)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterPost
  | bodyRejected
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost afterClosing rejected :
        Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeGrammar
/-! Ordinary success and exact rejection for Core `assembly`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive Core assembly success with the concrete public Yul
body relation. -/
abbrev AssemblyStatementOrdinaryParses :=
  AssemblyStatementParses YulBodyOrdinaryParses

/-- Exact first rejection stage of one Core assembly wrapper. -/
inductive AssemblyStatementRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .assemblyKw)) :
      AssemblyStatementRejects input input
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .assemblyKw) input markerSpan
        afterMarker)
      (bodyRejected : YulBodyRejects afterMarker rejected) :
      AssemblyStatementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end
