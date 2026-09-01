import Solcore.Syntax.DeclarativeCoreBlockGrammar
import Solcore.Syntax.DeclarativeCorePatternGrammar

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
