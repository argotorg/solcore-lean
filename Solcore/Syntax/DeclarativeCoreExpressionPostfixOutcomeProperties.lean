import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties

/-!
Exclusivity and deterministic outcomes for ordinary Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Exact postfix-tail rejection excludes ordinary postfix-tail success. -/
theorem PostfixTailRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder} {base : Syntax.Expr}
    (rejection : PostfixTailRejects nestedOrdinary nestedRejects input base
      rejected) :
    ¬ ∃ successfulBase expression output,
      PostfixTailParses nestedOrdinary input successfulBase expression
        output := by
  induction rejection with
  | indexNestedRejected openingSpan openingToken nestedRejected =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.1 openingToken.1
      | index successfulOpeningSpan closingSpan successfulOpening
            indexParsed closingToken tail =>
          have afterOpeningEq := exactToken_output_unique openingToken
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint nestedRejected
            ⟨_, _, indexParsed⟩
      | call indexAbsent argumentsParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
  | indexClosingMissing openingSpan openingToken indexParsed closingAbsent =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.1 openingToken.1
      | index successfulOpeningSpan closingSpan successfulOpening
            successfulIndex closingToken tail =>
          have afterOpeningEq := exactToken_output_unique openingToken
            successfulOpening
          subst afterOpeningEq
          have afterIndexEq := nestedOutcomes.successOutputUnique indexParsed
            successfulIndex
          subst afterIndexEq
          exact absent_conflicts_token closingAbsent closingToken.1
      | call indexAbsent argumentsParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
  | indexLaterRejected openingSpan closingSpan openingToken indexParsed
        closingToken tailRejected inductionHypothesis =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.1 openingToken.1
      | index successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulIndex successfulClosing successfulTail =>
          have afterOpeningEq := exactToken_output_unique openingToken
            successfulOpening
          subst afterOpeningEq
          have afterIndexEq := nestedOutcomes.successOutputUnique indexParsed
            successfulIndex
          subst afterIndexEq
          have afterClosingEq := exactToken_output_unique closingToken
            successfulClosing
          subst afterClosingEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩
      | call indexAbsent argumentsParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
  | callArgumentsRejected openingSpan indexAbsent openingToken
        argumentsRejected =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.2.1 openingToken
      | index indexOpeningSpan closingSpan indexOpening indexParsed
            closingToken tail =>
          exact absent_conflicts_token indexAbsent indexOpening.1
      | call successfulIndexAbsent argumentsParsed tail =>
          exact argumentsRejected.disjointAllowEmptyNoTrailing nestedOutcomes
            ⟨_, _, argumentsParsed⟩
      | field dotSpan successfulIndexAbsent callAbsent dotToken nameParsed
            tail =>
          exact absent_conflicts_token callAbsent openingToken
  | callLaterRejected indexAbsent argumentsParsed tailRejected
        inductionHypothesis =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact absent_conflicts_token absent.2.1 openingToken
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | call successfulIndexAbsent successfulArguments successfulTail =>
          have afterArgumentsEq :=
            NoTrailingDelimitedListParses.output_unique
              (opening := .leftParen) (closing := .rightParen)
              (elementParses := nestedOrdinary)
              nestedOutcomes.successOutputUnique argumentsParsed
                successfulArguments
          subst afterArgumentsEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩
      | field dotSpan successfulIndexAbsent callAbsent dotToken nameParsed
            tail =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact absent_conflicts_token callAbsent openingToken
  | fieldNameRejected dotSpan indexAbsent callAbsent dotToken nameRejected =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.2.2 dotToken.1
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | call successfulIndexAbsent argumentsParsed tail =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact absent_conflicts_token callAbsent openingToken
      | field successfulDotSpan successfulIndexAbsent successfulCallAbsent
            successfulDot nameParsed tail =>
          have afterDotEq := exactToken_output_unique dotToken successfulDot
          subst afterDotEq
          exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | fieldLaterRejected dotSpan indexAbsent callAbsent dotToken nameParsed
        tailRejected inductionHypothesis =>
      rintro ⟨successfulBase, expression, output, successful⟩
      cases successful with
      | done absent =>
          exact absent_conflicts_token absent.2.2 dotToken.1
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact absent_conflicts_token indexAbsent openingToken.1
      | call successfulIndexAbsent argumentsParsed tail =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact absent_conflicts_token callAbsent openingToken
      | field successfulDotSpan successfulIndexAbsent successfulCallAbsent
            successfulDot successfulName successfulTail =>
          have afterDotEq := exactToken_output_unique dotToken successfulDot
          subst afterDotEq
          have afterNameEq := nameParsed.output_unique successfulName
          subst afterNameEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Complete postfix rejection excludes complete ordinary postfix success. -/
theorem ExpressionPostfixRejects.disjointOrdinary
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : DeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary input
        expression output := by
  rintro ⟨expression, output, successful⟩
  rcases successful with ⟨successfulBase, successfulAfterAtom,
    successfulAtom, successfulTail⟩
  cases rejection with
  | atomRejected rejectedAtom =>
      exact atomOutcomes.successRejectDisjoint rejectedAtom
        ⟨successfulBase, successfulAfterAtom, successfulAtom⟩
  | tailRejected rejectedAtom rejectedTail =>
      have afterAtomEq := atomOutcomes.successOutputUnique rejectedAtom
        successfulAtom
      subst afterAtomEq
      exact rejectedTail.disjointOrdinary nestedOutcomes
        ⟨successfulBase, expression, output, successfulTail⟩

/-- Complete ordinary postfix outcomes are deterministic and exclusive. -/
theorem expressionPostfixDeterministicOutcomeSpec
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : DeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary)
      (ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects) where
  successOutputUnique :=
    ExpressionPostfixOrdinaryParses.output_unique atomOutcomes nestedOutcomes
  successRejectDisjoint :=
    ExpressionPostfixRejects.disjointOrdinary atomOutcomes nestedOutcomes

/-- Clean atom and nested relations embed into ordinary postfix success. -/
theorem ExpressionPostfixParses.toOrdinary
    {atomClean atomOrdinary nestedClean nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (atomToOrdinary : ∀ {input expression output},
      atomClean input expression output →
        atomOrdinary input expression output)
    (nestedToOrdinary : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionPostfixParses atomClean nestedClean input expression
      output) :
    ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary input
      expression output := by
  rcases parsed with ⟨base, afterAtom, atomParsed, tailParsed⟩
  exact ⟨base, afterAtom, atomToOrdinary atomParsed,
    tailParsed.mapNestedRelation nestedToOrdinary⟩

end Solcore.Syntax.DeclarativeGrammar
