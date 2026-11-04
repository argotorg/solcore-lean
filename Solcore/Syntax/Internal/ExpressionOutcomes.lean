import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Properties of the declarative grammar of operators, parenthesized forms, postfix tails and
atom recovery: outcomes are deterministic, and successful values and rejection points are
unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
/-!
Functionality and relation embeddings for ordinary Core postfix successes.
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

/-- Every allow-empty no-trailing list success exposes its opening token. -/
theorem NoTrailingDelimitedListParses.opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- A maximal ordinary postfix tail has a unique output remainder. -/
theorem PostfixTailParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {leftBase rightBase left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input leftBase left
      afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input rightBase right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBase right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftAbsent.1 openingToken.1)
      | call indexAbsent argumentsParsed tail =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token leftAbsent.2.1 openingToken)
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim
            (absent_conflicts_token leftAbsent.2.2 dotToken.1)
  | index leftOpeningSpan leftClosingSpan leftOpening leftIndex leftClosing
        leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent.1 leftOpening.1)
      | index rightOpeningSpan rightClosingSpan rightOpening rightIndex
            rightClosing rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterIndexEq := nestedOutcomes.successOutputUnique leftIndex
            rightIndex
          subst afterIndexEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          exact inductionHypothesis rightTail
      | call rightIndexAbsent argumentsParsed tail =>
          exact False.elim
            (absent_conflicts_token rightIndexAbsent leftOpening.1)
      | field dotSpan rightIndexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim
            (absent_conflicts_token rightIndexAbsent leftOpening.1)
  | call leftIndexAbsent leftArguments leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          rcases leftArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token rightAbsent.2.1 openingToken)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftIndexAbsent rightOpening.1)
      | call rightIndexAbsent rightArguments rightTail =>
          have afterArgumentsEq :=
            NoTrailingDelimitedListParses.output_unique
              (opening := .leftParen) (closing := .rightParen)
              (elementParses := nestedOrdinary)
              nestedOutcomes.successOutputUnique leftArguments rightArguments
          subst afterArgumentsEq
          exact inductionHypothesis rightTail
      | field dotSpan rightIndexAbsent rightCallAbsent dotToken nameParsed
            tail =>
          rcases leftArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token rightCallAbsent openingToken)
  | field leftDotSpan leftIndexAbsent leftCallAbsent leftDot leftName leftTail
        inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent.2.2 leftDot.1)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftIndexAbsent rightOpening.1)
      | call rightIndexAbsent rightArguments tail =>
          rcases rightArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token leftCallAbsent openingToken)
      | field rightDotSpan rightIndexAbsent rightCallAbsent rightDot rightName
            rightTail =>
          have afterDotEq := exactToken_output_unique leftDot rightDot
          subst afterDotEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact inductionHypothesis rightTail

/-- Complete ordinary postfix success has a unique output remainder. -/
theorem ExpressionPostfixOrdinaryParses.output_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : DeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterAtom, leftAtom, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterAtom, rightAtom, rightTail⟩
  have afterAtomEq := atomOutcomes.successOutputUnique leftAtom rightAtom
  subst afterAtomEq
  exact leftTail.output_unique nestedOutcomes rightTail

/-- Pointwise nested inclusion lifts through every postfix suffix. -/
theorem PostfixTailParses.mapNestedRelation
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (includeNested : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder} {base expression : Syntax.Expr}
    (parsed : PostfixTailParses source input base expression output) :
    PostfixTailParses target input base expression output := by
  induction parsed with
  | done absent => exact .done absent
  | index openingSpan closingSpan openingToken indexParsed closingToken tail
        inductionHypothesis =>
      exact .index openingSpan closingSpan openingToken
        (includeNested indexParsed) closingToken inductionHypothesis
  | call indexAbsent argumentsParsed tail inductionHypothesis =>
      exact .call indexAbsent
        (argumentsParsed.mapElementRelation includeNested) inductionHypothesis
  | field dotSpan indexAbsent callAbsent dotToken nameParsed tail
        inductionHypothesis =>
      exact .field dotSpan indexAbsent callAbsent dotToken nameParsed
        inductionHypothesis

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeProperties
/-!
Exclusivity and deterministic outcomes for ordinary Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeProperties
/-! Deterministic ordinary outcomes for one Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every ordinary expression name consumes exactly its current token. -/
theorem ExpressionNameOrdinaryParses.output_eq
    {input output : Remainder} {name : Syntax.Identifier}
    (parsed : ExpressionNameOrdinaryParses input name output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | boolean parsed => cases parsed <;> rfl
  | identifier trueAbsent falseAbsent parsed =>
      rcases parsed with ⟨token, tokensEq, endIndexEq, cursorEq⟩
      cases input
      cases output
      simp_all

/-- Ordinary expression-name output is functional. -/
theorem ExpressionNameOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact name rejection excludes every ordinary expression-name success. -/
theorem ExpressionNameRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ExpressionNameRejects input rejected) :
    ¬ ∃ name output,
      ExpressionNameOrdinaryParses input name output := by
  rintro ⟨name, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | boolean parsed =>
          cases parsed with
          | trueKeyword token =>
              exact absent_conflicts_token absent.1 token
          | falseKeyword token =>
              exact absent_conflicts_token absent.2.1 token
      | identifier trueAbsent falseAbsent parsed =>
          exact absent.2.2 ⟨name.span, name.value, parsed.1⟩

/-- Boolean-first expression names form a deterministic ordinary outcome. -/
theorem expressionNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExpressionNameOrdinaryParses
      ExpressionNameRejects where
  successOutputUnique := ExpressionNameOrdinaryParses.output_unique
  successRejectDisjoint := ExpressionNameRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeProperties
/-! Deterministic ordinary outcomes for a guarded leading-dot constructor. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem noTrailing_opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- Optional leading-dot arguments have a unique ordinary output. -/
theorem OptionalDotConstructorArgumentsOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Expr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input left afterLeft)
    (rightParsed : OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightArguments =>
          rcases noTrailing_opening_present rightArguments with
            ⟨span, openingToken⟩
          exact False.elim (absent_conflicts_token leftAbsent openingToken)
  | present leftArguments =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases noTrailing_opening_present leftArguments with
            ⟨span, openingToken⟩
          exact False.elim (absent_conflicts_token rightAbsent openingToken)
      | present rightArguments =>
          exact NoTrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftArguments rightArguments

/-- Present optional-argument rejection excludes both the absent and present
ordinary branches. -/
theorem OptionalDotConstructorArgumentsRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : OptionalDotConstructorArgumentsRejects nestedOrdinary
      nestedRejects input rejected) :
    ¬ ∃ arguments output,
      OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary input
        arguments output := by
  rintro ⟨arguments, output, successful⟩
  cases rejection with
  | present openingSpan openingToken argumentsRejected =>
      cases successful with
      | absent openingAbsent =>
          exact absent_conflicts_token openingAbsent openingToken
      | present argumentsParsed =>
          exact argumentsRejected.disjointAllowEmptyNoTrailing nestedOutcomes
            ⟨_, _, argumentsParsed⟩

/-- Optional leading-dot arguments form a deterministic ordinary outcome. -/
theorem optionalDotConstructorArgumentsDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary)
      (OptionalDotConstructorArgumentsRejects nestedOrdinary nestedRejects)
      where
  successOutputUnique :=
    OptionalDotConstructorArgumentsOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    OptionalDotConstructorArgumentsRejects.disjointOrdinary nestedOutcomes

/-- Pointwise nested inclusion lifts through optional leading-dot
arguments. -/
theorem OptionalDotConstructorArgumentsParses.mapNestedRelation
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (includeNested : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder}
    {arguments : Option (DelimitedList Syntax.Expr)}
    (parsed : OptionalDotConstructorArgumentsParses source input arguments
      output) :
    OptionalDotConstructorArgumentsOrdinaryParses target input arguments
      output := by
  cases parsed with
  | absent openingAbsent => exact .absent openingAbsent
  | present argumentsParsed =>
      exact .present (argumentsParsed.mapElementRelation includeNested)

/-- Ordinary leading-dot construction has the unique output selected by its
name and optional arguments. -/
theorem DotConstructorOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDotSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightDotSpan rightDot rightName rightArguments =>
          have afterDotEq := exactToken_output_unique leftDot rightDot
          subst afterDotEq
          have afterNameEq :=
            ExpressionNameOrdinaryParses.output_unique leftName rightName
          subst afterNameEq
          exact OptionalDotConstructorArgumentsOrdinaryParses.output_unique
            nestedOutcomes leftArguments rightArguments

/-- Rejection at the name or argument stage excludes every ordinary
leading-dot constructor success. -/
theorem DotConstructorRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : DotConstructorRejects nestedOrdinary nestedRejects input
      rejected) :
    ¬ ∃ expression output,
      DotConstructorOrdinaryParses nestedOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | nameRejected rejectedDotSpan rejectedDot rejectedName =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName arguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          subst afterDotEq
          exact rejectedName.disjointOrdinary
            ⟨_, _, successfulName⟩
  | argumentsRejected rejectedDotSpan rejectedDot rejectedName
        rejectedArguments =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName
            successfulArguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          subst afterDotEq
          have afterNameEq := ExpressionNameOrdinaryParses.output_unique
            rejectedName successfulName
          subst afterNameEq
          exact rejectedArguments.disjointOrdinary nestedOutcomes
            ⟨_, _, successfulArguments⟩

/-- Guarded leading-dot constructor outcomes are deterministic whenever the
nested expression outcome is. -/
theorem dotConstructorDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec (DotConstructorOrdinaryParses nestedOrdinary)
      (DotConstructorRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    DotConstructorOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    DotConstructorRejects.disjointOrdinary nestedOutcomes

/-- The existing clean leading-dot grammar embeds through any supplied
clean-to-ordinary nested-expression bridge. -/
theorem DotConstructorParses.toOrdinary
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (nestedToOrdinary : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : DotConstructorParses source input expression output) :
    DotConstructorOrdinaryParses target input expression output := by
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argumentsParsed =>
      exact .parsed dotSpan dotParsed nameParsed
        (argumentsParsed.mapNestedRelation nestedToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeProperties
/-! Deterministic ordinary outcomes for a Core identifier expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Identifier-expression output is the unique output of its name. -/
theorem IdentifierExpressionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierExpressionOrdinaryParses input left afterLeft)
    (rightParsed : IdentifierExpressionOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          exact ExpressionNameOrdinaryParses.output_unique leftName rightName

/-- Rejected expression names exclude identifier-expression success. -/
theorem IdentifierExpressionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : IdentifierExpressionRejects input rejected) :
    ¬ ∃ expression output,
      IdentifierExpressionOrdinaryParses input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | nameRejected nameRejected =>
      cases successful with
      | parsed nameParsed =>
          exact nameRejected.disjointOrdinary ⟨_, _, nameParsed⟩

/-- Identifier-expression leaves have deterministic ordinary outcomes. -/
theorem identifierExpressionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec IdentifierExpressionOrdinaryParses
      IdentifierExpressionRejects where
  successOutputUnique := IdentifierExpressionOrdinaryParses.output_unique
  successRejectDisjoint := IdentifierExpressionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLiteralOutcomeProperties
/-! Deterministic ordinary outcomes for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every ordinary Core literal consumes exactly its current token. -/
theorem CoreLiteralOrdinaryParses.output_eq
    {input output : Remainder} {literal : Syntax.CoreLiteral}
    (parsed : CoreLiteralOrdinaryParses input literal output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed <;> rfl

/-- Ordinary Core-literal output is functional. -/
theorem CoreLiteralOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.CoreLiteral}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralOrdinaryParses input left afterLeft)
    (rightParsed : CoreLiteralOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact literal rejection excludes every ordinary literal success. -/
theorem CoreLiteralRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : CoreLiteralRejects input rejected) :
    ¬ ∃ literal output, CoreLiteralOrdinaryParses input literal output := by
  rintro ⟨literal, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | decimal token => exact absent.1 ⟨_, _, token⟩
      | hexadecimal token => exact absent.2.1 ⟨_, _, token⟩
      | string token => exact absent.2.2 ⟨_, _, token⟩

/-- Core literal primitives form deterministic ordinary outcomes. -/
theorem coreLiteralDeterministicOutcomeSpec :
    DeterministicOutcomeSpec CoreLiteralOrdinaryParses
      CoreLiteralRejects where
  successOutputUnique := CoreLiteralOrdinaryParses.output_unique
  successRejectDisjoint := CoreLiteralRejects.disjointOrdinary

/-- Every ordinary literal expression consumes exactly its literal token. -/
theorem LiteralExpressionOrdinaryParses.output_eq
    {input output : Remainder} {expression : Syntax.Expr}
  (parsed : LiteralExpressionOrdinaryParses input expression output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | parsed literalParsed => cases literalParsed <;> rfl

/-- Ordinary literal-expression output is functional. -/
theorem LiteralExpressionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralExpressionOrdinaryParses input left afterLeft)
    (rightParsed : LiteralExpressionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact literal-expression rejection excludes every ordinary success. -/
theorem LiteralExpressionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LiteralExpressionRejects input rejected) :
    ¬ ∃ expression output,
      LiteralExpressionOrdinaryParses input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | parsed literalParsed =>
          cases literalParsed with
          | decimal token => exact absent.1 ⟨_, _, token⟩
          | hexadecimal token => exact absent.2.1 ⟨_, _, token⟩
          | string token => exact absent.2.2 ⟨_, _, token⟩

/-- Literal-expression leaves form deterministic ordinary outcomes. -/
theorem literalExpressionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LiteralExpressionOrdinaryParses
      LiteralExpressionRejects where
  successOutputUnique := LiteralExpressionOrdinaryParses.output_unique
  successRejectDisjoint := LiteralExpressionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLeafExactnessProperties
/-! Exact literal, Boolean-first name, and identifier Core expression leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The current Core literal token fixes its spelling and complete source span. -/
theorem CoreLiteralParses.value_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- A Core literal fixes its exact value and complete final remainder. -/
theorem CoreLiteralParses.result_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    CoreLiteralOrdinaryParses.output_unique leftParsed rightParsed⟩

/-- Ordinary Core literal outcomes fix both values and rejecting endpoints. -/
theorem coreLiteralExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreLiteralOrdinaryParses CoreLiteralRejects where
  toDeterministicOutcomeSpec := coreLiteralDeterministicOutcomeSpec
  successValueUnique := CoreLiteralParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Wrapping a Core literal preserves its exact AST and source span. -/
theorem LiteralExpressionOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LiteralExpressionOrdinaryParses input left afterLeft)
    (rightParsed : LiteralExpressionOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          cases leftLiteral.value_unique rightLiteral
          rfl

/-- Literal-expression leaves have exact ordinary outcomes. -/
theorem literalExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LiteralExpressionOrdinaryParses LiteralExpressionRejects where
  toDeterministicOutcomeSpec := literalExpressionDeterministicOutcomeSpec
  successValueUnique := LiteralExpressionOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Boolean-keyword names have a unique exact spelling and span. -/
theorem BooleanIdentifierParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : BooleanIdentifierParses input left afterLeft)
    (rightParsed : BooleanIdentifierParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- Boolean-first name priority fixes the complete identifier value. -/
theorem ExpressionNameOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | boolean leftBoolean =>
      cases rightParsed with
      | boolean rightBoolean => exact leftBoolean.value_unique rightBoolean
      | identifier rightTrueAbsent rightFalseAbsent _ =>
          cases leftBoolean with
          | trueKeyword token => exact False.elim (rightTrueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (rightFalseAbsent ⟨_, token⟩)
  | identifier leftTrueAbsent leftFalseAbsent leftIdentifier =>
      cases rightParsed with
      | boolean rightBoolean =>
          cases rightBoolean with
          | trueKeyword token => exact False.elim (leftTrueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (leftFalseAbsent ⟨_, token⟩)
      | identifier _ _ rightIdentifier => exact leftIdentifier.value_unique rightIdentifier

/-- An ordinary expression name fixes its value and final remainder. -/
theorem ExpressionNameOrdinaryParses.result_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Boolean-first expression names have exact ordinary outcomes. -/
theorem expressionNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExpressionNameOrdinaryParses ExpressionNameRejects where
  toDeterministicOutcomeSpec := expressionNameDeterministicOutcomeSpec
  successValueUnique := ExpressionNameOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- The ordinary identifier-expression wrapper preserves its exact name and span. -/
theorem IdentifierExpressionOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierExpressionOrdinaryParses input left afterLeft)
    (rightParsed : IdentifierExpressionOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          cases ExpressionNameOrdinaryParses.value_unique leftName rightName
          rfl

/-- Identifier-expression leaves have exact ordinary outcomes. -/
theorem identifierExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec IdentifierExpressionOrdinaryParses IdentifierExpressionRejects where
  toDeterministicOutcomeSpec := identifierExpressionDeterministicOutcomeSpec
  successValueUnique := IdentifierExpressionOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected with
    | nameRejected leftName =>
        cases rightRejected with
        | nameRejected rightName =>
            exact expressionNameExactOutcomeSpec.rejectOutputUnique leftName rightName

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeProperties
/-! Deterministic ordinary outcomes for a guarded Core proxy leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary proxy success has the unique output of its nested type. -/
theorem ProxyExpressionOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ProxyExpressionOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : ProxyExpressionOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftTypeParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightTypeParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          exact typeOutcomes.successOutputUnique leftTypeParsed
            rightTypeParsed

/-- Nested type rejection excludes every ordinary proxy success. -/
theorem ProxyExpressionRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : ProxyExpressionRejects typeRejects input rejected) :
    ¬ ∃ expression output,
      ProxyExpressionOrdinaryParses typeOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | typeRejected rejectedMarkerSpan rejectedMarkerParsed rejectedType =>
      cases successful with
      | parsed successfulMarkerSpan successfulMarkerParsed successfulType =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact typeOutcomes.successRejectDisjoint rejectedType
            ⟨_, _, successfulType⟩

/-- Guarded proxy success and nested type rejection are deterministic and
exclusive whenever the supplied type outcome is. -/
theorem proxyExpressionDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (ProxyExpressionOrdinaryParses typeOrdinary)
      (ProxyExpressionRejects typeRejects) where
  successOutputUnique :=
    ProxyExpressionOrdinaryParses.output_unique typeOutcomes
  successRejectDisjoint :=
    ProxyExpressionRejects.disjointOrdinary typeOutcomes

/-- The existing clean proxy grammar embeds through any supplied clean-to-
ordinary type bridge. -/
theorem ProxyExpressionParses.toOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (typeCleanToOrdinary : ∀ {input type output},
      TypeExprParses input type output → typeOrdinary input type output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ProxyExpressionParses input expression output) :
    ProxyExpressionOrdinaryParses typeOrdinary input expression output := by
  cases parsed with
  | parsed markerSpan markerParsed typeParsed =>
      exact .parsed markerSpan markerParsed (typeCleanToOrdinary typeParsed)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomFinalRejectionProperties
/-! Exclusivity of the final Core atom dispatcher rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token_variant {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Final dispatcher rejection excludes every successful ordered Core atom
branch, independently of the supplied recursive grammars. -/
theorem ExpressionAtomCoreFinalRejects.disjointCore
    {nestedParses : Remainder → Syntax.Expr → Remainder → Prop}
    {blockParses : Remainder → Syntax.Block → Remainder → Prop}
    {input : Remainder} (rejected : ExpressionAtomCoreFinalRejects input) :
    ¬ ∃ expression output,
      ExpressionAtomCoreParses nestedParses blockParses input expression
        output := by
  rintro ⟨expression, output, parsed⟩
  cases rejected with
  | final literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
      leftBracketAbsent lambdaAbsent =>
      cases parsed with
      | literal parsed =>
          cases parsed with
          | parsed literalParsed =>
              cases literalParsed with
              | decimal token =>
                  exact literalAbsent (Or.inl ⟨_, _, token⟩)
              | hexadecimal token =>
                  exact literalAbsent (Or.inr (Or.inl ⟨_, _, token⟩))
              | string token =>
                  exact literalAbsent (Or.inr (Or.inr ⟨_, _, token⟩))
      | identifier earlierLiteralAbsent parsed =>
          cases parsed with
          | parsed nameParsed =>
              cases nameParsed with
              | boolean booleanParsed =>
                  cases booleanParsed with
                  | trueKeyword token =>
                      exact nameAbsent (Or.inl ⟨_, token⟩)
                  | falseKeyword token =>
                      exact nameAbsent (Or.inr (Or.inl ⟨_, token⟩))
              | identifier trueAbsent falseAbsent identifierParsed =>
                  exact nameAbsent
                    (Or.inr (Or.inr ⟨_, _, identifierParsed.1⟩))
      | dotConstructor earlierLiteralAbsent earlierNameAbsent parsed =>
          cases parsed with
          | parsed dotSpan dotParsed nameParsed argumentsParsed =>
              exact absent_conflicts_token_variant dotAbsent dotParsed.1
      | proxy earlierLiteralAbsent earlierNameAbsent earlierDotAbsent parsed =>
          cases parsed with
          | parsed markerSpan markerParsed typeParsed =>
              exact absent_conflicts_token_variant atAbsent markerParsed.1
      | parenthesized earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent parsed =>
          cases parsed with
          | empty openingSpan closingSpan openingParsed closingParsed =>
              exact absent_conflicts_token_variant leftParenAbsent openingParsed.1
          | group openingSpan closingSpan openingParsed nestedParsed
              elementParsed progress commaAbsent closingParsed =>
              exact absent_conflicts_token_variant leftParenAbsent openingParsed.1
          | tuple openingSpan closingSpan openingParsed closingAbsent
              firstParsed progress tail =>
              exact absent_conflicts_token_variant leftParenAbsent openingParsed.1
      | array earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent earlierLeftParenAbsent parsed =>
          cases parsed with
          | parsed valuesParsed =>
              cases valuesParsed with
              | empty openingSpan closingSpan openingToken closingToken =>
                  exact absent_conflicts_token_variant leftBracketAbsent openingToken
              | nonempty closingAbsent nonemptyParsed =>
                  rcases nonemptyParsed with
                    ⟨openingSpan, first, afterFirst, rest, closingSpan,
                      tokensEq, endIndexEq, openingToken, firstParsed,
                      progress, tail, elementsEq, spanEq⟩
                  exact absent_conflicts_token_variant leftBracketAbsent
                    openingToken
      | lambda earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent earlierLeftParenAbsent earlierLeftBracketAbsent
          parsed =>
          cases parsed with
          | parsed markerSpan markerParsed parametersParsed returnTypeParsed
              bodyParsed =>
              exact absent_conflicts_token_variant lambdaAbsent markerParsed.1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionProperties
/-! Ordered guard selection is unique and exists for every token remainder,
including missing backing or a cursor outside the numeric window. These are
selection laws, not existence claims about recursive expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem ExpressionAtomDispatchSelects.branch_unique
    {input : Remainder} {left right : ExpressionAtomDispatchBranch}
    (leftSelected : ExpressionAtomDispatchSelects input left)
    (rightSelected : ExpressionAtomDispatchSelects input right) : left = right := by
  cases leftSelected <;> cases rightSelected <;> grind only [TokenKindAbsentAt]

theorem expressionAtomDispatchSelects_exists (input : Remainder) :
    ∃ branch, ExpressionAtomDispatchSelects input branch := by
  classical
  by_cases literal : CoreLiteralStartsAt input
  · exact ⟨.literal, .literal literal⟩
  by_cases name : ExpressionNameStartsAt input
  · exact ⟨.name, .name literal name⟩
  by_cases dot : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot }
  · exact ⟨.dotConstructor, .dotConstructor literal name dot⟩
  by_cases atMarker : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at }
  · exact ⟨.proxy, .proxy literal name dot atMarker⟩
  by_cases paren : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }
  · exact ⟨.parenthesized, .parenthesized literal name dot atMarker paren⟩
  by_cases bracket : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftBracket }
  · exact ⟨.array, .array literal name dot atMarker paren bracket⟩
  by_cases lambda : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .keyword .lamKw }
  · exact ⟨.lambda, .lambda literal name dot atMarker paren bracket lambda⟩
  exact ⟨.final, .final literal name dot atMarker paren bracket lambda⟩

/-- A unique selected branch exists without a success/rejection premise. -/
theorem expressionAtomDispatchSelects_exists_unique (input : Remainder) :
    ∃ branch, ExpressionAtomDispatchSelects input branch ∧
      ∀ other, ExpressionAtomDispatchSelects input other → other = branch := by
  rcases expressionAtomDispatchSelects_exists input with ⟨branch, selected⟩
  exact ⟨branch, selected, fun _ other => other.branch_unique selected⟩

/-- Equal current-token observations suffice even when the backing arrays,
numeric windows, and cursor positions themselves differ. -/
theorem ExpressionAtomDispatchSelects.congr_of_tokenAt
    {left right : Remainder} {branch : ExpressionAtomDispatchBranch}
    (current : ∀ token, TokenAt left.tokens left.endIndex left.cursor token ↔
      TokenAt right.tokens right.endIndex right.cursor token) :
    ExpressionAtomDispatchSelects left branch ↔ ExpressionAtomDispatchSelects right branch := by
  have literals : CoreLiteralStartsAt left ↔ CoreLiteralStartsAt right := by
    simp only [CoreLiteralStartsAt, current]
  have names : ExpressionNameStartsAt left ↔ ExpressionNameStartsAt right := by
    simp only [ExpressionNameStartsAt, current]
  have absences : ∀ kind, TokenKindAbsentAt left.tokens left.endIndex left.cursor kind ↔
      TokenKindAbsentAt right.tokens right.endIndex right.cursor kind := by
    intro kind
    simp only [TokenKindAbsentAt, current]
  constructor <;> intro selected <;> cases selected <;> constructor <;>
    grind only

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionUnaryLeftOutcomeProperties
/-!
Deterministic ordinary outcomes for Core unary and left-associative expression
layers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem unaryAbsent_conflicts_parsed
    {input output : Remainder} {operator : Located UnaryOp}
    (absent : UnaryOperatorAbsentAt input)
    (parsed : UnaryOperatorParses input operator output) : False := by
  rcases operator with ⟨span, operator⟩
  cases operator with
  | logicalNot =>
      exact absent.1 ⟨span, by
        simpa [UnaryOperatorParses, UnaryOp.symbol] using parsed.1⟩
  | bitNot =>
      exact absent.2 ⟨span, by
        simpa [UnaryOperatorParses, UnaryOp.symbol] using parsed.1⟩

private theorem binaryAbsent_conflicts_parsed
    {precedence : Nat} {input output : Remainder}
    {operator : Located BinaryOp}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input)
    (parsed : BinaryOperatorAtPrecedenceParses precedence input operator
      output) : False :=
  parsed.not_absent absent

private theorem binaryOperator_output_unique
    {precedence : Nat} {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located BinaryOp}
    (leftParsed : BinaryOperatorAtPrecedenceParses precedence input
      leftOperator leftOutput)
    (rightParsed : BinaryOperatorAtPrecedenceParses precedence input
      rightOperator rightOutput) : leftOutput = rightOutput :=
  (leftParsed.unique rightParsed).2

/-- Maximal unary-prefix parsing has a unique output remainder. -/
theorem UnaryOperatorsParses.output_unique
    {input : Remainder} {left right : List (Located UnaryOp)}
    {afterLeft afterRight : Remainder}
    (leftParsed : UnaryOperatorsParses input left afterLeft)
    (rightParsed : UnaryOperatorsParses input right afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightOperator rightTail =>
          exact False.elim
            (unaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | next leftOperator leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (unaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | next rightOperator rightTail =>
          have afterOperatorEq := leftOperator.2.trans rightOperator.2.symm
          subst afterOperatorEq
          exact inductionHypothesis rightTail

/-- Ordinary unary-layer success has a unique output remainder. -/
theorem ExpressionUnaryOrdinaryParses.output_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input left
      afterLeft)
    (rightParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftOperators, leftAfterOperators, leftBase, leftOperatorsParsed,
      leftBaseParsed, leftEq⟩
  rcases rightParsed with
    ⟨rightOperators, rightAfterOperators, rightBase, rightOperatorsParsed,
      rightBaseParsed, rightEq⟩
  have operatorsEq := leftOperatorsParsed.output_unique rightOperatorsParsed
  subst operatorsEq
  exact outcomes.successOutputUnique leftBaseParsed rightBaseParsed

/-- Unary rejection excludes ordinary unary success. -/
theorem ExpressionUnaryRejects.disjointOrdinary
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input rejected : Remainder}
    (rejection : ExpressionUnaryRejects postfixRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionUnaryOrdinaryParses postfixOrdinary input expression output :=
    by
  rintro ⟨expression, output, operators, afterOperators, base,
    operatorsParsed, baseParsed, expressionEq⟩
  cases rejection with
  | postfixRejected rejectedOperators rejectedPostfix =>
      have afterOperatorsEq :=
        rejectedOperators.output_unique operatorsParsed
      subst afterOperatorsEq
      exact outcomes.successRejectDisjoint rejectedPostfix
        ⟨base, output, baseParsed⟩

/-- Construct the deterministic outcome contract for the unary layer. -/
theorem expressionUnaryDeterministicOutcomeSpec
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    DeterministicOutcomeSpec
      (ExpressionUnaryOrdinaryParses postfixOrdinary)
      (ExpressionUnaryRejects postfixRejects) where
  successOutputUnique := ExpressionUnaryOrdinaryParses.output_unique outcomes
  successRejectDisjoint := ExpressionUnaryRejects.disjointOrdinary outcomes

/-- A maximal left-associative tail has a unique output remainder. -/
theorem LeftAssociativeTailParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {leftBase rightBase leftResult rightResult : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeTailParses operandOrdinary precedence input
      leftBase leftResult afterLeft)
    (rightParsed : LeftAssociativeTailParses operandOrdinary precedence input
      rightBase rightResult afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBase rightResult afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightOperator rightOperand rightTail =>
          exact False.elim
            (binaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | next leftOperator leftOperand leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (binaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | next rightOperator rightOperand rightTail =>
          have afterOperatorEq := binaryOperator_output_unique leftOperator
            rightOperator
          subst afterOperatorEq
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact inductionHypothesis rightTail

/-- A rejected left-associative tail excludes every ordinary tail success. -/
theorem LeftAssociativeTailRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder} {left : Syntax.Expr}
    (rejection : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input left rejected) :
    ¬ ∃ successfulLeft result output,
      LeftAssociativeTailParses operandOrdinary precedence input successfulLeft
        result output := by
  induction rejection with
  | rightRejected rejectedOperator rejectedRight =>
      rintro ⟨successfulLeft, result, output, parsed⟩
      cases parsed with
      | done absent =>
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | next successfulOperator successfulRight successfulTail =>
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          exact outcomes.successRejectDisjoint rejectedRight
            ⟨_, _, successfulRight⟩
  | laterRejected rejectedOperator rejectedRight rejectedTail
        inductionHypothesis =>
      rintro ⟨successfulLeft, result, output, parsed⟩
      cases parsed with
      | done absent =>
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | next successfulOperator successfulRight successfulTail =>
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          have afterRightEq := outcomes.successOutputUnique rejectedRight
            successfulRight
          subst afterRightEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Ordinary left-associative success has a unique output remainder. -/
theorem LeftAssociativeOrdinaryParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterBase, leftBaseParsed, leftTail⟩
  rcases rightParsed with
    ⟨rightBase, rightAfterBase, rightBaseParsed, rightTail⟩
  have afterBaseEq := outcomes.successOutputUnique leftBaseParsed
    rightBaseParsed
  subst afterBaseEq
  exact leftTail.output_unique outcomes rightTail

/-- Complete left-associative rejection excludes ordinary success. -/
theorem LeftAssociativeRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder}
    (rejection : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input rejected) :
    ¬ ∃ expression output,
      LeftAssociativeOrdinaryParses operandOrdinary precedence input expression
        output := by
  rintro ⟨expression, output, left, afterLeft, leftParsed, tailParsed⟩
  cases rejection with
  | firstRejected firstRejected =>
      exact outcomes.successRejectDisjoint firstRejected
        ⟨left, afterLeft, leftParsed⟩
  | tailRejected rejectedLeft rejectedTail =>
      have afterLeftEq := outcomes.successOutputUnique rejectedLeft leftParsed
      subst afterLeftEq
      exact rejectedTail.disjointOrdinary outcomes
        ⟨left, expression, output, tailParsed⟩

/-- Construct the deterministic outcome contract for a left-associative
precedence layer. -/
theorem leftAssociativeDeterministicOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    DeterministicOutcomeSpec
      (LeftAssociativeOrdinaryParses operandOrdinary precedence)
      (LeftAssociativeRejects operandOrdinary operandRejects precedence) where
  successOutputUnique :=
    LeftAssociativeOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    LeftAssociativeRejects.disjointOrdinary outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties
/-! Exact operator tokens, prefix sequences, and unary expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Unary spelling fixes its operator, token span, and complete remainder. -/
theorem UnaryOperatorParses.result_unique
    {input afterLeft afterRight : Remainder}
    {left right : Located UnaryOp}
    (leftParsed : UnaryOperatorParses input left afterLeft)
    (rightParsed : UnaryOperatorParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have outputEq := leftParsed.2.trans rightParsed.2.symm
  have tokenEq := leftParsed.1.token_unique rightParsed.1
  rcases left with ⟨leftSpan, leftValue⟩
  rcases right with ⟨rightSpan, rightValue⟩
  cases leftValue <;> cases rightValue <;> simp_all [UnaryOp.symbol]

/-- An absent unary operator excludes every positive unary-token judgment. -/
theorem UnaryOperatorAbsentAt.not_parses
    {input output : Remainder} {operator : Located UnaryOp}
    (absent : UnaryOperatorAbsentAt input)
    (parsed : UnaryOperatorParses input operator output) : False := by
  rcases operator with ⟨span, value⟩
  cases value with
  | logicalNot => exact absent.1 ⟨span, parsed.1⟩
  | bitNot => exact absent.2 ⟨span, parsed.1⟩

/-- A precedence-filtered binary token fixes its operator, span, and remainder. -/
theorem BinaryOperatorAtPrecedenceParses.result_unique
    {precedence : Nat} {input afterLeft afterRight : Remainder}
    {left right : Located BinaryOp}
    (leftParsed : BinaryOperatorAtPrecedenceParses precedence input left afterLeft)
    (rightParsed : BinaryOperatorAtPrecedenceParses precedence input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  leftParsed.unique rightParsed

/-- Absence at one precedence excludes every positive token at that precedence. -/
theorem BinaryOperatorAtPrecedenceAbsentAt.not_parses
    {precedence : Nat} {input output : Remainder} {operator : Located BinaryOp}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input)
    (parsed : BinaryOperatorAtPrecedenceParses precedence input operator output) :
    False :=
  parsed.not_absent absent

/-- A maximal prefix sequence fixes all operators in source order and its end. -/
theorem UnaryOperatorsParses.result_unique
    {input : Remainder} {left right : List (Located UnaryOp)}
    {afterLeft afterRight : Remainder}
    (leftParsed : UnaryOperatorsParses input left afterLeft)
    (rightParsed : UnaryOperatorsParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightOperator _ => exact False.elim (leftAbsent.not_parses rightOperator)
  | next leftOperator leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent.not_parses leftOperator)
      | next rightOperator rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, outputEq⟩
          subst operatorEq
          subst outputEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Exact postfix values fix the complete source-preserving unary AST. -/
theorem ExpressionUnaryOrdinaryParses.value_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input left afterLeft)
    (rightParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftOperators, leftAfter, leftBase, leftPrefix, leftPostfix, leftEq⟩
  rcases rightParsed with
    ⟨rightOperators, rightAfter, rightBase, rightPrefix, rightPostfix, rightEq⟩
  rcases leftPrefix.result_unique rightPrefix with ⟨prefixEq, outputEq⟩
  subst prefixEq
  subst outputEq
  have baseEq := outcomes.successValueUnique leftPostfix rightPostfix
  subst baseEq
  exact leftEq.trans rightEq.symm

/-- Exact postfix rejection fixes the endpoint after the maximal unary prefix. -/
theorem ExpressionUnaryRejects.output_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input left right : Remainder}
    (leftRejected : ExpressionUnaryRejects postfixRejects input left)
    (rightRejected : ExpressionUnaryRejects postfixRejects input right) : left = right := by
  cases leftRejected with
  | postfixRejected leftPrefix leftPostfix =>
      cases rightRejected with
      | postfixRejected rightPrefix rightPostfix =>
          have outputEq := leftPrefix.output_unique rightPrefix
          subst outputEq
          exact outcomes.rejectOutputUnique leftPostfix rightPostfix

/-- Exact postfix outcomes lift through maximal unary-prefix parsing. -/
theorem expressionUnaryExactOutcomeSpec
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    ExactDeterministicOutcomeSpec (ExpressionUnaryOrdinaryParses postfixOrdinary)
      (ExpressionUnaryRejects postfixRejects) where
  toDeterministicOutcomeSpec := expressionUnaryDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec
  successValueUnique := ExpressionUnaryOrdinaryParses.value_unique outcomes
  rejectOutputUnique := ExpressionUnaryRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLeftAssociativeExactnessProperties
/-! Exact left-associated expression ASTs and first-rejecting endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal tail fixes the complete result when both parses share their base. -/
theorem LeftAssociativeTailParses.result_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeTailParses operandOrdinary precedence input
      base left afterLeft)
    (rightParsed : LeftAssociativeTailParses operandOrdinary precedence input
      base right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightOperator _ _ => exact False.elim (leftAbsent.not_parses rightOperator)
  | next leftOperator leftOperand leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent.not_parses leftOperator)
      | next rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          rcases outcomes.successResultUnique leftOperand rightOperand with
            ⟨operandEq, operandEndEq⟩
          subst operandEq
          subst operandEndEq
          exact ih rightTail

/-- Exact operand values fix the entire left-associated AST and retained spans. -/
theorem LeftAssociativeOrdinaryParses.value_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftBase, leftAfterBase, leftOperand, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterBase, rightOperand, rightTail⟩
  rcases outcomes.successResultUnique leftOperand rightOperand with ⟨baseEq, outputEq⟩
  subst baseEq
  subst outputEq
  exact (leftTail.result_unique outcomes rightTail).1

/-- At a fixed accumulator, a rejected tail fixes its first failing endpoint. -/
theorem LeftAssociativeTailRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder} {base : Syntax.Expr}
    (leftRejected : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input base left)
    (rightRejected : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input base right) : left = right := by
  induction leftRejected generalizing right with
  | rightRejected leftOperator leftOperand =>
      cases rightRejected with
      | rightRejected rightOperator rightOperand =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact outcomes.rejectOutputUnique leftOperand rightOperand
      | laterRejected rightOperator rightOperand _ =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | laterRejected leftOperator leftOperand leftTail ih =>
      cases rightRejected with
      | rightRejected rightOperator rightOperand =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | laterRejected rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          rcases outcomes.successResultUnique leftOperand rightOperand with
            ⟨operandEq, operandEndEq⟩
          subst operandEq
          subst operandEndEq
          exact ih rightTail

/-- Complete left-associative rejection fixes its first failing endpoint. -/
theorem LeftAssociativeRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder}
    (leftRejected : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input left)
    (rightRejected : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input right) : left = right := by
  cases leftRejected with
  | firstRejected leftOperand =>
      cases rightRejected with
      | firstRejected rightOperand => exact outcomes.rejectOutputUnique leftOperand rightOperand
      | tailRejected rightOperand _ =>
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | tailRejected leftOperand leftTail =>
      cases rightRejected with
      | firstRejected rightOperand =>
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | tailRejected rightOperand rightTail =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨baseEq, outputEq⟩
          subst baseEq
          subst outputEq
          exact leftTail.output_unique outcomes rightTail

/-- Exact operands yield exact outcomes at any left-associated precedence. -/
theorem leftAssociativeExactOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    ExactDeterministicOutcomeSpec
      (LeftAssociativeOrdinaryParses operandOrdinary precedence)
      (LeftAssociativeRejects operandOrdinary operandRejects precedence) where
  toDeterministicOutcomeSpec := leftAssociativeDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec precedence
  successValueUnique := LeftAssociativeOrdinaryParses.value_unique outcomes
  rejectOutputUnique := LeftAssociativeRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeOutcomeProperties
/-! Deterministic ordinary outcomes for Core non-associative expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary non-associative success has a unique output remainder. -/
theorem NonAssociativeOrdinaryParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : NonAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : NonAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | plain leftOperand leftAbsent =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          exact outcomes.successOutputUnique leftOperand rightOperand
      | binary rightOperand rightOperator rightRight =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact False.elim
            (binaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | binary leftOperand leftOperator leftRight =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact False.elim
            (binaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | binary rightOperand rightOperator rightRight =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          have afterOperatorEq := binaryOperator_output_unique leftOperator
            rightOperator
          subst afterOperatorEq
          exact outcomes.successOutputUnique leftRight rightRight

/-- Non-associative rejection excludes ordinary success. -/
theorem NonAssociativeRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder}
    (rejection : NonAssociativeRejects operandOrdinary operandRejects
      precedence input rejected) :
    ¬ ∃ expression output,
      NonAssociativeOrdinaryParses operandOrdinary precedence input expression
        output := by
  rintro ⟨expression, output, parsed⟩
  cases rejection with
  | firstRejected firstRejected =>
      cases parsed with
      | plain operand absent =>
          exact outcomes.successRejectDisjoint firstRejected
            ⟨_, _, operand⟩
      | binary operand operator right =>
          exact outcomes.successRejectDisjoint firstRejected
            ⟨_, _, operand⟩
  | rightRejected rejectedLeft rejectedOperator rejectedRight =>
      cases parsed with
      | plain successfulLeft absent =>
          have afterLeftEq := outcomes.successOutputUnique rejectedLeft
            successfulLeft
          subst afterLeftEq
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | binary successfulLeft successfulOperator successfulRight =>
          have afterLeftEq := outcomes.successOutputUnique rejectedLeft
            successfulLeft
          subst afterLeftEq
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          exact outcomes.successRejectDisjoint rejectedRight
            ⟨_, _, successfulRight⟩

/-- Construct the deterministic outcome contract for a non-associative
precedence layer. -/
theorem nonAssociativeDeterministicOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    DeterministicOutcomeSpec
      (NonAssociativeOrdinaryParses operandOrdinary precedence)
      (NonAssociativeRejects operandOrdinary operandRejects precedence) where
  successOutputUnique := NonAssociativeOrdinaryParses.output_unique outcomes
  successRejectDisjoint := NonAssociativeRejects.disjointOrdinary outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeExactnessProperties
/-! Exact ASTs and rejecting endpoints of non-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Operand and operator exactness fixes both plain and binary ASTs. -/
theorem NonAssociativeOrdinaryParses.value_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonAssociativeOrdinaryParses operandOrdinary precedence input left afterLeft)
    (rightParsed : NonAssociativeOrdinaryParses operandOrdinary precedence input right afterRight) :
    left = right := by
  cases leftParsed with
  | plain leftOperand leftAbsent =>
      cases rightParsed with
      | plain rightOperand _ => exact outcomes.successValueUnique leftOperand rightOperand
      | binary rightOperand rightOperator _ =>
          have outputEq := outcomes.successOutputUnique leftOperand rightOperand
          subst outputEq
          exact False.elim (leftAbsent.not_parses rightOperator)
  | binary leftOperand leftOperator leftRight =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          have outputEq := outcomes.successOutputUnique leftOperand rightOperand
          subst outputEq
          exact False.elim (rightAbsent.not_parses leftOperator)
      | binary rightOperand rightOperator rightRight =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨leftEq, leftEndEq⟩
          subst leftEq
          subst leftEndEq
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          have rightEq := outcomes.successValueUnique leftRight rightRight
          subst rightEq
          rfl

/-- Rejection fixes either the initial or committed right-operand endpoint. -/
theorem NonAssociativeRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder}
    (leftRejected : NonAssociativeRejects operandOrdinary operandRejects precedence input left)
    (rightRejected : NonAssociativeRejects operandOrdinary operandRejects precedence input right) :
    left = right := by
  cases leftRejected with
  | firstRejected leftOperand =>
      cases rightRejected with
      | firstRejected rightOperand => exact outcomes.rejectOutputUnique leftOperand rightOperand
      | rightRejected rightOperand _ _ =>
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | rightRejected leftOperand leftOperator leftRight =>
      cases rightRejected with
      | firstRejected rightOperand =>
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | rightRejected rightOperand rightOperator rightRight =>
          have leftEndEq := outcomes.successOutputUnique leftOperand rightOperand
          subst leftEndEq
          have operatorEndEq := (leftOperator.result_unique rightOperator).2
          subst operatorEndEq
          exact outcomes.rejectOutputUnique leftRight rightRight

/-- Exact operands lift through any single non-associative precedence layer. -/
theorem nonAssociativeExactOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    ExactDeterministicOutcomeSpec
      (NonAssociativeOrdinaryParses operandOrdinary precedence)
      (NonAssociativeRejects operandOrdinary operandRejects precedence) where
  toDeterministicOutcomeSpec := nonAssociativeDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec precedence
  successValueUnique := NonAssociativeOrdinaryParses.value_unique outcomes
  rejectOutputUnique := NonAssociativeRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionConditionalOutcomeProperties
/-! Deterministic ordinary outcomes for Core conditional expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A maximal conditional tail has a unique output remainder. -/
theorem ConditionalTailParses.output_unique
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input : Remainder}
    {leftCondition rightCondition leftResult rightResult : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input leftCondition leftResult afterLeft)
    (rightParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input rightCondition rightResult afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightCondition rightResult afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen
            rightColon rightAlternative rightTail =>
          exact False.elim (absent_conflicts_exact leftAbsent rightQuestion)
  | next leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
        leftAlternative leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftQuestion)
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen
            rightColon rightAlternative rightTail =>
          have afterQuestionEq := exactToken_output_unique leftQuestion
            rightQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique leftThen
            rightThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          have afterAlternativeEq := alternativeOutcomes.successOutputUnique
            leftAlternative rightAlternative
          subst afterAlternativeEq
          exact inductionHypothesis rightTail

/-- Conditional-tail rejection excludes every ordinary tail success. -/
theorem ConditionalTailRejects.disjointOrdinary
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input rejected : Remainder} {condition : Syntax.Expr}
    (rejection : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition rejected) :
    ¬ ∃ successfulCondition expression output,
      ConditionalTailParses nestedOrdinary alternativeOrdinary input
        successfulCondition expression output := by
  induction rejection with
  | thenRejected rejectedQuestionSpan rejectedQuestion rejectedThen =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          exact nestedOutcomes.successRejectDisjoint rejectedThen
            ⟨_, _, successfulThen⟩
  | colonMissing rejectedQuestionSpan rejectedQuestion rejectedThen
        rejectedColonAbsent =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          exact absent_conflicts_exact rejectedColonAbsent successfulColon
  | alternativeRejected rejectedQuestionSpan rejectedColonSpan
        rejectedQuestion rejectedThen rejectedColon rejectedAlternative =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          exact alternativeOutcomes.successRejectDisjoint rejectedAlternative
            ⟨_, _, successfulAlternative⟩
  | laterRejected rejectedQuestionSpan rejectedColonSpan rejectedQuestion
        rejectedThen rejectedColon rejectedAlternative rejectedTail
        inductionHypothesis =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterAlternativeEq := alternativeOutcomes.successOutputUnique
            rejectedAlternative successfulAlternative
          subst afterAlternativeEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Ordinary conditional success has a unique output remainder. -/
theorem ConditionalOrdinaryParses.output_unique
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary
      input left afterLeft)
    (rightParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftCondition, leftAfterCondition, leftConditionParsed, leftTail⟩
  rcases rightParsed with
    ⟨rightCondition, rightAfterCondition, rightConditionParsed, rightTail⟩
  have afterConditionEq := alternativeOutcomes.successOutputUnique
    leftConditionParsed rightConditionParsed
  subst afterConditionEq
  exact leftTail.output_unique nestedOutcomes alternativeOutcomes rightTail

/-- Complete conditional rejection excludes ordinary success. -/
theorem ConditionalRejects.disjointOrdinary
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input rejected : Remainder}
    (rejection : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input rejected) :
    ¬ ∃ expression output,
      ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input
        expression output := by
  rintro ⟨expression, output, condition, afterCondition, conditionParsed,
    tailParsed⟩
  cases rejection with
  | conditionRejected conditionRejected =>
      exact alternativeOutcomes.successRejectDisjoint conditionRejected
        ⟨condition, afterCondition, conditionParsed⟩
  | tailRejected rejectedCondition rejectedTail =>
      have afterConditionEq := alternativeOutcomes.successOutputUnique
        rejectedCondition conditionParsed
      subst afterConditionEq
      exact rejectedTail.disjointOrdinary nestedOutcomes alternativeOutcomes
        ⟨condition, expression, output, tailParsed⟩

/-- Construct the deterministic outcome contract for the conditional layer. -/
theorem conditionalDeterministicOutcomeSpec
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects) :
    DeterministicOutcomeSpec
      (ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary)
      (ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects) where
  successOutputUnique :=
    ConditionalOrdinaryParses.output_unique nestedOutcomes alternativeOutcomes
  successRejectDisjoint :=
    ConditionalRejects.disjointOrdinary nestedOutcomes alternativeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionConditionalValueProperties
/-! Exact right-associated conditional values with a shared initial condition. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact branch outcomes fix a conditional tail at the same initial condition. -/
theorem ConditionalTailParses.result_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input : Remainder} {condition left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input condition left afterLeft)
    (rightParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input condition right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next _ _ rightQuestion _ _ _ _ =>
          exact False.elim (leftAbsent ⟨_, rightQuestion.1⟩)
  | next leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
      leftAlternative leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent ⟨_, leftQuestion.1⟩)
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen rightColon
          rightAlternative rightTail =>
          rcases leftQuestion.result_unique rightQuestion with ⟨questionEq, questionEndEq⟩
          subst questionEq
          subst questionEndEq
          rcases nestedOutcomes.successResultUnique leftThen rightThen with ⟨thenEq, thenEndEq⟩
          subst thenEq
          subst thenEndEq
          rcases leftColon.result_unique rightColon with ⟨colonEq, colonEndEq⟩
          subst colonEq
          subst colonEndEq
          rcases alternativeOutcomes.successResultUnique leftAlternative rightAlternative with
            ⟨alternativeEq, alternativeEndEq⟩
          subst alternativeEq
          subst alternativeEndEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Exact initial and nested expressions fix every conditional node and span. -/
theorem ConditionalOrdinaryParses.value_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input left afterLeft)
    (rightParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftCondition, leftAfter, leftConditionParsed, leftTail⟩
  rcases rightParsed with ⟨rightCondition, rightAfter, rightConditionParsed, rightTail⟩
  rcases alternativeOutcomes.successResultUnique leftConditionParsed rightConditionParsed with
    ⟨conditionEq, outputEq⟩
  subst conditionEq
  subst outputEq
  exact (leftTail.result_unique nestedOutcomes alternativeOutcomes rightTail).1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionConditionalExactnessProperties
/-! Exact first-rejecting endpoints and complete conditional outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A conditional suffix has one first-failing endpoint at each fixed condition. -/
theorem ConditionalTailRejects.output_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input left right : Remainder} {condition : Syntax.Expr}
    (leftRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition left)
    (rightRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition right) : left = right := by
  induction leftRejected generalizing right with
  | thenRejected leftQuestionSpan leftQuestion leftThen =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.rejectOutputUnique, nestedOutcomes.successRejectDisjoint]
  | colonMissing leftQuestionSpan leftQuestion leftThen leftAbsent =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, absent_conflicts_exact]
  | alternativeRejected leftQuestionSpan leftColonSpan leftQuestion leftThen
      leftColon leftAlternative =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, alternativeOutcomes.rejectOutputUnique,
          alternativeOutcomes.successRejectDisjoint, absent_conflicts_exact]
  | laterRejected leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
      leftAlternative leftTail ih =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, alternativeOutcomes.successResultUnique,
          alternativeOutcomes.successRejectDisjoint, absent_conflicts_exact]

/-- A complete conditional has one initial-expression or suffix-rejection endpoint. -/
theorem ConditionalRejects.output_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input left right : Remainder}
    (leftRejected : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input left)
    (rightRejected : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input right) : left = right := by
  cases leftRejected with
  | conditionRejected leftCondition =>
      cases rightRejected with
      | conditionRejected rightCondition =>
          exact alternativeOutcomes.rejectOutputUnique leftCondition rightCondition
      | tailRejected rightCondition _ =>
          exact False.elim (alternativeOutcomes.successRejectDisjoint leftCondition
            ⟨_, _, rightCondition⟩)
  | tailRejected leftCondition leftTail =>
      cases rightRejected with
      | conditionRejected rightCondition =>
          exact False.elim (alternativeOutcomes.successRejectDisjoint rightCondition
            ⟨_, _, leftCondition⟩)
      | tailRejected rightCondition rightTail =>
          rcases alternativeOutcomes.successResultUnique leftCondition rightCondition with
            ⟨conditionEq, outputEq⟩
          subst conditionEq
          subst outputEq
          exact leftTail.output_unique nestedOutcomes alternativeOutcomes rightTail

/-- Exact initial and nested operands compose into full conditional exactness. -/
theorem conditionalExactOutcomeSpec
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects) :
    ExactDeterministicOutcomeSpec
      (ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary)
      (ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects alternativeRejects) where
  toDeterministicOutcomeSpec := conditionalDeterministicOutcomeSpec
    nestedOutcomes.toDeterministicOutcomeSpec alternativeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ConditionalOrdinaryParses.value_unique nestedOutcomes alternativeOutcomes
  rejectOutputUnique := ConditionalRejects.output_unique nestedOutcomes alternativeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLayerExactnessProperties
/-! Fully exact outcomes of the complete Core expression operator stack. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested and postfix expressions compose through every precedence,
retaining operator spans and the specified associativity. -/
theorem expressionLayerExactOutcomeSpec
    {nestedOrdinary postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects postfixRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (postfixOutcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    ExactDeterministicOutcomeSpec
      (ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary)
      (ExpressionLayerRejects nestedOrdinary nestedRejects postfixOrdinary postfixRejects) := by
  let unaryOutcomes := expressionUnaryExactOutcomeSpec postfixOutcomes
  let multiplyOutcomes := leftAssociativeExactOutcomeSpec unaryOutcomes 9
  let addOutcomes := leftAssociativeExactOutcomeSpec multiplyOutcomes 8
  let shiftOutcomes := leftAssociativeExactOutcomeSpec addOutcomes 7
  let bitAndOutcomes := leftAssociativeExactOutcomeSpec shiftOutcomes 6
  let bitXorOutcomes := leftAssociativeExactOutcomeSpec bitAndOutcomes 5
  let bitOrOutcomes := leftAssociativeExactOutcomeSpec bitXorOutcomes 4
  let relationalOutcomes := nonAssociativeExactOutcomeSpec bitOrOutcomes 3
  let equalityOutcomes := nonAssociativeExactOutcomeSpec relationalOutcomes 2
  let logicalAndOutcomes := leftAssociativeExactOutcomeSpec equalityOutcomes 1
  let logicalOrOutcomes := leftAssociativeExactOutcomeSpec logicalAndOutcomes 0
  exact conditionalExactOutcomeSpec nestedOutcomes logicalOrOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeProperties
/-!
Deterministic outcomes and clean embedding for the complete Core expression
operator stack.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose nested and postfix outcome contracts through every expression
operator layer. -/
theorem expressionLayerDeterministicOutcomeSpec
    {nestedOrdinary postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects postfixRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (postfixOutcomes : DeterministicOutcomeSpec postfixOrdinary
      postfixRejects) :
    DeterministicOutcomeSpec
      (ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary)
      (ExpressionLayerRejects nestedOrdinary nestedRejects postfixOrdinary
        postfixRejects) := by
  let unaryOutcomes := expressionUnaryDeterministicOutcomeSpec
    postfixOutcomes
  let multiplyOutcomes := leftAssociativeDeterministicOutcomeSpec
    unaryOutcomes 9
  let addOutcomes := leftAssociativeDeterministicOutcomeSpec
    multiplyOutcomes 8
  let shiftOutcomes := leftAssociativeDeterministicOutcomeSpec
    addOutcomes 7
  let bitAndOutcomes := leftAssociativeDeterministicOutcomeSpec
    shiftOutcomes 6
  let bitXorOutcomes := leftAssociativeDeterministicOutcomeSpec
    bitAndOutcomes 5
  let bitOrOutcomes := leftAssociativeDeterministicOutcomeSpec
    bitXorOutcomes 4
  let relationalOutcomes := nonAssociativeDeterministicOutcomeSpec
    bitOrOutcomes 3
  let equalityOutcomes := nonAssociativeDeterministicOutcomeSpec
    relationalOutcomes 2
  let logicalAndOutcomes := leftAssociativeDeterministicOutcomeSpec
    equalityOutcomes 1
  let logicalOrOutcomes := leftAssociativeDeterministicOutcomeSpec
    logicalAndOutcomes 0
  simpa [ExpressionLayerOrdinaryParses, ExpressionLayerParses,
    ExpressionLayerRejects, unaryOutcomes, multiplyOutcomes, addOutcomes,
    bitAndOutcomes, bitXorOutcomes, bitOrOutcomes, relationalOutcomes,
    equalityOutcomes, logicalAndOutcomes, logicalOrOutcomes] using
      conditionalDeterministicOutcomeSpec nestedOutcomes logicalOrOutcomes

/-- Unary success embeds when its postfix success embeds. -/
theorem ExpressionUnaryParses.toOrdinary
    {postfixClean postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (postfixEmbedding : ∀ {input expression output},
      postfixClean input expression output →
        postfixOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionUnaryParses postfixClean input expression output) :
    ExpressionUnaryParses postfixOrdinary input expression output := by
  rcases parsed with
    ⟨operators, afterOperators, base, operatorsParsed, baseParsed,
      expressionEq⟩
  exact ⟨operators, afterOperators, base, operatorsParsed,
    postfixEmbedding baseParsed, expressionEq⟩

/-- A left-associated tail embeds when each operand embeds. -/
theorem LeftAssociativeTailParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {left expression : Syntax.Expr}
    (parsed : LeftAssociativeTailParses operandClean precedence input left
      expression output) :
    LeftAssociativeTailParses operandOrdinary precedence input left expression
      output := by
  induction parsed with
  | done absent => exact .done absent
  | next operatorParsed rightParsed tail inductionHypothesis =>
      exact .next operatorParsed (operandEmbedding rightParsed)
        inductionHypothesis

/-- A complete left-associated layer embeds with its operand relation. -/
theorem LeftAssociativeParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {expression : Syntax.Expr}
    (parsed : LeftAssociativeParses operandClean precedence input expression
      output) :
    LeftAssociativeParses operandOrdinary precedence input expression output :=
    by
  rcases parsed with ⟨left, afterLeft, leftParsed, tailParsed⟩
  exact ⟨left, afterLeft, operandEmbedding leftParsed,
    tailParsed.toOrdinary operandEmbedding⟩

/-- A non-associative layer embeds with its operand relation. -/
theorem NonAssociativeParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {expression : Syntax.Expr}
    (parsed : NonAssociativeParses operandClean precedence input expression
      output) :
    NonAssociativeParses operandOrdinary precedence input expression output :=
    by
  cases parsed with
  | plain leftParsed absent => exact .plain (operandEmbedding leftParsed) absent
  | binary leftParsed operatorParsed rightParsed =>
      exact .binary (operandEmbedding leftParsed) operatorParsed
        (operandEmbedding rightParsed)

/-- A conditional tail embeds with both recursive operand relations. -/
theorem ConditionalTailParses.toOrdinary
    {nestedClean nestedOrdinary alternativeClean alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (alternativeEmbedding : ∀ {input expression output},
      alternativeClean input expression output →
        alternativeOrdinary input expression output)
    {input output : Remainder} {condition expression : Syntax.Expr}
    (parsed : ConditionalTailParses nestedClean alternativeClean input
      condition expression output) :
    ConditionalTailParses nestedOrdinary alternativeOrdinary input condition
      expression output := by
  induction parsed with
  | done absent => exact .done absent
  | next questionSpan colonSpan questionParsed thenParsed colonParsed
        alternativeParsed tail inductionHypothesis =>
      exact .next questionSpan colonSpan questionParsed
        (nestedEmbedding thenParsed) colonParsed
        (alternativeEmbedding alternativeParsed) inductionHypothesis

/-- A complete conditional layer embeds with both operand relations. -/
theorem ConditionalParses.toOrdinary
    {nestedClean nestedOrdinary alternativeClean alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (alternativeEmbedding : ∀ {input expression output},
      alternativeClean input expression output →
        alternativeOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ConditionalParses nestedClean alternativeClean input expression
      output) :
    ConditionalParses nestedOrdinary alternativeOrdinary input expression
      output := by
  rcases parsed with ⟨condition, afterCondition, conditionParsed, tailParsed⟩
  exact ⟨condition, afterCondition, alternativeEmbedding conditionParsed,
    tailParsed.toOrdinary nestedEmbedding alternativeEmbedding⟩

/-- The complete clean operator stack embeds into its ordinary counterpart. -/
theorem ExpressionLayerParses.toOrdinary
    {nestedClean nestedOrdinary postfixClean postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (postfixEmbedding : ∀ {input expression output},
      postfixClean input expression output →
        postfixOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionLayerParses nestedClean postfixClean input expression
      output) :
    ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary input
      expression output := by
  let unaryClean := ExpressionUnaryParses postfixClean
  let unaryOrdinary := ExpressionUnaryParses postfixOrdinary
  let multiplyClean := LeftAssociativeParses unaryClean 9
  let multiplyOrdinary := LeftAssociativeParses unaryOrdinary 9
  let addClean := LeftAssociativeParses multiplyClean 8
  let addOrdinary := LeftAssociativeParses multiplyOrdinary 8
  let shiftClean := LeftAssociativeParses addClean 7
  let bitAndClean := LeftAssociativeParses shiftClean 6
  let shiftOrdinary := LeftAssociativeParses addOrdinary 7
  let bitAndOrdinary := LeftAssociativeParses shiftOrdinary 6
  let bitXorClean := LeftAssociativeParses bitAndClean 5
  let bitXorOrdinary := LeftAssociativeParses bitAndOrdinary 5
  let bitOrClean := LeftAssociativeParses bitXorClean 4
  let bitOrOrdinary := LeftAssociativeParses bitXorOrdinary 4
  let relationalClean := NonAssociativeParses bitOrClean 3
  let relationalOrdinary := NonAssociativeParses bitOrOrdinary 3
  let equalityClean := NonAssociativeParses relationalClean 2
  let equalityOrdinary := NonAssociativeParses relationalOrdinary 2
  let logicalAndClean := LeftAssociativeParses equalityClean 1
  let logicalAndOrdinary := LeftAssociativeParses equalityOrdinary 1
  let logicalOrClean := LeftAssociativeParses logicalAndClean 0
  let logicalOrOrdinary := LeftAssociativeParses logicalAndOrdinary 0
  let unaryEmbedding : ∀ {input expression output},
      unaryClean input expression output →
        unaryOrdinary input expression output :=
    fun parsed => parsed.toOrdinary postfixEmbedding
  let multiplyEmbedding : ∀ {input expression output},
      multiplyClean input expression output →
        multiplyOrdinary input expression output :=
    fun parsed => parsed.toOrdinary unaryEmbedding
  let addEmbedding : ∀ {input expression output},
      addClean input expression output →
        addOrdinary input expression output :=
    fun parsed => parsed.toOrdinary multiplyEmbedding
  let shiftEmbedding : ∀ {input expression output},
      shiftClean input expression output →
        shiftOrdinary input expression output :=
    fun parsed => parsed.toOrdinary addEmbedding
  let bitAndEmbedding : ∀ {input expression output},
      bitAndClean input expression output →
        bitAndOrdinary input expression output :=
    fun parsed => parsed.toOrdinary shiftEmbedding
  let bitXorEmbedding : ∀ {input expression output},
      bitXorClean input expression output →
        bitXorOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitAndEmbedding
  let bitOrEmbedding : ∀ {input expression output},
      bitOrClean input expression output →
        bitOrOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitXorEmbedding
  let relationalEmbedding : ∀ {input expression output},
      relationalClean input expression output →
        relationalOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitOrEmbedding
  let equalityEmbedding : ∀ {input expression output},
      equalityClean input expression output →
        equalityOrdinary input expression output :=
    fun parsed => parsed.toOrdinary relationalEmbedding
  let logicalAndEmbedding : ∀ {input expression output},
      logicalAndClean input expression output →
        logicalAndOrdinary input expression output :=
    fun parsed => parsed.toOrdinary equalityEmbedding
  let logicalOrEmbedding : ∀ {input expression output},
      logicalOrClean input expression output →
        logicalOrOrdinary input expression output :=
    fun parsed => parsed.toOrdinary logicalAndEmbedding
  change ConditionalParses nestedClean logicalOrClean input expression output
    at parsed
  change ConditionalParses nestedOrdinary logicalOrOrdinary input expression
    output
  exact ConditionalParses.toOrdinary nestedEmbedding logicalOrEmbedding parsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeProperties
/-! Deterministic ordinary outcomes for guarded Core array literals. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary array-literal success has the unique output of its exact
allow-empty, no-trailing element list. -/
theorem ArrayLiteralExpressionOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      left afterLeft)
    (rightParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftValues =>
      cases rightParsed with
      | parsed rightValues =>
          exact NoTrailingDelimitedListParses.output_unique
            (opening := .leftBracket) (closing := .rightBracket)
            (elementParses := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftValues rightValues

/-- A selected array-literal rejection excludes every ordinary array
success. -/
theorem ArrayLiteralExpressionRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ArrayLiteralExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ expression output,
      ArrayLiteralExpressionOrdinaryParses nestedOrdinary input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | present openingSpan openingToken valuesRejected =>
      cases successful with
      | parsed valuesParsed =>
          exact valuesRejected.disjointAllowEmptyNoTrailing nestedOutcomes
            ⟨_, _, valuesParsed⟩

/-- Lift deterministic nested expression outcomes to the guarded array
literal branch. -/
theorem arrayLiteralExpressionDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ArrayLiteralExpressionOrdinaryParses nestedOrdinary)
      (ArrayLiteralExpressionRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ArrayLiteralExpressionOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ArrayLiteralExpressionRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreParenthesizedTailOutcomeProperties
/-! Determinism and rejection exclusion for the parenthesized tuple tail. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every successful tuple tail starts with the selected comma. -/
theorem ParenthesizedTupleTailParses.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {elements : List Syntax.Expr}
    {closingSpan : SourceSpan}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (parsed : ParenthesizedTupleTailParses nestedOrdinary input elements
      closingSpan output) : False := by
  cases parsed with
  | trailing commaSpan closingSpan commaParsed closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | final commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress laterCommaAbsent closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | next commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress tail =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- Every rejected tuple tail likewise starts with the selected comma. -/
theorem ParenthesizedTupleTailRejects.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (rejection : ParenthesizedTupleTailRejects nestedOrdinary nestedRejects
      input rejected) : False := by
  cases rejection with
  | elementRejected commaSpan commaParsed closingAbsent elementRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | closingMissing commaSpan commaParsed closingAbsentAfterComma
        elementParsed progress laterCommaAbsent closingAbsent =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | laterRejected commaSpan commaParsed closingAbsent elementParsed progress
        tailRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- A successful maximal tuple tail has a unique output remainder whenever a
nested ordinary expression does. -/
theorem ParenthesizedTupleTailParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    (nestedOutputUnique : ∀ {input : Remainder}
      {left right : Syntax.Expr} {afterLeft afterRight : Remainder},
      nestedOrdinary input left afterLeft →
      nestedOrdinary input right afterRight → afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List Syntax.Expr}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ParenthesizedTupleTailParses nestedOrdinary input left leftClosing
          afterLeft →
      ParenthesizedTupleTailParses nestedOrdinary input right rightClosing
          afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact exactToken_output_unique leftClosing rightClosing
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact exactToken_output_unique leftClosing rightClosing
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Exact tuple-tail rejection excludes every successful tuple tail. -/
theorem ParenthesizedTupleTailRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedTupleTailRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ elements closingSpan output,
      ParenthesizedTupleTailParses nestedOrdinary input elements closingSpan
        output := by
  induction rejection with
  | elementRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
  | closingMissing rejectedCommaSpan rejectedComma
        rejectedClosingAbsentAfterComma rejectedElement rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterComma
            successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | laterRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement rejectedProgress rejectedTail inductionHypothesis =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeProperties
/-! Deterministic ordinary outcomes for guarded Core parenthesized atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A parenthesized ordinary success has a unique maximal output remainder. -/
theorem ParenthesizedExpressionOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpeningSpan leftClosingSpan leftOpening leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact exactToken_output_unique leftClosing rightClosing
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | group leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightElement
          subst afterElementEq
          exact exactToken_output_unique leftClosing rightClosing
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightFirst
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | tuple leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftFirst
            rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique leftFirst
            rightFirst
          subst afterFirstEq
          exact ParenthesizedTupleTailParses.output_unique
            (nestedOrdinary := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftTail rightTail

/-- Exact guarded parenthesized rejection excludes every ordinary success. -/
theorem ParenthesizedExpressionRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ expression output,
      ParenthesizedExpressionOrdinaryParses nestedOrdinary input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | firstRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
  | closingMissing rejectedOpeningSpan rejectedOpening
        rejectedClosingAbsentAfterOpening rejectedFirst rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterOpening
            successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | tailRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst rejectedProgress rejectedTail =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.disjointOrdinary nestedOutcomes
            ⟨_, _, _, successfulTail⟩

/-- Lift deterministic nested expression outcomes to guarded parenthesized
atoms. -/
theorem parenthesizedExpressionDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ParenthesizedExpressionOrdinaryParses nestedOrdinary)
      (ParenthesizedExpressionRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ParenthesizedExpressionOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ParenthesizedExpressionRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreParenthesizedExactnessProperties
/-! Exact source-order elements, closing spans, and parenthesized Core ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested expressions fix a tuple tail's forward elements, close, and output. -/
theorem ParenthesizedTupleTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ∀ {input : Remainder} {left right : List Syntax.Expr}
      {leftClosing rightClosing : SourceSpan} {afterLeft afterRight : Remainder},
      ParenthesizedTupleTailParses nestedOrdinary input left leftClosing afterLeft →
      ParenthesizedTupleTailParses nestedOrdinary input right rightClosing afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, absent_conflicts_exact]
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
          absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftTail ih =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
          absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]

/-- Exact nested expressions fix empty/group/tuple choice and the complete AST. -/
theorem ParenthesizedExpressionOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique, outcomes.successResultUnique,
      ParenthesizedTupleTailParses.result_unique outcomes,
      absent_conflicts_exact, ParenthesizedTupleTailParses.comma_conflicts_absent]

/-- Parenthesized ordinary success fixes both the complete AST and remainder. -/
theorem ParenthesizedExpressionOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryProperties
/-! Functionality and outcome exclusion for Core atom recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- Every scan stop preserves its complete declarative remainder. -/
theorem ExpressionAtomRecoveryStops.output_eq
    {input stopped : Remainder}
    (stops : ExpressionAtomRecoveryStops input stopped) : stopped = input := by
  cases stops <;> rfl

/-- An atom recovery scan has functional output from one current remainder. -/
theorem ExpressionAtomRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.Expr} {afterLeft afterRight : Remainder},
      ExpressionAtomRecoveryScanParses first leftLast input left afterLeft →
      ExpressionAtomRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete ordinary atom recovery has functional output. -/
theorem ExpressionAtomRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryParses input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every complete recovery rejection is non-consuming. -/
theorem ExpressionAtomRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : ExpressionAtomRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes complete recovery rejection. -/
theorem ExpressionAtomRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : ExpressionAtomRecoveryRejects input rejected) :
    ¬ ∃ expression output, ExpressionAtomRecoveryParses input expression output := by
  rintro ⟨expression, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd current.1)
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for complete atom recovery. -/
theorem expressionAtomRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExpressionAtomRecoveryParses
      ExpressionAtomRecoveryRejects where
  successOutputUnique := ExpressionAtomRecoveryParses.output_unique
  successRejectDisjoint := ExpressionAtomRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeProperties
/-! Deterministic outcomes at the public Core atom recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pre-recovery boundary is also a stop of the recovery scan itself. -/
theorem ExpressionAtomBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : ExpressionAtomBoundaryStops input) :
    ExpressionAtomRecoveryStops input input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | rightBracket token => exact .rightBracket token
  | rightBrace token => exact .rightBrace token
  | question token => exact .question token
  | colon token => exact .colon token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | elseKeyword token => exact .elseKeyword token

/-- Preserved carrier and active-window evidence makes cursor-only rewind
exactly the original declarative input. -/
theorem CoreAtomRejectsWithPreservedWindow.exists_rewind_eq
    {coreRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : CoreAtomRejectsWithPreservedWindow coreRejects input) :
    ∃ failed, coreRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary atom success has a functional output whenever the Core
outcome does. -/
theorem ExpressionAtomOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact coreOutcomes.successOutputUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes both direct Core and recovered success. -/
theorem ExpressionAtomRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : ExpressionAtomRejects coreRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact expressionAtomRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public atom rejection leaves the rewound declarative input
unchanged. -/
theorem ExpressionAtomRejects.output_eq
    {coreRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ExpressionAtomRejects coreRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift a deterministic Core outcome through rewind and atom recovery. -/
theorem expressionAtomDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (ExpressionAtomOrdinaryParses coreOrdinary coreRejects)
      (ExpressionAtomRejects coreRejects) where
  successOutputUnique := ExpressionAtomOrdinaryParses.output_unique
    coreOutcomes
  successRejectDisjoint := ExpressionAtomRejects.disjointOrdinary
    coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryExactnessProperties
/-! Exact recovery ASTs and public Core atom rewind outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed recovery prefix determines the complete diagnosed error AST and span. -/
theorem ExpressionAtomRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryScanParses first last input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryScanParses first last input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftToken leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightToken rightTail =>
          have tokenEq := leftToken.token_unique rightToken
          cases tokenEq
          exact ih rightTail

/-- A complete recovery fixes its initial token and exact error AST. -/
theorem ExpressionAtomRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryParses input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryParses input right afterRight) : left = right := by
  cases leftParsed with
  | recovered leftToken leftScan =>
      cases rightParsed with
      | recovered rightToken rightScan =>
          have tokenEq := leftToken.token_unique rightToken
          cases tokenEq
          exact leftScan.value_unique rightScan

/-- Atom recovery has exact successful error ASTs and non-consuming rejections. -/
theorem expressionAtomRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExpressionAtomRecoveryParses ExpressionAtomRecoveryRejects where
  toDeterministicOutcomeSpec := expressionAtomRecoveryDeterministicOutcomeSpec
  successValueUnique := ExpressionAtomRecoveryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Public atom rewind preserves exact successful ASTs without needing raw core
rejection endpoints to be unique. -/
theorem ExpressionAtomOrdinaryParses.value_unique_of_success
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (values : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft → coreOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input left afterLeft)
    (rightParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input right afterRight) :
    left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact values leftCore rightCore
      | recovered rightRejected _ _ =>
          rcases rightRejected with ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact False.elim (outcomes.successRejectDisjoint rejected ⟨_, _, leftCore⟩)
  | recovered leftRejected _ leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact False.elim (outcomes.successRejectDisjoint rejected ⟨_, _, rightCore⟩)
      | recovered _ _ rightRecovery => exact leftRecovery.value_unique rightRecovery

/-- Rewinding all public rejection paths gives one complete atom endpoint. -/
theorem ExpressionAtomRejects.output_unique
    {coreRejects : Remainder → Remainder → Prop} {input left right : Remainder}
    (leftRejected : ExpressionAtomRejects coreRejects input left)
    (rightRejected : ExpressionAtomRejects coreRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact core success values suffice for fully exact public atom outcomes. -/
theorem expressionAtomExactOutcomeSpecOfSuccess
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (values : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft → coreOrdinary input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec (ExpressionAtomOrdinaryParses coreOrdinary coreRejects)
      (ExpressionAtomRejects coreRejects) where
  toDeterministicOutcomeSpec := expressionAtomDeterministicOutcomeSpec outcomes
  successValueUnique := ExpressionAtomOrdinaryParses.value_unique_of_success outcomes values
  rejectOutputUnique := ExpressionAtomRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
