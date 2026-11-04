import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Grammar.Yul

/-!
Exactness of the declarative grammar of delimited lists: outcomes fix the whole result.
Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedFallbackProperties
/-!
Whole-list rejection disjointness and concrete transactional fallback specs.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A required no-trailing list rejection excludes every clean success. -/
theorem DelimitedListRejects.disjointNonemptyNoTrailing {α : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing false false
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      NonemptyNoTrailingDelimitedListParses opening closing cleanParses
        input values output := by
  intro successful
  rcases successful with ⟨values, output, openingSpan, first, afterFirst,
    rest, closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
    progress, tail, elementsEq, spanEq⟩
  cases rejected with
  | openingMissing openingAbsent =>
      exact absent_conflicts_token openingAbsent openingToken
  | firstRejected _ _ continues nestedRejected =>
      cases continues
      exact outcomes.successRejectDisjoint nestedRejected
        ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected _ _ continues ordinaryFirst _ tailRejected =>
      cases continues
      have cleanFirst := cleanToOrdinary firstParsed
      have outputEq := outcomes.successOutputUnique ordinaryFirst cleanFirst
      subst outputEq
      exact tailRejected.disjointNoTrailing outcomes cleanToOrdinary
        ⟨_, _, _, tail⟩

/-- An allow-empty/trailing list rejection excludes every clean success. -/
theorem DelimitedListRejects.disjointAllowEmptyTrailing {α : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing true true
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      TrailingDelimitedListParses opening closing cleanParses input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejected with
  | openingMissing openingAbsent =>
      cases successful with
      | empty _ _ openingToken _ =>
          exact absent_conflicts_token openingAbsent openingToken
      | nonempty _ parsed =>
          rcases parsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact absent_conflicts_token openingAbsent openingToken
  | firstRejected _ openingToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty _ parsed =>
              rcases parsed with ⟨openingSpan, first, afterFirst, rest,
                closingSpan, tokensEq, endIndexEq, parsedOpening, firstParsed,
                progress, tail, elementsEq, spanEq⟩
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected _ openingToken continues ordinaryFirst _ tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty _ parsed =>
              rcases parsed with ⟨openingSpan, first, afterFirst, rest,
                closingSpan, tokensEq, endIndexEq, parsedOpening, firstParsed,
                progress, tail, elementsEq, spanEq⟩
              have cleanFirst := cleanToOrdinary firstParsed
              have outputEq := outcomes.successOutputUnique ordinaryFirst
                cleanFirst
              subst outputEq
              exact tailRejected.disjointTrailing outcomes cleanToOrdinary
                ⟨_, _, _, tail⟩

/-- Exact rejection predicate for required pattern constructor arguments. -/
def ConstructorArgumentsRejects
    (ordinaryParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, DelimitedListRejects .leftParen .rightParen false false
    ordinaryParses nestedRejects input rejected

/-- Build the committed pattern fallback from deterministic nested outcomes. -/
def ConstructorArgumentsFallbackSpec.ofOutcomes
    (ordinaryParses cleanParses :
      Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output) :
    ConstructorArgumentsFallbackSpec cleanParses where
  rejects := ConstructorArgumentsRejects ordinaryParses nestedRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejected⟩
    rintro ⟨arguments, output, parsed⟩
    exact rejected.disjointNonemptyNoTrailing outcomes cleanToOrdinary
      ⟨{
        span := arguments.span
        elements := arguments.elements.toList
      }, output, parsed⟩

/-- Exact rejection predicate for allow-empty/trailing Yul call arguments. -/
def YulCallArgumentsRejects
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, DelimitedListRejects .leftParen .rightParen true true
    ordinaryParses nestedRejects input rejected

/-- Build the committed Yul fallback from deterministic nested outcomes. -/
def YulCallArgumentsFallbackSpec.ofOutcomes
    (ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output) :
    YulCallArgumentsFallbackSpec cleanParses where
  rejects := YulCallArgumentsRejects ordinaryParses nestedRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejected⟩
    exact rejected.disjointAllowEmptyTrailing outcomes cleanToOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
/-! Full functionality of no-trailing generic delimited-list outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A no-trailing tail fixes its element sequence, closing span, and final
remainder whenever one nested element has exact ordinary outcomes. -/
theorem NoTrailingDelimitedTailParses.result_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      NoTrailingDelimitedTailParses closing elementParses input left
          leftClosing afterLeft →
      NoTrailingDelimitedTailParses closing elementParses input right
          rightClosing afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          have tokenEq := leftClosingToken.token_unique rightClosingToken
          cases tokenEq
          exact ⟨rfl, rfl, rfl⟩
      | next rightCommaToken rightElement rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | next leftCommaToken leftElement leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | next rightCommaToken rightElement rightProgress rightTail =>
          rcases outcomes.successResultUnique leftElement rightElement with
            ⟨elementEq, afterElementEq⟩
          subst elementEq
          subst afterElementEq
          rcases inductionHypothesis rightTail with
            ⟨elementsEq, closingEq, outputEq⟩
          subst elementsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- A nonempty no-trailing list fixes its complete delimited-list value. -/
theorem NonemptyNoTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have openingTokenEq := leftOpeningToken.token_unique rightOpeningToken
  have openingEq : leftOpening = rightOpening :=
    congrArg (fun token : Token => token.span) openingTokenEq
  rcases outcomes.successResultUnique leftFirstParsed rightFirstParsed with
    ⟨firstEq, afterFirstEq⟩
  subst firstEq
  subst afterFirstEq
  rcases leftTail.result_unique outcomes rightTail with
    ⟨restEq, closingEq, outputEq⟩
  cases left
  cases right
  simp_all

/-- An allow-empty no-trailing list fixes its complete delimited-list value. -/
theorem NoTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NoTrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : NoTrailingDelimitedListParses opening closing elementParses
      input right afterRight) : left = right := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          have openingTokenEq :=
            leftOpeningToken.token_unique rightOpeningToken
          have openingEq : leftOpening = rightOpening :=
            congrArg (fun token : Token => token.span) openingTokenEq
          have closingTokenEq :=
            leftClosingToken.token_unique rightClosingToken
          have closingEq : leftClosing = rightClosing :=
            congrArg (fun token : Token => token.span) closingTokenEq
          subst openingEq
          subst closingEq
          rfl
      | nonempty rightClosingAbsent rightNonempty =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftNonempty =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightNonempty =>
          exact leftNonempty.value_unique outcomes rightNonempty

/-- Required no-trailing delimited lists have fully functional success and
rejection outcomes. -/
theorem nonemptyNoTrailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (NonemptyNoTrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing false false ordinaryParses
        nestedRejects) where
  toDeterministicOutcomeSpec := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed rightParsed
      exact NonemptyNoTrailingDelimitedListParses.output_unique
        (opening := opening) (closing := closing)
        (elementParses := ordinaryParses) outcomes.successOutputUnique
        leftParsed rightParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact rejection.disjointNonemptyNoTrailing
        outcomes.toDeterministicOutcomeSpec (fun parsed => parsed)
  }
  successValueUnique :=
    NonemptyNoTrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

/-- Allow-empty no-trailing delimited lists have fully functional success and
rejection outcomes. -/
theorem noTrailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true false ordinaryParses
        nestedRejects) where
  toDeterministicOutcomeSpec :=
    noTrailingDelimitedListDeterministicOutcomeSpec opening closing
      outcomes.toDeterministicOutcomeSpec
  successValueUnique := NoTrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
/-!
Deterministic ordinary outcomes for possibly empty comma-separated lists that
allow a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Construct the deterministic outcome contract for an allow-empty,
allow-trailing delimited list. -/
theorem trailingDelimitedListDeterministicOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true true ordinaryParses
        nestedRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact TrailingDelimitedListParses.output_unique
      (opening := opening) (closing := closing)
      (elementParses := ordinaryParses) outcomes.successOutputUnique leftParsed
      rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact rejection.disjointAllowEmptyTrailing outcomes (fun parsed => parsed)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
/-! Full functionality of generic allow-trailing delimited-list outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An allow-trailing tail fixes its elements, closing span, and output when
the nested production has exact outcomes. -/
theorem TrailingDelimitedTailParses.result_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      TrailingDelimitedTailParses closing elementParses input left leftClosing
          afterLeft →
      TrailingDelimitedTailParses closing elementParses input right rightClosing
          afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          have tokenEq := leftClosingToken.token_unique rightClosingToken
          cases tokenEq
          exact ⟨rfl, rfl, rfl⟩
      | trailing rightCommaToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | trailing leftCommaToken leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing rightCommaToken rightClosingToken =>
          have tokenEq := leftClosingToken.token_unique rightClosingToken
          cases tokenEq
          exact ⟨rfl, rfl, rfl⟩
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | next leftCommaToken leftClosingAbsent leftElement leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing rightCommaToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          rcases outcomes.successResultUnique leftElement rightElement with
            ⟨elementEq, afterElementEq⟩
          subst elementEq
          subst afterElementEq
          rcases inductionHypothesis rightTail with
            ⟨elementsEq, closingEq, outputEq⟩
          subst elementsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- A required allow-trailing list fixes its complete delimited-list value. -/
theorem NonemptyTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have openingTokenEq := leftOpeningToken.token_unique rightOpeningToken
  have openingEq : leftOpening = rightOpening :=
    congrArg (fun token : Token => token.span) openingTokenEq
  rcases outcomes.successResultUnique leftFirstParsed rightFirstParsed with
    ⟨firstEq, afterFirstEq⟩
  subst firstEq
  subst afterFirstEq
  rcases leftTail.result_unique outcomes rightTail with
    ⟨restEq, closingEq, outputEq⟩
  cases left
  cases right
  simp_all

/-- An allow-empty, allow-trailing list fixes its complete value. -/
theorem TrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : TrailingDelimitedListParses opening closing elementParses
      input right afterRight) :
    left = right := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          have openingTokenEq :=
            leftOpeningToken.token_unique rightOpeningToken
          have openingEq : leftOpening = rightOpening :=
            congrArg (fun token : Token => token.span) openingTokenEq
          have closingTokenEq :=
            leftClosingToken.token_unique rightClosingToken
          have closingEq : leftClosing = rightClosing :=
            congrArg (fun token : Token => token.span) closingTokenEq
          subst openingEq
          subst closingEq
          rfl
      | nonempty rightClosingAbsent rightNonempty =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftNonempty =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightNonempty =>
          exact leftNonempty.value_unique outcomes rightNonempty

/-- Required allow-trailing lists have exact success values and rejection
endpoints. -/
theorem nonemptyTrailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses opening closing elementParses)
      (DelimitedListRejects opening closing false true elementParses
        nestedRejects) where
  toDeterministicOutcomeSpec := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed rightParsed
      exact NonemptyTrailingDelimitedListParses.output_unique
        (opening := opening) (closing := closing)
        (elementParses := elementParses) outcomes.successOutputUnique
        leftParsed rightParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact rejection.disjointNonemptyTrailing
        outcomes.toDeterministicOutcomeSpec (fun parsed => parsed)
  }
  successValueUnique :=
    NonemptyTrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

/-- Allow-empty, allow-trailing lists have exact success values and rejection
endpoints. -/
theorem trailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses opening closing elementParses)
      (DelimitedListRejects opening closing true true elementParses
        nestedRejects) where
  toDeterministicOutcomeSpec :=
    trailingDelimitedListDeterministicOutcomeSpec opening closing
      outcomes.toDeterministicOutcomeSpec
  successValueUnique := TrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
end
