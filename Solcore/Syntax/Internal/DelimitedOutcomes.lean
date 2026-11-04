import Solcore.Syntax.Grammar.Basics

/-!
Properties of the declarative grammar of delimited lists, transactional choice and
primitive tokens: outcomes are deterministic, and successful values and rejection points
are unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties
/-! Deterministic laws for prioritized transactional fallback outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional fallback has a unique output whenever both alternatives do. -/
theorem TransactionalFallbackOrdinaryParses.output_unique {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | primary leftPrimary =>
      cases rightParsed with
      | primary rightPrimary =>
          exact primaryOutcomes.successOutputUnique leftPrimary rightPrimary
      | fallback rightPrimaryRejection rightFallback =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint rightPrimaryRejection
              ⟨_, _, leftPrimary⟩)
  | fallback leftPrimaryRejection leftFallback =>
      cases rightParsed with
      | primary rightPrimary =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint leftPrimaryRejection
              ⟨_, _, rightPrimary⟩)
      | fallback rightPrimaryRejection rightFallback =>
          exact fallbackOutcomes.successOutputUnique leftFallback
            rightFallback

/-- Rejection of both alternatives excludes every wrapper success. -/
theorem TransactionalFallbackRejects.disjointOrdinary {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects)
    {input rejected : Remainder}
    (rejection : TransactionalFallbackRejects primaryRejects fallbackRejects
      input rejected) :
    ¬ ∃ value output,
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output := by
  rintro ⟨value, output, parsed⟩
  cases rejection with
  | both primaryRejection fallbackRejection =>
      cases parsed with
      | primary primaryParsed =>
          exact primaryOutcomes.successRejectDisjoint primaryRejection
            ⟨_, _, primaryParsed⟩
      | fallback otherPrimaryRejection fallbackParsed =>
          exact fallbackOutcomes.successRejectDisjoint fallbackRejection
            ⟨_, _, fallbackParsed⟩

/-- Build deterministic wrapper outcomes from deterministic branch outcomes. -/
theorem transactionalFallbackDeterministicOutcomeSpec {alpha : Type}
    (primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects) :
    DeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) where
  successOutputUnique := fun leftParsed rightParsed =>
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed
  successRejectDisjoint := fun rejection =>
    rejection.disjointOrdinary primaryOutcomes fallbackOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTransactionalFallbackExactnessProperties
/-! Full functionality transport through prioritized transactional fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Successful branch values and priority fix the wrapper value; neither
branch needs a unique raw rejection endpoint. -/
theorem TransactionalFallbackOrdinaryParses.value_unique_of_success {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | primary leftPrimary =>
      cases rightParsed with
      | primary rightPrimary =>
          exact primaryValues leftPrimary rightPrimary
      | fallback rightPrimaryRejects rightFallback =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint rightPrimaryRejects
              ⟨_, _, leftPrimary⟩)
  | fallback leftPrimaryRejects leftFallback =>
      cases rightParsed with
      | primary rightPrimary =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint leftPrimaryRejects
              ⟨_, _, rightPrimary⟩)
      | fallback rightPrimaryRejects rightFallback =>
          exact fallbackValues leftFallback rightFallback

/-- Prioritized transactional fallback preserves exact successful values when
both alternatives have exact outcomes. -/
theorem TransactionalFallbackOrdinaryParses.value_unique {alpha : Type}
    {primaryParses fallbackParses : Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses
      primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right :=
  leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
    primaryOutcomes.toDeterministicOutcomeSpec
    primaryOutcomes.successValueUnique fallbackOutcomes.successValueUnique
    rightParsed

/-- Deterministic branches with unique successful values fix the wrapper's
complete result without assumptions on their raw rejecting endpoints. -/
theorem TransactionalFallbackOrdinaryParses.result_unique_of_success {alpha : Type}
    {primaryParses fallbackParses : Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues
      fallbackValues rightParsed,
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed⟩

/-- Prioritized transactional fallback fixes its successful value and final
remainder when both alternatives have exact outcomes. -/
theorem TransactionalFallbackOrdinaryParses.result_unique {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses
      primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique primaryOutcomes fallbackOutcomes rightParsed,
    leftParsed.output_unique primaryOutcomes.toDeterministicOutcomeSpec
      fallbackOutcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- A double transactional rejection always has the unique original-input
endpoint. -/
theorem TransactionalFallbackRejects.output_unique
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejects : TransactionalFallbackRejects primaryRejects fallbackRejects
      input left)
    (rightRejects : TransactionalFallbackRejects primaryRejects
      fallbackRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Transactional rewind supplies exact rejecting endpoints independently of
the raw branch endpoints. Only deterministic branches and unique successful
values are needed to obtain the full wrapper contract. -/
theorem transactionalFallbackExactOutcomeSpecOfSuccess {alpha : Type}
    (primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) where
  toDeterministicOutcomeSpec :=
    transactionalFallbackDeterministicOutcomeSpec primaryParses
      fallbackParses primaryRejects fallbackRejects
      primaryOutcomes fallbackOutcomes
  successValueUnique := fun leftParsed rightParsed =>
    leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues
      fallbackValues rightParsed
  rejectOutputUnique := TransactionalFallbackRejects.output_unique

/-- Exact branch outcomes lift through prioritized transactional fallback. -/
theorem transactionalFallbackExactOutcomeSpec {alpha : Type}
    (primaryParses fallbackParses : Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses fallbackRejects) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) :=
  transactionalFallbackExactOutcomeSpecOfSuccess primaryParses fallbackParses
    primaryRejects fallbackRejects primaryOutcomes.toDeterministicOutcomeSpec
    fallbackOutcomes.toDeterministicOutcomeSpec primaryOutcomes.successValueUnique
    fallbackOutcomes.successValueUnique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTailRejectionProperties
/-! Disjointness of exact delimited-tail rejection traces from success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A no-trailing tail rejection cannot overlap a clean successful tail. -/
theorem DelimitedTailRejects.disjointNoTrailing {α : Type}
    {closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedTailRejects closing false ordinaryParses
      nestedRejects input rejectedOutput) :
    ¬ ∃ elements closingSpan output,
      NoTrailingDelimitedTailParses closing cleanParses input elements
        closingSpan output := by
  induction rejected with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact absent_conflicts_token closingAbsent closingToken
      | next commaToken _ _ _ =>
          exact absent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close commaAbsent _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next _ elementParsed _ _ =>
          exact outcomes.successRejectDisjoint nestedRejected
            ⟨_, _, cleanToOrdinary elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close commaAbsent _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next _ cleanElementParsed _ cleanTail =>
          have ordinaryClean := cleanToOrdinary cleanElementParsed
          have outputEq := outcomes.successOutputUnique elementParsed
            ordinaryClean
          subst outputEq
          exact inductionHypothesis ⟨_, _, _, cleanTail⟩

/-- An allow-trailing tail rejection cannot overlap a clean successful tail. -/
theorem DelimitedTailRejects.disjointTrailing {α : Type}
    {closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedTailRejects closing true ordinaryParses
      nestedRejects input rejectedOutput) :
    ¬ ∃ elements closingSpan output,
      TrailingDelimitedTailParses closing cleanParses input elements
        closingSpan output := by
  induction rejected with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact absent_conflicts_token closingAbsent closingToken
      | trailing commaToken _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next commaToken _ _ _ _ =>
          exact absent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨elements, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact absent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | next _ _ elementParsed _ _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, cleanToOrdinary elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨elements, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact absent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | next _ _ cleanElementParsed _ cleanTail =>
              have ordinaryClean := cleanToOrdinary cleanElementParsed
              have outputEq := outcomes.successOutputUnique elementParsed
                ordinaryClean
              subst outputEq
              exact inductionHypothesis ⟨_, _, _, cleanTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
/-! Totality and exactness of independent current-input rejection reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every carrier has an exact current-token or empty-window observation. -/
theorem currentInputAt_total (source : SourceId) (endByte : Nat)
    (input : Remainder) :
    ∃ span found, CurrentInputAt source endByte input span found := by
  by_cases inside : input.cursor < input.endIndex
  · cases current : input.tokens[input.cursor]? with
    | none => exact ⟨_, _, .missingToken inside current⟩
    | some token => exact ⟨_, _, .token ⟨inside, current⟩⟩
  · exact ⟨_, _, .windowEnd (Nat.le_of_not_gt inside)⟩

/-- Fixed source, byte boundary, and remainder determine both observed fields. -/
theorem CurrentInputAt.result_unique
    {source : SourceId} {endByte : Nat} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {leftFound rightFound : Option TokenKind}
    (left : CurrentInputAt source endByte input leftSpan leftFound)
    (right : CurrentInputAt source endByte input rightSpan rightFound) :
    leftSpan = rightSpan ∧ leftFound = rightFound := by
  cases left with
  | token leftPresent =>
      cases right with
      | token rightPresent =>
          have same := Option.some.inj (leftPresent.2.symm.trans rightPresent.2)
          cases same
          exact ⟨rfl, rfl⟩
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd leftPresent.1)
      | missingToken inside missing => simp [leftPresent.2] at missing
  | windowEnd atEnd =>
      cases right with
      | token rightPresent => exact False.elim (Nat.not_lt_of_ge atEnd rightPresent.1)
      | windowEnd => exact ⟨rfl, rfl⟩
      | missingToken inside missing => exact False.elim (Nat.not_lt_of_ge atEnd inside)
  | missingToken inside missing =>
      cases right with
      | token rightPresent => simp [rightPresent.2] at missing
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | missingToken => exact ⟨rfl, rfl⟩

/-- Every expected-token catalog and context select a report. -/
theorem rejectAtReports_total (source : SourceId) (endByte : Nat)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (input : Remainder) :
    ∃ diagnostic, RejectAtReports source endByte expected context input diagnostic := by
  rcases currentInputAt_total source endByte input with ⟨span, found, current⟩
  exact ⟨_, .reported current⟩

/-- Reports fix the full source span, found token, expectations, and context. -/
theorem RejectAtReports.diagnostic_unique
    {source : SourceId} {endByte : Nat}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {input : Remainder} {left right : ParseDiagnostic}
    (leftReported : RejectAtReports source endByte expected context input left)
    (rightReported : RejectAtReports source endByte expected context input right) :
    left = right := by
  cases leftReported with
  | reported leftCurrent =>
      cases rightReported with
      | reported rightCurrent =>
          rcases leftCurrent.result_unique rightCurrent with ⟨rfl, rfl⟩
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingSuccessProperties
/-!
Functionality and relation embeddings for successful generic delimited lists
that reject a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A no-trailing tail has a unique output whenever one nested element does.
Element values and closing spans need not agree. -/
theorem NoTrailingDelimitedTailParses.output_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      NoTrailingDelimitedTailParses closing elementParses input left
          leftClosing afterLeft →
      NoTrailingDelimitedTailParses closing elementParses input right
          rightClosing afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close => rfl
      | next rightCommaToken _ _ _ =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | next leftCommaToken leftElementParsed leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | next _ rightElementParsed _ rightTail =>
          have afterElementEq :=
            elementOutputUnique leftElementParsed rightElementParsed
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Pointwise inclusion of element relations lifts to no-trailing tails. -/
theorem NoTrailingDelimitedTailParses.mapElementRelation {alpha : Type}
    {closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {elements : List alpha}
    {closingSpan : SourceSpan}
    (parsed : NoTrailingDelimitedTailParses closing source input elements
      closingSpan output) :
    NoTrailingDelimitedTailParses closing target input elements closingSpan
      output := by
  induction parsed with
  | close commaAbsent closingToken =>
      exact .close commaAbsent closingToken
  | next commaToken elementParsed progress tail inductionHypothesis =>
      exact .next commaToken (includeElement elementParsed) progress
        inductionHypothesis

/-- A nonempty no-trailing list has functional output whenever its nested
element relation does. -/
theorem NonemptyNoTrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have afterFirstEq := elementOutputUnique leftFirstParsed rightFirstParsed
  subst afterFirstEq
  exact NoTrailingDelimitedTailParses.output_unique
    (closing := closing) (elementParses := elementParses)
    elementOutputUnique leftTail rightTail

/-- Pointwise inclusion of element relations lifts to nonempty no-trailing
lists without changing their value or remainder. -/
theorem NonemptyNoTrailingDelimitedListParses.mapElementRelation
    {alpha : Type} {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NonemptyNoTrailingDelimitedListParses opening closing source
      input values output) :
    NonemptyNoTrailingDelimitedListParses opening closing target input values
      output := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, first, afterFirst, rest, closingSpan, tokensEq,
    endIndexEq, openingToken, includeElement firstParsed, progress,
    tail.mapElementRelation includeElement, elementsEq, spanEq⟩

/-- An allow-empty no-trailing list has functional output whenever its nested
element relation does. -/
theorem NoTrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NoTrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : NoTrailingDelimitedListParses opening closing elementParses
      input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightClosingAbsent rightParsed =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftParsed =>
      cases rightParsed with
      | empty _ _ _ rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightParsed =>
          exact NonemptyNoTrailingDelimitedListParses.output_unique
            (opening := opening) (closing := closing)
            (elementParses := elementParses) elementOutputUnique leftParsed
            rightParsed

/-- Pointwise inclusion of element relations lifts to allow-empty no-trailing
lists. -/
theorem NoTrailingDelimitedListParses.mapElementRelation {alpha : Type}
    {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing source input values
      output) :
    NoTrailingDelimitedListParses opening closing target input values output :=
  by
    cases parsed with
    | empty openingSpan closingSpan openingToken closingToken =>
        exact .empty openingSpan closingSpan openingToken closingToken
    | nonempty closingAbsent parsed =>
        exact .nonempty closingAbsent
          (parsed.mapElementRelation includeElement)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties
/-!
Deterministic ordinary outcomes for possibly empty comma-separated lists that
forbid a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact rejection of an allow-empty, no-trailing list excludes every
ordinary success for the same deterministic element outcomes. -/
theorem DelimitedListRejects.disjointAllowEmptyNoTrailing {alpha : Type}
    {opening closing : Symbol}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input rejected : Remainder}
    (rejection : DelimitedListRejects opening closing true false
      ordinaryParses nestedRejects input rejected) :
    ¬ ∃ values output,
      NoTrailingDelimitedListParses opening closing ordinaryParses input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases successful with
      | empty openingSpan closingSpan openingToken closingToken =>
          exact absent_conflicts_token openingAbsent openingToken
      | nonempty closingAbsent parsed =>
          rcases parsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact absent_conflicts_token openingAbsent openingToken
  | firstRejected openingSpan openingToken continues firstRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty successfulOpeningSpan closingSpan successfulOpening
                closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty successfulClosingAbsent parsed =>
              rcases parsed with ⟨successfulOpeningSpan, first, afterFirst,
                rest, closingSpan, tokensEq, endIndexEq, successfulOpening,
                firstParsed, progress, tail, elementsEq, spanEq⟩
              exact outcomes.successRejectDisjoint firstRejected
                ⟨first, afterFirst, firstParsed⟩
  | tailRejected openingSpan openingToken continues firstParsed progress
        tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty successfulOpeningSpan closingSpan successfulOpening
                closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty successfulClosingAbsent parsed =>
              rcases parsed with ⟨successfulOpeningSpan, successfulFirst,
                successfulAfterFirst, rest, closingSpan, tokensEq, endIndexEq,
                successfulOpening, successfulFirstParsed, successfulProgress,
                successfulTail, elementsEq, spanEq⟩
              have afterFirstEq := outcomes.successOutputUnique firstParsed
                successfulFirstParsed
              subst afterFirstEq
              exact tailRejected.disjointNoTrailing outcomes
                (fun parsed => parsed)
                ⟨rest, closingSpan, output, successfulTail⟩

/-- Construct the deterministic outcome contract for an allow-empty,
no-trailing delimited list. -/
theorem noTrailingDelimitedListDeterministicOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true false ordinaryParses
        nestedRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact NoTrailingDelimitedListParses.output_unique
      (opening := opening) (closing := closing)
      (elementParses := ordinaryParses) outcomes.successOutputUnique leftParsed
      rightParsed
  successRejectDisjoint :=
    DelimitedListRejects.disjointAllowEmptyNoTrailing outcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties
/-!
Functionality and relation embeddings for successful generic delimited lists
that allow a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A trailing-comma tail has a unique output whenever one nested element does.
Element values and closing spans need not agree. -/
theorem TrailingDelimitedTailParses.output_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      TrailingDelimitedTailParses closing elementParses input left leftClosing
          afterLeft →
      TrailingDelimitedTailParses closing elementParses input right rightClosing
          afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close => rfl
      | trailing rightCommaToken _ =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
      | next rightCommaToken _ _ _ _ =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | trailing leftCommaToken leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing => rfl
      | next _ rightClosingAbsent _ _ _ =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | next leftCommaToken leftClosingAbsent leftElementParsed leftProgress
        leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing _ rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | next _ _ rightElementParsed _ rightTail =>
          have afterElementEq :=
            elementOutputUnique leftElementParsed rightElementParsed
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Pointwise inclusion of element relations lifts to trailing-comma tails. -/
theorem TrailingDelimitedTailParses.mapElementRelation {alpha : Type}
    {closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {elements : List alpha}
    {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses closing source input elements
      closingSpan output) :
    TrailingDelimitedTailParses closing target input elements closingSpan
      output := by
  induction parsed with
  | close commaAbsent closingToken =>
      exact .close commaAbsent closingToken
  | trailing commaToken closingToken =>
      exact .trailing commaToken closingToken
  | next commaToken closingAbsent elementParsed progress tail
        inductionHypothesis =>
      exact .next commaToken closingAbsent (includeElement elementParsed)
        progress inductionHypothesis

/-- A nonempty trailing-comma list has functional output whenever its nested
element relation does. -/
theorem NonemptyTrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have afterFirstEq := elementOutputUnique leftFirstParsed rightFirstParsed
  subst afterFirstEq
  exact TrailingDelimitedTailParses.output_unique
    (closing := closing) (elementParses := elementParses)
    elementOutputUnique leftTail rightTail

/-- Pointwise inclusion of element relations lifts to nonempty trailing-comma
lists without changing their value or remainder. -/
theorem NonemptyTrailingDelimitedListParses.mapElementRelation {alpha : Type}
    {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NonemptyTrailingDelimitedListParses opening closing source input
      values output) :
    NonemptyTrailingDelimitedListParses opening closing target input values
      output := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, first, afterFirst, rest, closingSpan, tokensEq,
    endIndexEq, openingToken, includeElement firstParsed, progress,
    tail.mapElementRelation includeElement, elementsEq, spanEq⟩

/-- An allow-empty trailing-comma list has functional output whenever its
nested element relation does. -/
theorem TrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : TrailingDelimitedListParses opening closing elementParses
      input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightClosingAbsent rightParsed =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftParsed =>
      cases rightParsed with
      | empty _ _ _ rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightParsed =>
          exact NonemptyTrailingDelimitedListParses.output_unique
            (opening := opening) (closing := closing)
            (elementParses := elementParses) elementOutputUnique leftParsed
            rightParsed

/-- Pointwise inclusion of element relations lifts to allow-empty
trailing-comma lists. -/
theorem TrailingDelimitedListParses.mapElementRelation {alpha : Type}
    {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : TrailingDelimitedListParses opening closing source input values
      output) :
    TrailingDelimitedListParses opening closing target input values output := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact .empty openingSpan closingSpan openingToken closingToken
  | nonempty closingAbsent parsed =>
      exact .nonempty closingAbsent
        (parsed.mapElementRelation includeElement)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
/-!
Diagnostic-inclusive deterministic outcomes for nonempty comma-separated lists
that allow a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A required allow-trailing list rejection excludes every nonempty
allow-trailing success. -/
theorem DelimitedListRejects.disjointNonemptyTrailing {alpha : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing false true
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      NonemptyTrailingDelimitedListParses opening closing cleanParses input
        values output := by
  intro successful
  rcases successful with ⟨values, output, openingSpan, first, afterFirst,
    rest, closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
    progress, tail, elementsEq, spanEq⟩
  cases rejected with
  | openingMissing openingAbsent =>
      exact absent_conflicts_token openingAbsent openingToken
  | firstRejected rejectedOpeningSpan rejectedOpening continues
        nestedRejected =>
      cases continues
      exact outcomes.successRejectDisjoint nestedRejected
        ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected rejectedOpeningSpan rejectedOpening continues ordinaryFirst
        rejectedProgress tailRejected =>
      cases continues
      have cleanFirst := cleanToOrdinary firstParsed
      have afterFirstEq := outcomes.successOutputUnique ordinaryFirst cleanFirst
      subst afterFirstEq
      exact tailRejected.disjointTrailing outcomes cleanToOrdinary
        ⟨_, _, _, tail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreIdentifierOutcomeProperties
/-! Deterministic ordinary outcomes for one checked Core identifier. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Checked identifiers have a unique output remainder. -/
theorem IdentifierParses.output_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftToken, leftTokens, leftEndIndex, leftCursor⟩
  rcases rightParsed with ⟨rightToken, rightTokens, rightEndIndex,
    rightCursor⟩
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Checked-identifier rejection excludes checked-identifier success. -/
theorem IdentifierRejects.disjoint {input rejected : Remainder}
    (rejection : IdentifierRejects input rejected) :
    ¬ ∃ name output, IdentifierParses input name output := by
  cases rejection with
  | absent identifierAbsent =>
      rintro ⟨name, output, parsed⟩
      exact identifierAbsent ⟨name.span, name.value, parsed.1⟩

/-- Checked identifiers form a deterministic ordinary outcome. -/
theorem identifierDeterministicOutcomeSpec :
    DeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  successOutputUnique := IdentifierParses.output_unique
  successRejectDisjoint := IdentifierRejects.disjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePrimitiveExactnessProperties
/-! Exact functionality of primitive declarative token outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One carrier slot contains at most one exact token. -/
theorem TokenAt.token_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- An exact-token success fixes the consumed source span. -/
theorem ExactTokenParses.span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  exact congrArg (fun token : Token => token.span)
    (leftParsed.1.token_unique rightParsed.1)

/-- An exact-token success fixes the one-token advanced remainder. -/
theorem ExactTokenParses.output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- An exact-token success fixes both its span and final remainder. -/
theorem ExactTokenParses.result_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan ∧ leftOutput = rightOutput :=
  ⟨leftParsed.span_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The token at one checked-identifier position fixes its exact value. -/
theorem IdentifierParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) : left = right := by
  have tokenEq : ({ span := left.span, value := .identifier left.value } :
      Token) = { span := right.span, value := .identifier right.value } :=
    leftParsed.1.token_unique rightParsed.1
  cases left
  cases right
  simp_all

/-- A checked identifier fixes both its exact value and final remainder. -/
theorem IdentifierParses.result_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Checked-identifier rejection has one exact nonconsuming endpoint. -/
theorem IdentifierRejects.output_unique {input left right : Remainder}
    (leftRejects : IdentifierRejects input left)
    (rightRejects : IdentifierRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Checked identifiers have fully functional success and rejection outcomes. -/
theorem identifierExactOutcomeSpec :
    ExactDeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  toDeterministicOutcomeSpec := identifierDeterministicOutcomeSpec
  successValueUnique := IdentifierParses.value_unique
  rejectOutputUnique := IdentifierRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedRejectionExactnessProperties
/-! Exact rejection-endpoint functionality for generic delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A delimited-tail rejection has one exact failing endpoint whenever the
nested production has exact ordinary outcomes. -/
theorem DelimitedTailRejects.output_unique {alpha : Type}
    {closing : Symbol} {allowTrailing : Bool}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : DelimitedTailRejects closing allowTrailing
      ordinaryParses nestedRejects input left)
    (rightRejects : DelimitedTailRejects closing allowTrailing
      ordinaryParses nestedRejects input right) : left = right := by
  induction leftRejects generalizing right with
  | delimiterMissing leftCommaAbsent leftClosingAbsent =>
      cases rightRejects with
      | delimiterMissing => rfl
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightComma)
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightComma)
  | elementRejected leftCommaSpan leftComma leftContinues
        leftNestedRejects =>
      cases rightRejects with
      | delimiterMissing rightCommaAbsent rightClosingAbsent =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftComma)
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact outcomes.rejectOutputUnique leftNestedRejects
            rightNestedRejects
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          exact False.elim
            (outcomes.successRejectDisjoint leftNestedRejects
              ⟨_, _, rightElement⟩)
  | laterRejected leftCommaSpan leftComma leftContinues leftElement
        leftProgress leftTail inductionHypothesis =>
      cases rightRejects with
      | delimiterMissing rightCommaAbsent rightClosingAbsent =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftComma)
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact False.elim
            (outcomes.successRejectDisjoint rightNestedRejects
              ⟨_, _, leftElement⟩)
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          have afterElementEq :=
            outcomes.successOutputUnique leftElement rightElement
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- A complete delimited-list rejection has one exact failing endpoint
whenever the nested production has exact ordinary outcomes. -/
theorem DelimitedListRejects.output_unique {alpha : Type}
    {opening closing : Symbol} {allowEmpty allowTrailing : Bool}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : DelimitedListRejects opening closing allowEmpty
      allowTrailing ordinaryParses nestedRejects input left)
    (rightRejects : DelimitedListRejects opening closing allowEmpty
      allowTrailing ordinaryParses nestedRejects input right) : left = right :=
  by
    cases leftRejects with
    | openingMissing leftOpeningAbsent =>
        cases rightRejects with
        | openingMissing => rfl
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening)
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening)
    | firstRejected leftOpeningSpan leftOpening leftContinues
          leftNestedRejects =>
        cases rightRejects with
        | openingMissing rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening)
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact outcomes.rejectOutputUnique leftNestedRejects
              rightNestedRejects
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            exact False.elim
              (outcomes.successRejectDisjoint leftNestedRejects
                ⟨_, _, rightFirst⟩)
    | tailRejected leftOpeningSpan leftOpening leftContinues leftFirst
          leftProgress leftTail =>
        cases rightRejects with
        | openingMissing rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening)
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact False.elim
              (outcomes.successRejectDisjoint rightNestedRejects
                ⟨_, _, leftFirst⟩)
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            have afterFirstEq :=
              outcomes.successOutputUnique leftFirst rightFirst
            subst afterFirstEq
            exact leftTail.output_unique outcomes rightTail

end Solcore.Syntax.DeclarativeGrammar
end
