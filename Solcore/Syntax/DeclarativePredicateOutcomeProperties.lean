import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativePredicateOutcomeGrammar

/-!
Deterministic parser-independent outcomes for predicates and grouped predicate
sequences.
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

/-- Recursive type-expression tails have a unique final remainder. -/
theorem TypeExprTrailingDelimitedTailParses.output_unique
    {closing : Symbol} {input : Remainder}
    {left right : List Syntax.TypeExpr}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprTrailingDelimitedTailParses closing input left
      leftClosing afterLeft)
    (rightParsed : TypeExprTrailingDelimitedTailParses closing input right
      rightClosing afterRight) : afterLeft = afterRight := by
  refine TypeExprTrailingDelimitedTailParses.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun closing input _ _ output _ =>
      ∀ {right rightClosing afterRight},
        TypeExprTrailingDelimitedTailParses closing input right rightClosing
          afterRight → output = afterRight)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ ?_ (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) leftParsed rightParsed
  · intro closing input closingSpan commaAbsent closingToken right
      rightClosing afterRight rightParsed
    cases rightParsed with
    | close => rfl
    | trailing commaToken _ =>
        exact False.elim (absent_conflicts_token commaAbsent commaToken)
    | next commaToken _ _ _ _ _ =>
        exact False.elim (absent_conflicts_token commaAbsent commaToken)
  · intro closing input commaSpan closingSpan commaToken closingToken right
      rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim (absent_conflicts_token commaAbsent commaToken)
    | trailing => rfl
    | next _ closingAbsent _ _ _ _ =>
        exact False.elim
          (absent_conflicts_token closingAbsent closingToken)
  · intro closing input afterElement output commaSpan closingSpan element
      elements values commaToken closingAbsent progress elementsEq elementParsed
      tail elementIH tailIH right rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim (absent_conflicts_token commaAbsent commaToken)
    | trailing _ rightClosing =>
        exact False.elim
          (absent_conflicts_token closingAbsent rightClosing)
    | next _ _ _ _ rightElement rightTail =>
        have afterElementEq := TypeExprParses.output_unique elementParsed
          rightElement
        subst afterElementEq
        exact tailIH rightTail

/-- Optional named type arguments have a unique final remainder. -/
theorem OptionalNamedTypeArgumentsParses.output_unique
    {input : Remainder}
    {left right : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalNamedTypeArgumentsParses input left afterLeft)
    (rightParsed : OptionalNamedTypeArgumentsParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftOpeningAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ _ rightOpening _ _ _ _ _ _ _ =>
          exact False.elim
            (absent_conflicts_token leftOpeningAbsent rightOpening)
  | present _ _ leftOpening _ _ _ _ _ leftFirst leftTail =>
      cases rightParsed with
      | absent rightOpeningAbsent =>
          exact False.elim
            (absent_conflicts_token rightOpeningAbsent leftOpening)
      | present _ _ _ _ _ _ _ _ rightFirst rightTail =>
          have afterFirstEq := TypeExprParses.output_unique leftFirst rightFirst
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- One predicate grammar derivation has a unique final remainder. -/
theorem PredicateParses.output_unique {input : Remainder}
    {left right : Syntax.Predicate} {afterLeft afterRight : Remainder}
    (leftParsed : PredicateParses input left afterLeft)
    (rightParsed : PredicateParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed _ leftSubject leftColon leftName leftArguments =>
      cases rightParsed with
      | parsed _ rightSubject rightColon rightName rightArguments =>
          have afterSubjectEq := TypeExprParses.output_unique leftSubject
            rightSubject
          subst afterSubjectEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          exact leftArguments.output_unique rightArguments

/-- Exact predicate rejection excludes every successful predicate derivation. -/
theorem PredicateRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : PredicateRejects input rejected) :
    ¬ ∃ value output, PredicateParses input value output := by
  rintro ⟨value, output, successful⟩
  cases successful with
  | parsed successfulColonSpan successfulSubject successfulColon
        successfulName successfulArguments =>
      cases rejection with
      | subjectRejected subjectRejected =>
          exact typeExprDeterministicOutcomeSpec.successRejectDisjoint
            subjectRejected ⟨_, _, successfulSubject⟩
      | colonMissing rejectedSubject colonAbsent =>
          have afterSubjectEq := TypeExprParses.output_unique rejectedSubject
            successfulSubject
          subst afterSubjectEq
          exact absent_conflicts_token colonAbsent successfulColon.1
      | nameRejected rejectedColonSpan rejectedSubject rejectedColon
            nameRejected =>
          have afterSubjectEq := TypeExprParses.output_unique rejectedSubject
            successfulSubject
          subst afterSubjectEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | argumentsRejected rejectedColonSpan rejectedSubject rejectedColon
            rejectedName argumentsRejected =>
          have afterSubjectEq := TypeExprParses.output_unique rejectedSubject
            successfulSubject
          subst afterSubjectEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact argumentsRejected.disjointOptional
            typeExprDeterministicOutcomeSpec successfulArguments

/-- Predicates have deterministic and exclusive ordinary outcomes. -/
theorem predicateDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PredicateParses PredicateRejects where
  successOutputUnique := PredicateParses.output_unique
  successRejectDisjoint := PredicateRejects.disjointOrdinary

/-- Grouped predicate success has a unique final remainder. -/
theorem GroupedPredicateSequenceParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : GroupedPredicateSequenceParses input left afterLeft)
    (rightParsed : GroupedPredicateSequenceParses input right afterRight) :
    afterLeft = afterRight := by
  unfold GroupedPredicateSequenceParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := PredicateParses) PredicateParses.output_unique
      leftParsed rightParsed

/-- Exact grouped rejection excludes every grouped predicate success. -/
theorem GroupedPredicateSequenceRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : GroupedPredicateSequenceRejects input rejected) :
    ¬ ∃ values output, GroupedPredicateSequenceParses input values output := by
  rintro ⟨values, output, successful⟩
  unfold GroupedPredicateSequenceParses at successful
  exact rejection.disjointNonemptyTrailing predicateDeterministicOutcomeSpec
    (fun parsed => parsed) ⟨_, _, successful⟩

/-- Grouped predicate sequences have deterministic and exclusive outcomes. -/
theorem groupedPredicateSequenceDeterministicOutcomeSpec :
    DeterministicOutcomeSpec GroupedPredicateSequenceParses
      GroupedPredicateSequenceRejects where
  successOutputUnique := GroupedPredicateSequenceParses.output_unique
  successRejectDisjoint := GroupedPredicateSequenceRejects.disjointOrdinary

/-- A grouped rejection is direct evidence that no grouped success exists. -/
theorem GroupedPredicateSequenceRejects.no_parse
    {input rejected : Remainder}
    (rejection : GroupedPredicateSequenceRejects input rejected) :
    ¬ ∃ values output, GroupedPredicateSequenceParses input values output :=
  rejection.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
