import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Grammar.Basics

/-!
Properties of the declarative grammar of parameters and predicates: outcomes are
deterministic, and successful values and rejection points are unique. Nothing here
mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateSequenceOutcomeProperties
/-!
Deterministic ordinary outcomes for bare and grouped-first predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A successful bare tail has one final remainder. -/
theorem BarePredicateTailParses.output_unique
    {leftLast rightLast : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses leftLast input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses rightLast input right rightFinal
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightLast right rightFinal afterRight with
  | done commaAbsent =>
      cases rightParsed with
      | done => rfl
      | trailing commaParsed _ =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | next commaParsed _ _ _ =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
  | trailing commaParsed nextAbsent =>
      cases rightParsed with
      | done commaAbsent =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | trailing rightComma _ =>
          exact exactToken_output_unique commaParsed rightComma
      | next rightComma rightStarts _ _ =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact False.elim (nextAbsent rightStarts)
  | next commaParsed nextStarts predicateParsed tailParsed tailIH =>
      cases rightParsed with
      | done commaAbsent =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | trailing rightComma rightAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact False.elim (rightAbsent nextStarts)
      | next rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          have afterPredicateEq := PredicateParses.output_unique
            predicateParsed rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- An exact bare-tail rejection excludes every successful tail. -/
theorem BarePredicateTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BarePredicateTailRejects input rejected)
    {lastSpan finalSpan : SourceSpan} {predicates : List Syntax.Predicate}
    {output : Remainder}
    (successful : BarePredicateTailParses lastSpan input predicates finalSpan
      output) : False := by
  induction rejection generalizing lastSpan predicates finalSpan output with
  | predicateRejected commaSpan commaParsed nextStarts predicateRejected =>
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | trailing rightComma nextAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact nextAbsent nextStarts
      | next rightComma rightStarts predicateParsed tailParsed =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact predicateDeterministicOutcomeSpec.successRejectDisjoint
            predicateRejected ⟨_, _, predicateParsed⟩
  | next commaSpan commaParsed nextStarts predicateParsed tailRejected tailIH =>
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | trailing rightComma nextAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact nextAbsent nextStarts
      | next rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          have afterPredicateEq := PredicateParses.output_unique
            predicateParsed rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- A successful bare predicate sequence has one final remainder. -/
theorem BarePredicateSequenceParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateSequenceParses input left afterLeft)
    (rightParsed : BarePredicateSequenceParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftFirst leftTail =>
      cases rightParsed with
      | parsed rightFirst rightTail =>
          have afterFirstEq := PredicateParses.output_unique leftFirst
            rightFirst
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Exact bare-sequence rejection excludes every ordinary success. -/
theorem BarePredicateSequenceRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BarePredicateSequenceRejects input rejected) :
    ¬ ∃ values output, BarePredicateSequenceParses input values output := by
  rintro ⟨values, output, successful⟩
  cases successful with
  | parsed successfulFirst successfulTail =>
      cases rejection with
      | firstRejected firstRejected =>
          exact predicateDeterministicOutcomeSpec.successRejectDisjoint
            firstRejected ⟨_, _, successfulFirst⟩
      | tailRejected rejectedFirst tailRejected =>
          have afterFirstEq := PredicateParses.output_unique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact tailRejected.disjointOrdinary successfulTail

/-- Bare predicate sequences have deterministic and exclusive outcomes. -/
theorem barePredicateSequenceDeterministicOutcomeSpec :
    DeterministicOutcomeSpec BarePredicateSequenceParses
      BarePredicateSequenceRejects where
  successOutputUnique := BarePredicateSequenceParses.output_unique
  successRejectDisjoint := BarePredicateSequenceRejects.disjointOrdinary

private theorem openingAbsent_conflicts_grouped
    {input output : Remainder}
    {values : NonemptyDelimitedList Syntax.Predicate}
    (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen))
    (parsed : GroupedPredicateSequenceParses input values output) : False := by
  unfold GroupedPredicateSequenceParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact openingAbsent ⟨openingSpan, openingToken⟩

/-- A prioritized predicate-sequence success has one final remainder. -/
theorem PredicateSequenceParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | bare leftUnavailable leftBare =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact leftBare.output_unique rightBare
      | grouped rightGrouped =>
          exact False.elim (leftUnavailable ⟨_, _, rightGrouped⟩)
  | grouped leftGrouped =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact False.elim (rightUnavailable ⟨_, _, leftGrouped⟩)
      | grouped rightGrouped =>
          exact leftGrouped.output_unique rightGrouped

/-- Exact predicate-sequence rejection excludes every prioritized success. -/
theorem PredicateSequenceRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : PredicateSequenceRejects input rejected) :
    ¬ ∃ values output, PredicateSequenceParses input values output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | direct openingAbsent bareRejected =>
      cases successful with
      | bare groupedUnavailable bareParsed =>
          exact bareRejected.disjointOrdinary ⟨_, _, bareParsed⟩
      | grouped groupedParsed =>
          exact openingAbsent_conflicts_grouped openingAbsent groupedParsed
  | fallback openingPresent groupedRejected bareRejected =>
      cases successful with
      | bare groupedUnavailable bareParsed =>
          exact bareRejected.disjointOrdinary ⟨_, _, bareParsed⟩
      | grouped groupedParsed =>
          exact groupedRejected.disjointOrdinary ⟨_, _, groupedParsed⟩

/-- Grouped-first predicate sequences have deterministic exact outcomes. -/
theorem predicateSequenceDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PredicateSequenceParses PredicateSequenceRejects
    where
  successOutputUnique := PredicateSequenceParses.output_unique
  successRejectDisjoint := PredicateSequenceRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties
/-! Deterministic exact outcomes for optional canonical `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional `where` success has one final remainder. -/
theorem OptionalWhereClauseParses.output_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightPredicates =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftPredicates =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightPredicates =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact PredicateSequenceParses.output_unique leftPredicates
            rightPredicates

/-- Exact optional-`where` rejection excludes every successful branch. -/
theorem OptionalWhereClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalWhereClauseRejects input rejected) :
    ¬ ∃ clause output, OptionalWhereClauseParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | predicatesRejected rejectedMarkerSpan rejectedMarker
        predicatesRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_exact markerAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker predicatesParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact predicateSequenceDeterministicOutcomeSpec.successRejectDisjoint
            predicatesRejected ⟨_, _, predicatesParsed⟩

/-- Optional canonical `where` has deterministic and exclusive outcomes. -/
theorem optionalWhereClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalWhereClauseParses
      OptionalWhereClauseRejects where
  successOutputUnique := OptionalWhereClauseParses.output_unique
  successRejectDisjoint := OptionalWhereClauseRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeProperties
/-! Deterministic ordinary outcomes of the lambda-parameter core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem identifier_value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) : left = right := by
  have tokenEq : ({ span := left.span, value := .identifier left.value } :
      Token) = { span := right.span, value := .identifier right.value } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  cases left
  cases right
  simp_all

/-- A comptime-branch outcome proves the positive two-token guard. -/
theorem ComptimeLambdaParameterOrdinaryParses.startsAt
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {input output : Remainder} {parameter : Syntax.LambdaParameter}
    (parsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      parameter output) : ComptimeLambdaParameterStartsAt input := by
  cases parsed with
  | typed markerSpan colonSpan markerParsed nameParsed =>
      have nameToken := nameParsed.1
      rw [markerParsed.2] at nameToken
      exact ⟨markerSpan, _, _, markerParsed.1, nameToken⟩
  | typeMissing markerSpan markerParsed nameParsed =>
      have nameToken := nameParsed.1
      rw [markerParsed.2] at nameToken
      exact ⟨markerSpan, _, _, markerParsed.1, nameToken⟩

/-- The ordinary suffix has one deterministic remainder. -/
theorem OrdinaryLambdaParameterTailOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {name : Syntax.Identifier} {input : Remainder}
    {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input left afterLeft)
    (rightParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | inferred leftAbsent =>
      cases rightParsed with
      | inferred => rfl
      | typed span colonParsed typeParsed =>
          exact False.elim
            (absent_conflicts_token leftAbsent colonParsed.1)
  | typed span leftColon leftType =>
      cases rightParsed with
      | inferred rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
      | typed span rightColon rightType =>
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType

/-- Ordinary-name success has one deterministic remainder. -/
theorem OrdinaryLambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          have nameEq := identifier_value_unique leftName rightName
          subst nameEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail

/-- Contextual-comptime success has one deterministic remainder. -/
theorem ComptimeLambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | typed markerSpan colonSpan leftMarker leftName leftColon leftType =>
      cases rightParsed with
      | typed markerSpan colonSpan rightMarker rightName rightColon rightType =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType
      | typeMissing markerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
  | typeMissing markerSpan leftMarker leftName leftAbsent =>
      cases rightParsed with
      | typed markerSpan colonSpan rightMarker rightName rightColon rightType =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (absent_conflicts_token leftAbsent rightColon.1)
      | typeMissing markerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact leftName.output_unique rightName

/-- Core success has one deterministic remainder. -/
theorem LambdaParameterCoreOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | comptime left =>
      cases rightParsed with
      | comptime right => exact left.output_unique typeOutcomes right
      | ordinary absent right => exact False.elim (absent left.startsAt)
  | ordinary absent left =>
      cases rightParsed with
      | comptime right => exact False.elim (absent right.startsAt)
      | ordinary otherAbsent right =>
          exact left.output_unique typeOutcomes right

/-- Core rejection excludes every ordinary Core success. -/
theorem LambdaParameterCoreRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : LambdaParameterCoreRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases rejection with
  | comptimeType markerSpan colonSpan rejectedMarker rejectedName
        rejectedColon typeRejected =>
      cases parsed with
      | ordinary absent ordinaryParsed =>
          have nameToken := rejectedName.1
          rw [rejectedMarker.2] at nameToken
          exact absent ⟨markerSpan, _, _, rejectedMarker.1, nameToken⟩
      | comptime successful =>
          cases successful with
          | typeMissing successMarkerSpan successMarker successName
                colonAbsent =>
              have afterMarkerEq := exactToken_output_unique rejectedMarker
                successMarker
              subst afterMarkerEq
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed markerSpan colonSpan successMarker successName successColon
                typeParsed =>
              have afterMarkerEq := exactToken_output_unique rejectedMarker
                successMarker
              subst afterMarkerEq
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              have afterColonEq := exactToken_output_unique rejectedColon
                successColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩
  | ordinaryName absent nameRejected =>
      cases parsed with
      | comptime successful => exact absent successful.startsAt
      | ordinary otherAbsent successful =>
          cases successful with
          | parsed nameParsed tail =>
              exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | ordinaryType colonSpan absent rejectedName rejectedColon typeRejected =>
      cases parsed with
      | comptime successful => exact absent successful.startsAt
      | ordinary otherAbsent successful =>
          cases successful with
          | parsed successName tail =>
              have afterNameEq := rejectedName.output_unique successName
              subst afterNameEq
              cases tail with
              | inferred colonAbsent =>
                  exact absent_conflicts_token colonAbsent rejectedColon.1
              | typed span successColon typeParsed =>
                  have afterColonEq := exactToken_output_unique rejectedColon
                    successColon
                  subst afterColonEq
                  exact typeOutcomes.successRejectDisjoint typeRejected
                    ⟨_, _, typeParsed⟩

/-- Deterministic ordinary outcome contract for `lambdaParameterCore`. -/
theorem lambdaParameterCoreDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (LambdaParameterCoreOrdinaryParses typeOrdinary)
      (LambdaParameterCoreRejects typeRejects) where
  successOutputUnique := LambdaParameterCoreOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := LambdaParameterCoreRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterCoreValueProperties
/-! Successful-value functionality for the ordinary lambda-parameter core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem lambdaParameter_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- At one fixed name, an inferred or typed suffix fixes its parameter AST. -/
theorem OrdinaryLambdaParameterTailOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {name : Syntax.Identifier} {input : Remainder}
    {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input left afterLeft)
    (rightParsed : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
      input right afterRight) : left = right := by
  cases leftParsed with
  | inferred leftAbsent =>
      cases rightParsed with
      | inferred => rfl
      | typed rightSpan rightColon rightType =>
          exact False.elim
            (lambdaParameter_absent_conflicts_exact leftAbsent rightColon)
  | typed leftSpan leftColon leftType =>
      cases rightParsed with
      | inferred rightAbsent =>
          exact False.elim
            (lambdaParameter_absent_conflicts_exact rightAbsent leftColon)
      | typed rightSpan rightColon rightType =>
          have afterColonEq := leftColon.output_unique rightColon
          subst afterColonEq
          have typeEq := typeOutcomes.successValueUnique leftType rightType
          subst typeEq
          rfl

/-- The ordinary-name branch fixes its inferred or typed parameter value. -/
theorem OrdinaryLambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      left afterLeft)
    (rightParsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.value_unique typeOutcomes rightTail

/-- The contextual-comptime branch fixes its typed or missing-type AST. -/
theorem ComptimeLambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      left afterLeft)
    (rightParsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
      right afterRight) : left = right := by
  cases leftParsed with
  | typed leftMarkerSpan leftColonSpan leftMarker leftName leftColon
      leftType =>
      cases rightParsed with
      | typed rightMarkerSpan rightColonSpan rightMarker rightName
          rightColon rightType =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          have afterColonEq := leftColon.output_unique rightColon
          subst afterColonEq
          have typeEq := typeOutcomes.successValueUnique leftType rightType
          subst typeEq
          rfl
      | typeMissing rightMarkerSpan rightMarker rightName rightAbsent =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (lambdaParameter_absent_conflicts_exact rightAbsent leftColon)
  | typeMissing leftMarkerSpan leftMarker leftName leftAbsent =>
      cases rightParsed with
      | typed rightMarkerSpan rightColonSpan rightMarker rightName
          rightColon rightType =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact False.elim
            (lambdaParameter_absent_conflicts_exact leftAbsent rightColon)
      | typeMissing rightMarkerSpan rightMarker rightName rightAbsent =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          have nameEq := identifierExactOutcomeSpec.successValueUnique
            leftName rightName
          subst nameEq
          rfl

/-- Ordered comptime/ordinary dispatch fixes every successful Core value. -/
theorem LambdaParameterCoreOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | comptime leftComptime =>
      cases rightParsed with
      | comptime rightComptime =>
          exact leftComptime.value_unique typeOutcomes rightComptime
      | ordinary rightAbsent rightOrdinary =>
          exact False.elim (rightAbsent leftComptime.startsAt)
  | ordinary leftAbsent leftOrdinary =>
      cases rightParsed with
      | comptime rightComptime =>
          exact False.elim (leftAbsent rightComptime.startsAt)
      | ordinary rightAbsent rightOrdinary =>
          exact leftOrdinary.value_unique typeOutcomes rightOrdinary

/-- A non-recovering lambda-parameter success fixes its AST and remainder. -/
theorem LambdaParameterCoreOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : LambdaParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique typeOutcomes rightParsed,
    leftParsed.output_unique typeOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties
/-! Deterministic exact outcomes for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem GenericParametersParses.opening_present
    {input output : Remainder} {parameters : Syntax.GenericParameters}
    (parsed : GenericParametersParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol .less
    } := by
  unfold GenericParametersParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

/-- A successful generic-parameter list has one final remainder. -/
theorem GenericParametersParses.output_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    afterLeft = afterRight := by
  unfold GenericParametersParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .less) (closing := .greater)
    (elementParses := IdentifierParses) IdentifierParses.output_unique
    leftParsed rightParsed

/-- Exact generic-parameter rejection excludes every successful list. -/
theorem GenericParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : GenericParametersRejects input rejected) :
    ¬ ∃ parameters output, GenericParametersParses input parameters output := by
  rintro ⟨parameters, output, parsed⟩
  exact rejection.disjointNonemptyTrailing identifierDeterministicOutcomeSpec
    (fun successful => successful) ⟨_, output, parsed⟩

/-- Required canonical generic parameters have deterministic and exclusive
ordinary outcomes. -/
theorem genericParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec GenericParametersParses
      GenericParametersRejects where
  successOutputUnique := GenericParametersParses.output_unique
  successRejectDisjoint := GenericParametersRejects.disjointOrdinary

/-- Optional generic-parameter success has one final remainder. -/
theorem OptionalGenericParametersParses.output_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParsed =>
          rcases rightParsed.opening_present with ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent openingPresent)
  | present leftParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases leftParsed.opening_present with ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent openingPresent)
      | present rightParsed =>
          exact leftParsed.output_unique rightParsed

/-- Exact optional-generic rejection excludes absent and present success. -/
theorem OptionalGenericParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalGenericParametersRejects input rejected) :
    ¬ ∃ parameters output,
      OptionalGenericParametersParses input parameters output := by
  rintro ⟨parameters, output, successful⟩
  cases rejection with
  | present openingPresent parametersRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
      | present parametersParsed =>
          exact genericParametersDeterministicOutcomeSpec.successRejectDisjoint
            parametersRejected ⟨_, _, parametersParsed⟩

/-- Optional canonical generic parameters have deterministic and exclusive
ordinary outcomes. -/
theorem optionalGenericParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalGenericParametersParses
      OptionalGenericParametersRejects where
  successOutputUnique := OptionalGenericParametersParses.output_unique
  successRejectDisjoint := OptionalGenericParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParameterCoreOutcomeProperties
/-! Deterministic ordinary outcomes of non-recovering named parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem comptimePrefixAbsent_conflicts_exact
    {input afterMarker afterName : Remainder} {markerSpan : SourceSpan}
    {name : Syntax.Identifier}
    (absent : ComptimeParameterPrefixAbsentAt input)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.comptime.spelling)
      input markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterName) : False := by
  apply absent
  refine ⟨markerSpan, name.span, name.value, markerParsed.1, ?_⟩
  have nameToken := nameParsed.1
  rw [markerParsed.2] at nameToken
  exact nameToken

/-- A named-parameter tail has one deterministic final remainder. -/
theorem FunctionParameterTailOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {leftStart rightStart : SourceSpan}
    {leftMarker rightMarker : Option SourceSpan}
    {leftName rightName : Syntax.Identifier}
    {leftErrorSpan rightErrorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary leftStart
      leftMarker leftName leftErrorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary rightStart
      rightMarker rightName rightErrorSpan input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | typed leftColonSpan leftColon leftType =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          exact typeOutcomes.successOutputUnique leftType rightType
      | typeMissing rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftColon.1)
  | typeMissing leftAbsent =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          exact False.elim
            (absent_conflicts_token leftAbsent rightColon.1)
      | typeMissing => rfl

/-- Non-recovering named-parameter success has one final remainder. -/
theorem FunctionParameterCoreOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | ordinary leftAbsent leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail
      | comptime markerSpan rightMarker rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exact leftAbsent rightMarker
              rightName)
  | comptime markerSpan leftMarker leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exact rightAbsent leftMarker
              leftName)
      | comptime markerSpan rightMarker rightName rightTail =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftTail.output_unique typeOutcomes rightTail

/-- Non-recovering rejection excludes every ordinary Core success. -/
theorem FunctionParameterCoreRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : FunctionParameterCoreRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterCoreOrdinaryParses typeOrdinary input parameter
        output := by
  rintro ⟨parameter, output, parsed⟩
  cases rejection with
  | comptimeType markerSpan colonSpan rejectedMarker rejectedName
        rejectedColon typeRejected =>
      cases parsed with
      | ordinary absent nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent rejectedMarker
            rejectedName
      | comptime successfulMarkerSpan successfulMarker successfulName tail =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          cases tail with
          | typeMissing colonAbsent =>
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed successfulColonSpan successfulColon typeParsed =>
              have afterColonEq := exactToken_output_unique rejectedColon
                successfulColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩
  | ordinaryName absent nameRejected =>
      cases parsed with
      | comptime markerSpan markerParsed nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent markerParsed
            nameParsed
      | ordinary otherAbsent nameParsed tail =>
          exact nameRejected.disjoint ⟨_, _, nameParsed⟩
  | ordinaryType colonSpan absent rejectedName rejectedColon typeRejected =>
      cases parsed with
      | comptime markerSpan markerParsed nameParsed tail =>
          exact comptimePrefixAbsent_conflicts_exact absent markerParsed
            nameParsed
      | ordinary otherAbsent successfulName tail =>
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          cases tail with
          | typeMissing colonAbsent =>
              exact absent_conflicts_token colonAbsent rejectedColon.1
          | typed successfulColonSpan successfulColon typeParsed =>
              have afterColonEq := exactToken_output_unique rejectedColon
                successfulColon
              subst afterColonEq
              exact typeOutcomes.successRejectDisjoint typeRejected
                ⟨_, _, typeParsed⟩

/-- Deterministic ordinary outcomes of non-recovering `namedParameterCore`. -/
theorem functionParameterCoreDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (FunctionParameterCoreOrdinaryParses typeOrdinary)
      (FunctionParameterCoreRejects typeRejects) where
  successOutputUnique := FunctionParameterCoreOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := FunctionParameterCoreRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeProperties
/-! Deterministic ordinary outcomes of parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- The recursive recovery scan has one deterministic remainder. -/
theorem FunctionParameterRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.FunctionParameter}
      {afterLeft afterRight : Remainder},
      FunctionParameterRecoveryScanParses first leftLast input left afterLeft →
      FunctionParameterRecoveryScanParses first rightLast input right afterRight →
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

/-- Complete function-parameter recovery has one deterministic remainder. -/
theorem FunctionParameterRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Lambda retagging preserves the function recovery's unique remainder. -/
theorem LambdaParameterRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Every unavailable-first-token rejection is non-consuming. -/
theorem FunctionParameterRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes recovery rejection. -/
theorem FunctionParameterRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterRecoveryParses input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- The same first-token exclusion applies after lambda retagging. -/
theorem FunctionParameterRecoveryRejects.disjointLambdaParses
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterRecoveryParses input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases parsed with
  | recovered recovered =>
      exact rejection.disjointParses ⟨_, _, recovered⟩

/-- Deterministic ordinary function-parameter recovery outcome. -/
theorem functionParameterRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionParameterRecoveryParses
      FunctionParameterRecoveryRejects where
  successOutputUnique := FunctionParameterRecoveryParses.output_unique
  successRejectDisjoint := FunctionParameterRecoveryRejects.disjointParses

/-- Deterministic ordinary lambda-parameter recovery outcome. -/
theorem lambdaParameterRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LambdaParameterRecoveryParses
      LambdaParameterRecoveryRejects where
  successOutputUnique := LambdaParameterRecoveryParses.output_unique
  successRejectDisjoint :=
    FunctionParameterRecoveryRejects.disjointLambdaParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeProperties
/-! Deterministic ordinary outcomes of the public lambda parameter. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every pre-recovery boundary is also a recovery-scan stop. -/
theorem LambdaParameterBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : LambdaParameterBoundaryStops input) :
    FunctionParameterRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token

/-- Preserved carrier and window make the cursor-only rewind exact. -/
theorem LambdaParameterCoreRejectsWithPreservedWindow.exists_rewind_eq
    {typeRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : LambdaParameterCoreRejectsWithPreservedWindow typeRejects
      input) :
    ∃ failed, LambdaParameterCoreRejects typeRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary success has one deterministic remainder. -/
theorem LambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects input
      left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.output_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes direct and recovered ordinary success. -/
theorem LambdaParameterRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : LambdaParameterRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output := by
  rintro ⟨parameter, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact lambdaParameterRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public rejection retains the original rewound remainder. -/
theorem LambdaParameterRejects.output_eq
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : LambdaParameterRejects typeRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift deterministic type outcomes through Core choice and recovery. -/
theorem lambdaParameterDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses typeOrdinary typeRejects)
      (LambdaParameterRejects typeRejects) where
  successOutputUnique := LambdaParameterOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := LambdaParameterRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParameterPublicOutcomeProperties
/-! Deterministic ordinary outcomes of the public named parameter. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every public pre-recovery boundary is also a recovery-scan stop. -/
theorem FunctionParameterBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : FunctionParameterBoundaryStops input) :
    FunctionParameterRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token

/-- Preserved carrier and window make the cursor-only rewind exact. -/
theorem FunctionParameterCoreRejectsWithPreservedWindow.exists_rewind_eq
    {typeRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : FunctionParameterCoreRejectsWithPreservedWindow typeRejects
      input) :
    ∃ failed, FunctionParameterCoreRejects typeRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public named-parameter success has one deterministic final remainder. -/
theorem FunctionParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.output_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes direct and recovered ordinary success. -/
theorem FunctionParameterRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : FunctionParameterRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output := by
  rintro ⟨parameter, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact functionParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact functionParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact functionParameterRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public named-parameter rejection retains the rewound remainder. -/
theorem FunctionParameterRejects.output_eq
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : FunctionParameterRejects typeRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift deterministic type outcomes through Core choice and recovery. -/
theorem functionParameterDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses typeOrdinary typeRejects)
      (FunctionParameterRejects typeRejects) where
  successOutputUnique := FunctionParameterOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := FunctionParameterRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParameterRecoveryExactnessProperties
/-! Exact values for malformed named-function-parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With fixed first and outer-last spans, a recovery scan fixes its error
parameter and final remainder. -/
theorem FunctionParameterRecoveryScanParses.result_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.FunctionParameter}
      {afterLeft afterRight : Remainder},
      FunctionParameterRecoveryScanParses first last input left afterLeft →
      FunctionParameterRecoveryScanParses first last input right afterRight →
      left = right ∧ afterLeft = afterRight := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => exact ⟨rfl, rfl⟩
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- With fixed first and outer-last spans, a recovery scan fixes its value. -/
theorem FunctionParameterRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : FunctionParameterRecoveryScanParses first last input right
      afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

/-- Complete malformed-parameter recovery fixes its value and remainder. -/
theorem FunctionParameterRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.result_unique rightScan

/-- Complete malformed-parameter recovery fixes its error parameter. -/
theorem FunctionParameterRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- An unavailable recovery first token has one nonconsuming endpoint. -/
theorem FunctionParameterRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionParameterRecoveryRejects input left)
    (rightRejected : FunctionParameterRecoveryRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Standalone malformed-parameter recovery has fully exact outcomes. -/
theorem functionParameterRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionParameterRecoveryParses
      FunctionParameterRecoveryRejects where
  toDeterministicOutcomeSpec :=
    functionParameterRecoveryDeterministicOutcomeSpec
  successValueUnique := FunctionParameterRecoveryParses.value_unique
  rejectOutputUnique := FunctionParameterRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
