import Solcore.Syntax.Internal.TypeExactness
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.BlockExactness
import Solcore.Syntax.Internal.ExpressionAtomOutcomes
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Grammar.TermLevels

/-!
Exactness of the declarative grammar of predicates, parameters, signatures and expression
fuel: outcomes fix the whole result. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateExactnessProperties
/-! Exact successful values and rejection endpoints for predicates. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem predicate_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A predicate success constructs one exact predicate AST. -/
theorem PredicateParses.value_unique
    {input : Remainder} {left right : Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateParses input left afterLeft)
    (rightParsed : PredicateParses input right afterRight) : left = right := by
  cases leftParsed with
  | @parsed leftAfterSubject leftAfterColon leftAfterName _ leftSubjectValue
      leftTraitName leftArgumentsValue leftColonSpan leftSubject leftColon
      leftName leftArguments =>
      cases rightParsed with
      | @parsed rightAfterSubject rightAfterColon rightAfterName _
          rightSubjectValue rightTraitName rightArgumentsValue rightColonSpan
          rightSubject rightColon rightName rightArguments =>
          rcases typeExprExactOutcomeSpec.successResultUnique leftSubject
              rightSubject with ⟨subjectEq, afterSubjectEq⟩
          subst subjectEq
          subst afterSubjectEq
          rcases leftColon.result_unique rightColon with
            ⟨colonSpanEq, afterColonEq⟩
          subst colonSpanEq
          subst afterColonEq
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases leftArguments.result_unique rightArguments with
            ⟨argumentsEq, afterArgumentsEq⟩
          subst argumentsEq
          cases leftArgumentsValue <;> rfl

/-- A predicate success fixes both its AST and final remainder. -/
theorem PredicateParses.result_unique
    {input : Remainder} {left right : Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateParses input left afterLeft)
    (rightParsed : PredicateParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Predicate rejection has one exact first-failing endpoint. -/
theorem PredicateRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PredicateRejects input left)
    (rightRejected : PredicateRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [predicate_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      typeExprExactOutcomeSpec.successOutputUnique,
      typeExprExactOutcomeSpec.successRejectDisjoint,
      typeExprExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      NamedTypeArgumentsRejects.output_unique typeExprExactOutcomeSpec]

/-- Predicates have fully exact ordinary outcomes. -/
theorem predicateExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PredicateParses PredicateRejects where
  toDeterministicOutcomeSpec := predicateDeterministicOutcomeSpec
  successValueUnique := PredicateParses.value_unique
  rejectOutputUnique := PredicateRejects.output_unique

private theorem groupedPredicateListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses .leftParen .rightParen
        PredicateParses)
      (DelimitedListRejects .leftParen .rightParen false true
        PredicateParses PredicateRejects) :=
  nonemptyTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    predicateExactOutcomeSpec

/-- A grouped predicate sequence constructs one exact nonempty list. -/
theorem GroupedPredicateSequenceParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : GroupedPredicateSequenceParses input left afterLeft)
    (rightParsed : GroupedPredicateSequenceParses input right afterRight) :
    left = right := by
  have encodedEq := groupedPredicateListExactOutcomeSpec
    |>.successValueUnique leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp [Syntax.NonemptyList.toList] at encodedEq
                  simp_all

/-- A grouped predicate sequence fixes its value and final remainder. -/
theorem GroupedPredicateSequenceParses.result_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : GroupedPredicateSequenceParses input left afterLeft)
    (rightParsed : GroupedPredicateSequenceParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Grouped predicate rejection has one exact endpoint. -/
theorem GroupedPredicateSequenceRejects.output_unique
    {input left right : Remainder}
    (leftRejected : GroupedPredicateSequenceRejects input left)
    (rightRejected : GroupedPredicateSequenceRejects input right) :
    left = right :=
  groupedPredicateListExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

/-- Grouped predicate sequences have fully exact ordinary outcomes. -/
theorem groupedPredicateSequenceExactOutcomeSpec :
    ExactDeterministicOutcomeSpec GroupedPredicateSequenceParses
      GroupedPredicateSequenceRejects where
  toDeterministicOutcomeSpec :=
    groupedPredicateSequenceDeterministicOutcomeSpec
  successValueUnique := GroupedPredicateSequenceParses.value_unique
  rejectOutputUnique := GroupedPredicateSequenceRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePredicateSequenceExactnessProperties
/-! Exact bare and prioritized predicate-sequence outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem predicateSequence_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem predicateSequence_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  predicateSequence_absent_conflicts_token absent parsed.1

/-- With the preceding span fixed, a bare predicate tail fixes its elements,
final span, and remainder. -/
theorem BarePredicateTailParses.result_unique
    {lastSpan : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses lastSpan input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses lastSpan input right rightFinal
      afterRight) :
    left = right ∧ leftFinal = rightFinal ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right rightFinal afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | trailing rightComma _ =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact leftCommaAbsent
              rightComma)
      | next rightComma _ _ _ =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact leftCommaAbsent
              rightComma)
  | trailing leftComma leftNextAbsent =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact rightCommaAbsent
              leftComma)
      | trailing rightComma rightNextAbsent =>
          rcases leftComma.result_unique rightComma with
            ⟨commaSpanEq, afterCommaEq⟩
          exact ⟨rfl, commaSpanEq, afterCommaEq⟩
      | next rightComma rightNextStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim (leftNextAbsent rightNextStarts)
  | next leftComma leftNextStarts leftPredicate leftTail tailIH =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact rightCommaAbsent
              leftComma)
      | trailing rightComma rightNextAbsent =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim (rightNextAbsent leftNextStarts)
      | next rightComma rightNextStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          rcases predicateExactOutcomeSpec.successResultUnique leftPredicate
              rightPredicate with ⟨predicateEq, afterPredicateEq⟩
          subst predicateEq
          subst afterPredicateEq
          rcases tailIH rightTail with ⟨tailEq, finalEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, finalEq, outputEq⟩

/-- With the preceding span fixed, a bare predicate tail fixes its values. -/
theorem BarePredicateTailParses.value_unique
    {lastSpan : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses lastSpan input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses lastSpan input right rightFinal
      afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

/-- A bare predicate tail has one first rejecting endpoint. -/
theorem BarePredicateTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : BarePredicateTailRejects input left)
    (rightRejected : BarePredicateTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | predicateRejected leftCommaSpan leftComma leftStarts leftPredicate =>
      cases rightRejected with
      | predicateRejected rightCommaSpan rightComma rightStarts
          rightPredicate =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact predicateExactOutcomeSpec.rejectOutputUnique leftPredicate
            rightPredicate
      | next rightCommaSpan rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim
            (predicateExactOutcomeSpec.successRejectDisjoint leftPredicate
              ⟨_, _, rightPredicate⟩)
  | next leftCommaSpan leftComma leftStarts leftPredicate leftTail tailIH =>
      cases rightRejected with
      | predicateRejected rightCommaSpan rightComma rightStarts
          rightPredicate =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim
            (predicateExactOutcomeSpec.successRejectDisjoint rightPredicate
              ⟨_, _, leftPredicate⟩)
      | next rightCommaSpan rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          have afterPredicateEq :=
            predicateExactOutcomeSpec.successOutputUnique leftPredicate
              rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- A complete bare predicate sequence fixes its nonempty AST. -/
theorem BarePredicateSequenceParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateSequenceParses input left afterLeft)
    (rightParsed : BarePredicateSequenceParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftFirst leftTail =>
      cases rightParsed with
      | parsed rightFirst rightTail =>
          rcases predicateExactOutcomeSpec.successResultUnique leftFirst
              rightFirst with ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          rcases leftTail.result_unique rightTail with
            ⟨tailEq, finalSpanEq, outputEq⟩
          subst tailEq
          subst finalSpanEq
          rfl

/-- Bare predicate-sequence rejection has one endpoint. -/
theorem BarePredicateSequenceRejects.output_unique
    {input left right : Remainder}
    (leftRejected : BarePredicateSequenceRejects input left)
    (rightRejected : BarePredicateSequenceRejects input right) :
    left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [predicateExactOutcomeSpec.successOutputUnique,
      predicateExactOutcomeSpec.successRejectDisjoint,
      predicateExactOutcomeSpec.rejectOutputUnique,
      BarePredicateTailRejects.output_unique]

/-- Bare predicate sequences have exact outcomes. -/
theorem barePredicateSequenceExactOutcomeSpec :
    ExactDeterministicOutcomeSpec BarePredicateSequenceParses
      BarePredicateSequenceRejects where
  toDeterministicOutcomeSpec := barePredicateSequenceDeterministicOutcomeSpec
  successValueUnique := BarePredicateSequenceParses.value_unique
  rejectOutputUnique := BarePredicateSequenceRejects.output_unique

/-- Prioritized grouped-or-bare predicate success fixes its AST. -/
theorem PredicateSequenceParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | bare leftUnavailable leftBare =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.successValueUnique
            leftBare rightBare
      | grouped rightGrouped =>
          exact False.elim (leftUnavailable ⟨_, _, rightGrouped⟩)
  | grouped leftGrouped =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact False.elim (rightUnavailable ⟨_, _, leftGrouped⟩)
      | grouped rightGrouped =>
          exact groupedPredicateSequenceExactOutcomeSpec.successValueUnique
            leftGrouped rightGrouped

/-- Prioritized predicate-sequence rejection has one endpoint. -/
theorem PredicateSequenceRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PredicateSequenceRejects input left)
    (rightRejected : PredicateSequenceRejects input right) : left = right := by
  cases leftRejected with
  | direct leftOpeningAbsent leftBare =>
      cases rightRejected with
      | direct rightOpeningAbsent rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftBare rightBare
      | fallback rightOpeningPresent rightGrouped rightBare =>
          rcases rightOpeningPresent with ⟨span, openingToken⟩
          exact False.elim
            (predicateSequence_absent_conflicts_token leftOpeningAbsent
              openingToken)
  | fallback leftOpeningPresent leftGrouped leftBare =>
      cases rightRejected with
      | direct rightOpeningAbsent rightBare =>
          rcases leftOpeningPresent with ⟨span, openingToken⟩
          exact False.elim
            (predicateSequence_absent_conflicts_token rightOpeningAbsent
              openingToken)
      | fallback rightOpeningPresent rightGrouped rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftBare rightBare

/-- Prioritized grouped-or-bare predicate sequences have exact outcomes. -/
theorem predicateSequenceExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PredicateSequenceParses
      PredicateSequenceRejects where
  toDeterministicOutcomeSpec := predicateSequenceDeterministicOutcomeSpec
  successValueUnique := PredicateSequenceParses.value_unique
  rejectOutputUnique := PredicateSequenceRejects.output_unique

/-- A complete prioritized predicate sequence fixes its AST and remainder. -/
theorem PredicateSequenceParses.result_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  predicateSequenceExactOutcomeSpec.successResultUnique leftParsed rightParsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWhereClauseExactnessProperties
/-! Exact values and rejection endpoints for optional `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem where_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An optional `where` clause fixes its absent or present AST value. -/
theorem OptionalWhereClauseParses.value_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightPredicates =>
          exact False.elim
            (where_absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftPredicates =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (where_absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightPredicates =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have predicatesEq :=
            predicateSequenceExactOutcomeSpec.successValueUnique
              leftPredicates rightPredicates
          subst predicatesEq
          rfl

/-- An optional `where` clause fixes its AST and final remainder. -/
theorem OptionalWhereClauseParses.result_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed `where` rejection has one first failing endpoint. -/
theorem OptionalWhereClauseRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalWhereClauseRejects input left)
    (rightRejected : OptionalWhereClauseRejects input right) :
    left = right := by
  cases leftRejected with
  | predicatesRejected _ leftMarker leftPredicates =>
      cases rightRejected with
      | predicatesRejected _ rightMarker rightPredicates =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact predicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftPredicates rightPredicates

/-- Optional `where` clauses have fully exact ordinary outcomes. -/
theorem optionalWhereClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalWhereClauseParses
      OptionalWhereClauseRejects where
  toDeterministicOutcomeSpec := optionalWhereClauseDeterministicOutcomeSpec
  successValueUnique := OptionalWhereClauseParses.value_unique
  rejectOutputUnique := OptionalWhereClauseRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeReturnClauseExactnessProperties
/-! Full value and rejection-endpoint functionality for optional returns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem return_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem returnTypeListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftParen .rightParen TypeExprParses)
      (DelimitedListRejects .leftParen .rightParen true true TypeExprParses
        TypeExprRejects) :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    typeExprExactOutcomeSpec

/-- An optional return clause fixes its absent or present AST value. -/
theorem OptionalReturnClauseParses.value_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightTypes =>
          exact False.elim
            (return_absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftTypes =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (return_absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightTypes =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have typesEq := returnTypeListExactOutcomeSpec.successValueUnique
            leftTypes rightTypes
          subst typesEq
          rfl

/-- An optional return clause fixes its value and final remainder. -/
theorem OptionalReturnClauseParses.result_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed return-clause rejection has one failing endpoint. -/
theorem OptionalReturnClauseRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalReturnClauseRejects input left)
    (rightRejected : OptionalReturnClauseRejects input right) : left = right := by
  cases leftRejected with
  | typesRejected _ leftMarker leftTypes =>
      cases rightRejected with
      | typesRejected _ rightMarker rightTypes =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact returnTypeListExactOutcomeSpec.rejectOutputUnique leftTypes
            rightTypes

/-- Optional return clauses have fully exact ordinary outcomes. -/
theorem optionalReturnClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalReturnClauseParses
      OptionalReturnClauseRejects where
  toDeterministicOutcomeSpec := optionalReturnClauseDeterministicOutcomeSpec
  successValueUnique := OptionalReturnClauseParses.value_unique
  rejectOutputUnique := OptionalReturnClauseRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParameterExactnessProperties
/-! Exact values for recovery-aware named function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem comptimePrefixAbsent_conflicts_exactValue
    {input afterMarker afterName : Remainder} {markerSpan : SourceSpan}
    {name : Syntax.Identifier}
    (absent : ComptimeParameterPrefixAbsentAt input)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.comptime.spelling)
      input markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterName) : False := by
  apply absent
  refine ⟨markerSpan, name.span, name.value, markerParsed.1, ?_⟩
  simpa [markerParsed.2] using nameParsed.1

/-- With fixed accumulated fields, a parameter tail fixes its AST and final
remainder. -/
theorem FunctionParameterTailOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {start : SourceSpan} {marker : Option SourceSpan}
    {name : Syntax.Identifier} {errorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | typed leftColonSpan leftColon leftType =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          rcases leftColon.result_unique rightColon with
            ⟨colonSpanEq, afterColonEq⟩
          subst colonSpanEq
          subst afterColonEq
          rcases typeOutcomes.successResultUnique leftType rightType with
            ⟨typeEq, outputEq⟩
          subst typeEq
          exact ⟨rfl, outputEq⟩
      | typeMissing rightColonAbsent =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightColonAbsent leftColon.1)
  | typeMissing leftColonAbsent =>
      cases rightParsed with
      | typed rightColonSpan rightColon rightType =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftColonAbsent rightColon.1)
      | typeMissing => exact ⟨rfl, rfl⟩

/-- With fixed accumulated fields, a parameter tail fixes its AST. -/
theorem FunctionParameterTailOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {start : SourceSpan} {marker : Option SourceSpan}
    {name : Syntax.Identifier} {errorSpan : SourceSpan}
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input left afterLeft)
    (rightParsed : FunctionParameterTailOrdinaryParses typeOrdinary start
      marker name errorSpan input right afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- Non-recovering named-parameter success fixes its AST and final
remainder. -/
theorem FunctionParameterCoreOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | ordinary leftAbsent leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.result_unique typeOutcomes rightTail
      | comptime markerSpan rightMarker rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exactValue leftAbsent rightMarker
              rightName)
  | comptime markerSpan leftMarker leftName leftTail =>
      cases rightParsed with
      | ordinary rightAbsent rightName rightTail =>
          exact False.elim
            (comptimePrefixAbsent_conflicts_exactValue rightAbsent leftMarker
              leftName)
      | comptime rightMarkerSpan rightMarker rightName rightTail =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          exact leftTail.result_unique typeOutcomes rightTail

/-- Non-recovering named-parameter success fixes its AST. -/
theorem FunctionParameterCoreOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : FunctionParameterCoreOrdinaryParses typeOrdinary input right
      afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- A recovery-aware named parameter fixes its AST and final remainder. -/
theorem FunctionParameterOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.result_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.result_unique rightRecovery

/-- A recovery-aware named parameter fixes its AST. -/
theorem FunctionParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right :=
  (leftParsed.result_unique typeOutcomes rightParsed).1

/-- Public named-parameter rejection has one nonconsuming endpoint. -/
theorem FunctionParameterRejects.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : FunctionParameterRejects typeRejects input left)
    (rightRejected : FunctionParameterRejects typeRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Recovery-aware named parameters preserve exact child outcomes. -/
theorem functionParameterExactOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects) :
    ExactDeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses typeOrdinary typeRejects)
      (FunctionParameterRejects typeRejects) where
  toDeterministicOutcomeSpec :=
    functionParameterDeterministicOutcomeSpec
      typeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := FunctionParameterOrdinaryParses.value_unique
    typeOutcomes
  rejectOutputUnique := FunctionParameterRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties
/-! Exact values for recovery-aware function-parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware function-parameter lists have fully exact outcomes. -/
theorem functionParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionParametersOrdinaryParses
      FunctionParametersRejects :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    (functionParameterExactOutcomeSpec typeExprExactOutcomeSpec)

/-- A complete function-parameter list fixes its AST and final remainder. -/
theorem FunctionParametersOrdinaryParses.result_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  functionParametersExactOutcomeSpec.successResultUnique leftParsed
    rightParsed

/-- A complete function-parameter list fixes its delimited-list AST. -/
theorem FunctionParametersOrdinaryParses.value_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    left = right :=
  functionParametersExactOutcomeSpec.successValueUnique leftParsed
    rightParsed

/-- Function-parameter-list rejection has one exact failing endpoint. -/
theorem FunctionParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionParametersRejects input left)
    (rightRejected : FunctionParametersRejects input right) : left = right :=
  functionParametersExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionSignatureExactnessProperties
/-! Exact values and rejection endpoints for complete function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem signature_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The fixed `public`-then-`payable` sequence fixes its modifier AST. -/
theorem FunctionModifiersParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    left = right := by
  cases left
  cases right
  simp_all only [FunctionModifiersParses]
  rcases leftParsed with ⟨leftAfterPublic, leftPublic, leftPayable⟩
  rcases rightParsed with ⟨rightAfterPublic, rightPublic, rightPayable⟩
  rcases leftPublic.result_unique rightPublic with
    ⟨publicEq, afterPublicEq⟩
  subst publicEq
  subst afterPublicEq
  have payableEq := leftPayable.value_unique rightPayable
  subst payableEq
  rfl

/-- The fixed modifier sequence fixes its AST and final remainder. -/
theorem FunctionModifiersParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A complete function-signature success fixes its AST. -/
theorem FunctionSignatureOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftKeywordSpan leftKeyword leftName leftGenerics leftParameters
      leftModifiers leftReturns leftWhere =>
      cases rightParsed with
      | parsed rightKeywordSpan rightKeyword rightName rightGenerics
          rightParameters rightModifiers rightReturns rightWhere =>
          rcases leftKeyword.result_unique rightKeyword with
            ⟨keywordSpanEq, afterKeywordEq⟩
          subst keywordSpanEq
          subst afterKeywordEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases functionParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨modifiersEq, afterModifiersEq⟩
          subst modifiersEq
          subst afterModifiersEq
          rcases optionalReturnClauseExactOutcomeSpec.successResultUnique
              leftReturns rightReturns with
            ⟨returnsEq, afterReturnsEq⟩
          subst returnsEq
          subst afterReturnsEq
          have whereEq := optionalWhereClauseExactOutcomeSpec
            |>.successValueUnique leftWhere rightWhere
          subst whereEq
          rfl

/-- A complete function-signature success fixes its AST and final remainder. -/
theorem FunctionSignatureOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The six-stage function-signature rejection sequence has one endpoint. -/
theorem FunctionSignatureRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionSignatureRejects input left)
    (rightRejected : FunctionSignatureRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [signature_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      functionParametersExactOutcomeSpec.successOutputUnique,
      functionParametersExactOutcomeSpec.successRejectDisjoint,
      functionParametersExactOutcomeSpec.rejectOutputUnique,
      FunctionModifiersParses.output_unique,
      optionalReturnClauseExactOutcomeSpec.successOutputUnique,
      optionalReturnClauseExactOutcomeSpec.successRejectDisjoint,
      optionalReturnClauseExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique]

/-- Complete recovery-aware function signatures have exact outcomes. -/
theorem functionSignatureExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionSignatureOrdinaryParses
      FunctionSignatureRejects where
  toDeterministicOutcomeSpec := functionSignatureDeterministicOutcomeSpec
  successValueUnique := FunctionSignatureOrdinaryParses.value_unique
  rejectOutputUnique := FunctionSignatureRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterExactnessProperties
/-! Exact outcomes for recovery-aware ordinary lambda parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lambda recovery preserves the unique span of malformed named recovery. -/
theorem LambdaParameterRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          have parameterEq := leftRecovery.value_unique rightRecovery
          subst parameterEq
          rfl

/-- Complete lambda recovery fixes its error AST and final remainder. -/
theorem LambdaParameterRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Retagging named-parameter recovery gives exact lambda recovery outcomes. -/
theorem lambdaParameterRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LambdaParameterRecoveryParses
      LambdaParameterRecoveryRejects where
  toDeterministicOutcomeSpec := lambdaParameterRecoveryDeterministicOutcomeSpec
  successValueUnique := LambdaParameterRecoveryParses.value_unique
  rejectOutputUnique := FunctionParameterRecoveryRejects.output_unique

/-- Exact type outcomes make direct and recovered lambda values unique. -/
theorem LambdaParameterOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.value_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec
              typeOutcomes.toDeterministicOutcomeSpec
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.value_unique rightRecovery

/-- Recovery-aware lambda success fixes the complete AST and remainder. -/
theorem LambdaParameterOrdinaryParses.result_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique typeOutcomes rightParsed,
    leftParsed.output_unique typeOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- Every public lambda rejection has the same nonconsuming endpoint. -/
theorem LambdaParameterRejects.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : LambdaParameterRejects typeRejects input left)
    (rightRejected : LambdaParameterRejects typeRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact type outcomes lift through ordinary lambda parameters and recovery. -/
theorem lambdaParameterExactOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects) :
    ExactDeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses typeOrdinary typeRejects)
      (LambdaParameterRejects typeRejects) where
  toDeterministicOutcomeSpec := lambdaParameterDeterministicOutcomeSpec
    typeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := LambdaParameterOrdinaryParses.value_unique typeOutcomes
  rejectOutputUnique := LambdaParameterRejects.output_unique

/-- Public recursive Core types discharge every lambda-parameter premise. -/
theorem lambdaParameterPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (LambdaParameterRejects TypeExprRejects) :=
  lambdaParameterExactOutcomeSpec typeExprExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomExactnessProperties
/-! Exact public Core atoms, including fixed-previous-fuel lambda bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested expressions, parameters, types, and bodies fix all public atom
outcomes, including transactional rewind and diagnosed recovery. -/
theorem coreExpressionAtomExactOutcomeSpec (relations : CoreExpressionStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    ExactDeterministicOutcomeSpec relations.atomOrdinary relations.atomRejects :=
  expressionAtomExactOutcomeSpecOfSuccess
    (expressionAtomCoreDeterministicOutcomeSpec nestedOutcomes.toDeterministicOutcomeSpec
      parameterOutcomes.toDeterministicOutcomeSpec typeOutcomes.toDeterministicOutcomeSpec
      blockOutcomes.toDeterministicOutcomeSpec)
    (ExpressionAtomCoreOrdinaryParses.value_unique nestedOutcomes parameterOutcomes
      typeOutcomes blockOutcomes)

/-- Only expression and statement outcomes at the preceding fuel are needed
for the next step's atom grammar; no successor-level outcome is assumed. -/
theorem coreExpressionAtomExactOutcomeSpecWithFuel (fuel : Nat)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel) (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel) (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (coreExpressionStepRelationsWithFuel fuel).atomOrdinary
      (coreExpressionStepRelationsWithFuel fuel).atomRejects :=
  coreExpressionAtomExactOutcomeSpec (coreExpressionStepRelationsWithFuel fuel)
    expressionOutcomes lambdaParameterPublicExactOutcomeSpec typeExprExactOutcomeSpec
    (isolatedCoreBlockExactOutcomeSpec (coreBlockExactOutcomeSpec .require statementOutcomes))

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionStepExactnessProperties
/-! Full exactness of a complete Core expression step over exact children. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child outcomes compose through atom priority, recovery, postfix
extension, and the entire operator stack without stronger rejection premises. -/
theorem coreExpressionStepExactOutcomeSpec (relations : CoreExpressionStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    ExactDeterministicOutcomeSpec (CoreExpressionStepOrdinaryParses relations)
      (CoreExpressionStepRejects relations) :=
  expressionLayerExactOutcomeSpec nestedOutcomes
    (expressionPostfixExactOutcomeSpec
      (coreExpressionAtomExactOutcomeSpec relations nestedOutcomes
        parameterOutcomes typeOutcomes blockOutcomes) nestedOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionFuelExactnessProperties
/-! Base and successor exactness for mutually recursive Core expression fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero has neither an ordinary expression success nor rejection. -/
theorem coreExpressionExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel 0)
      (CoreExpressionRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := coreExpressionOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CoreExpressionOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CoreExpressionRejectsWithFuel.zero leftRejected)

/-- Exact expressions and statements at one preceding fuel yield the next
expression layer. Types and lambda parameters need no recursive assumption. -/
theorem coreExpressionExactOutcomeSpecWithFuel_succ (fuel : Nat)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel) (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel) (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel (fuel + 1))
      (CoreExpressionRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (CoreExpressionStepOrdinaryParses (coreExpressionStepRelationsWithFuel fuel))
    (CoreExpressionStepRejects (coreExpressionStepRelationsWithFuel fuel))
  exact coreExpressionStepExactOutcomeSpec (coreExpressionStepRelationsWithFuel fuel)
    expressionOutcomes lambdaParameterPublicExactOutcomeSpec typeExprExactOutcomeSpec
    (isolatedCoreBlockExactOutcomeSpec (coreBlockExactOutcomeSpec .require statementOutcomes))

end Solcore.Syntax.DeclarativeGrammar
end
