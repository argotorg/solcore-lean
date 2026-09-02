import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativePredicateOutcomeProperties

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
