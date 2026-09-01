import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.PredicateSequenceProperties
import Solcore.Syntax.Parser.PredicateTotalityProperties

/-! Valid-input totality for canonical predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One canonical predicate has only ordinary outcomes on valid inputs. -/
theorem predicate_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, predicate input = .ok value next) ∨
      (∃ failure next, predicate input = .reject failure next) :=
  predicate_invariantFreeOnValid input inputValid

namespace PredicateInternals

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor) (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/-- More fuel than remaining tokens makes the bare-sequence loop ordinary. -/
theorem barePredicatesTail_ordinary_of_remainingCount_lt
    (first : Predicate) : ∀ fuel last tailRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ values next,
        barePredicatesTail first fuel last tailRev input = .ok values next) ∨
      (∃ failure next,
        barePredicatesTail first fuel last tailRev input =
          .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev input inputValid adequate
      unfold barePredicatesTail
      split
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .typeExpr input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .typeExpr input inputValid
            rw [commaResult] at commaReply
            simp only
            split
            · cases valueResult : predicate afterComma with
              | invariant error =>
                  exact False.elim
                    (predicate_ne_invariant afterComma commaReply.2.1 error
                      valueResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  change
                    (∃ values final,
                      barePredicatesTail first fuel value
                        (value :: tailRev) next = .ok values final) ∨
                    (∃ failure final,
                      barePredicatesTail first fuel value
                        (value :: tailRev) next = .reject failure final)
                  apply inductionHypothesis value (value :: tailRev) next
                  · have valueReply := predicate_validFor afterComma
                      commaReply.2.1
                    rw [valueResult] at valueReply
                    exact valueReply.2.1
                  · have valueReply := predicate_validFor afterComma
                      commaReply.2.1
                    rw [valueResult] at valueReply
                    have commaWindow := symbol_preservesTokenWindow .comma
                      .typeExpr input
                    rw [commaResult] at commaWindow
                    have valueWindow := predicate_preservesTokenWindow afterComma
                    rw [valueResult] at valueWindow
                    exact remainingCount_lt_after_strict_progress valueReply.2.1
                      (valueWindow.2.trans commaWindow.2)
                      (Nat.lt_trans
                        (acceptToken_cursor_lt_onSuccess (.symbol .comma)
                          .typeExpr (· == .symbol .comma) commaResult)
                        (predicate_cursor_lt_onSuccess valueResult)) adequate
            · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inl ⟨_, _, rfl⟩

theorem barePredicatesTail_ne_invariant_of_remainingCount_lt
    (first last : Predicate) (fuel : Nat) (tailRev : List Predicate)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    barePredicatesTail first fuel last tailRev input ≠ .invariant error := by
  intro failed
  rcases barePredicatesTail_ordinary_of_remainingCount_lt first fuel last
      tailRev input inputValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production fuel selected by `barePredicates` is always adequate. -/
theorem barePredicatesTail_production_ordinary (first last : Predicate)
    (tailRev : List Predicate) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      barePredicatesTail first (input.remainingCount + 1) last tailRev input =
        .ok values next) ∨
    (∃ failure next,
      barePredicatesTail first (input.remainingCount + 1) last tailRev input =
        .reject failure next) :=
  barePredicatesTail_ordinary_of_remainingCount_lt first
    (input.remainingCount + 1) last tailRev input inputValid (by omega)

/-- Bare predicate sequences have only ordinary outcomes on valid inputs. -/
theorem barePredicates_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, barePredicates input = .ok values next) ∨
      (∃ failure next, barePredicates input = .reject failure next) := by
  unfold barePredicates
  cases firstResult : predicate input with
  | invariant error =>
      exact False.elim
        (predicate_ne_invariant input inputValid error firstResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      have firstReply := predicate_validFor input inputValid
      rw [firstResult] at firstReply
      exact barePredicatesTail_production_ordinary first first [] next
        firstReply.2.1

theorem barePredicates_invariantFreeOnValid :
    Parser.InvariantFreeOnValid barePredicates :=
  barePredicates_ordinary

theorem barePredicates_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    barePredicates input ≠ .invariant error :=
  barePredicates_invariantFreeOnValid.ne_invariant input inputValid error

/-- Parenthesized predicate sequences discharge their nonempty refinement. -/
theorem groupedPredicates_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, groupedPredicates input = .ok values next) ∨
      (∃ failure next, groupedPredicates input = .reject failure next) := by
  rcases delimited_ordinary .leftParen .rightParen false predicate .typeExpr
      .topLevel predicate_elementTotalityContract input inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · have nonempty := delimited_false_elements_ne_nil_onSuccess .leftParen
      .rightParen predicate .typeExpr .topLevel valuesResult
    cases elements : values.elements with
    | nil => exact False.elim (nonempty elements)
    | cons head tail =>
        exact Or.inl ⟨{
          span := values.span
          elements := { head, tail }
        }, afterValues, by
          simp only [groupedPredicates, bind, valuesResult, elements, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [groupedPredicates, bind, valuesResult]⟩

theorem groupedPredicates_invariantFreeOnValid :
    Parser.InvariantFreeOnValid groupedPredicates :=
  groupedPredicates_ordinary

theorem groupedPredicates_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    groupedPredicates input ≠ .invariant error :=
  groupedPredicates_invariantFreeOnValid.ne_invariant input inputValid error

/-- Predicate-sequence dispatch is ordinary in both grouped and bare forms. -/
theorem predicateSequence_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, predicateSequence input = .ok values next) ∨
      (∃ failure next, predicateSequence input = .reject failure next) := by
  unfold predicateSequence
  split
  · exact Parser.orElse_invariantFreeOnValid
      groupedPredicates_invariantFreeOnValid
      barePredicates_invariantFreeOnValid input inputValid
  · exact barePredicates_ordinary input inputValid

theorem predicateSequence_invariantFreeOnValid :
    Parser.InvariantFreeOnValid predicateSequence :=
  predicateSequence_ordinary

theorem predicateSequence_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    predicateSequence input ≠ .invariant error :=
  predicateSequence_invariantFreeOnValid.ne_invariant input inputValid error

end PredicateInternals
end Solcore.Syntax.Parser
