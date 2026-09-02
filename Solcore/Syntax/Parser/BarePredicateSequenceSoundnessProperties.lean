import Solcore.Syntax.Parser.PredicateSequenceProperties
import Solcore.Syntax.Parser.PredicateSoundnessProperties

/-! Success soundness for unparenthesized predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem typeExprStartsAt_of_isKeyword_function
    {input : State} (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword .functionKw) = true at present
      have parsed : keyword .functionKw .typeExpr input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold keyword acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, .keyword .functionKw,
        (keyword_ok_tokenAt .functionKw .typeExpr parsed).1, .function⟩

private theorem typeExprStartsAt_of_isSymbol
    (symbol : Symbol) (starts : DeclarativeGrammar.TypeExprStartToken
      (.symbol symbol)) {input : State}
    (present : isSymbol input symbol = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol symbol) = true at present
      have parsed : Solcore.Syntax.Parser.symbol symbol .typeExpr input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold Solcore.Syntax.Parser.symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, .symbol symbol,
        (symbol_ok_tokenAt symbol .typeExpr parsed).1, starts⟩

private theorem typeExprStartsAt_of_isIdentifier {input : State}
    (present : isIdentifier input = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isIdentifier State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      cases kindEq : token.value <;> simp [kindEq] at present
      case identifier text =>
        have tokenEq : token = {
            span := token.span
            value := .identifier text
          } := by
          rcases token with ⟨span, kind⟩
          simp only at kindEq ⊢
          subst kind
          rfl
        have tokenAt := tokenAt_of_peek?_eq_some found
        rw [tokenEq] at tokenAt
        exact ⟨token.span, .identifier text, tokenAt, .identifier text⟩

/-- Positive executable type lookahead is exact declarative start evidence. -/
theorem typeExprStartsAt_of_startsTypeExpr_eq_true {input : State}
    (present : startsTypeExpr input = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  simp only [startsTypeExpr, Bool.or_eq_true] at present
  rcases present with left | identifierPresent
  · rcases left with left | tuplePresent
    · rcases left with functionPresent | proxyPresent
      · exact typeExprStartsAt_of_isKeyword_function functionPresent
      · exact typeExprStartsAt_of_isSymbol .at .proxy proxyPresent
    · exact typeExprStartsAt_of_isSymbol .leftParen .tuple tuplePresent
  · exact typeExprStartsAt_of_isIdentifier identifierPresent

private theorem startsTypeExpr_eq_true_of_typeExprStartsAt {input : State}
    (present : DeclarativeGrammar.TypeExprStartsAt
      input.declarativeRemainder) : startsTypeExpr input = true := by
  rcases present with ⟨span, kind, tokenAt, starts⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at tokenAt
  have found : input.peek? = some { span, value := kind } := by
    unfold State.peek?
    simp only [tokenAt.1, ↓reduceIte, tokenAt.2]
  cases starts <;>
    (unfold startsTypeExpr isKeyword isSymbol isIdentifier State.peekKind?
     rw [found]
     rfl)

private theorem typeExprAbsentAt_of_startsTypeExpr_eq_false {input : State}
    (absent : startsTypeExpr input = false) :
    DeclarativeGrammar.TypeExprAbsentAt input.declarativeRemainder := by
  intro present
  have contradictory := startsTypeExpr_eq_true_of_typeExprStartsAt present
  rw [absent] at contradictory
  contradiction

private theorem barePredicatesTail_success_sound_strong
    (first : Predicate) : ∀ fuel last tailRev input values next,
      barePredicatesTail first fuel last tailRev input = .ok values next →
      ∃ suffix finalSpan,
        values = {
          span := SourceSpan.cover first.span finalSpan
          elements := {
            head := first
            tail := tailRev.reverse ++ suffix
          }
        } ∧
        DeclarativeGrammar.BarePredicateTailParses last.span
          input.declarativeRemainder suffix finalSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input values next result
      simp [barePredicatesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input values next result
      unfold barePredicatesTail at result
      split at result
      · rename_i commaPresent
        cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaGrammar := symbol_success_exactTokenParses .comma
              .typeExpr commaResult
            split at result
            · rename_i typePresent
              cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at result
              | reject failure rejected => simp [predicateResult] at result
              | ok value afterPredicate =>
                  simp only [predicateResult] at result
                  rcases inductionHypothesis value (value :: tailRev)
                      afterPredicate values next result with
                    ⟨suffix, finalSpan, valuesEq, tailGrammar⟩
                  refine ⟨value :: suffix, finalSpan, ?_,
                    .next commaGrammar
                      (typeExprStartsAt_of_startsTypeExpr_eq_true typePresent)
                      (predicate_success_sound predicateResult) tailGrammar⟩
                  rw [valuesEq]
                  simp [List.reverse_cons, List.append_assoc]
            · rename_i typeAbsent
              cases result
              refine ⟨[], comma.span, by simp, .trailing commaGrammar ?_⟩
              exact typeExprAbsentAt_of_startsTypeExpr_eq_false
                (Bool.eq_false_iff.mpr typeAbsent)
      · rename_i commaAbsent
        cases result
        refine ⟨[], last.span, by simp,
          .done (symbolAbsentAt_of_isSymbol_eq_false .comma ?_)⟩
        exact Bool.eq_false_iff.mpr commaAbsent

/-- Every successful bare sequence follows its exact retained grammar. -/
theorem barePredicates_success_sound {input next : State}
    {values : PredicateSequence}
    (result : barePredicates input = .ok values next) :
    DeclarativeGrammar.BarePredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold barePredicates at result
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases barePredicatesTail_success_sound_strong first
          (afterFirst.remainingCount + 1) first [] afterFirst values next
          result with ⟨rest, finalSpan, valuesEq, tailGrammar⟩
      rw [valuesEq]
      simpa using DeclarativeGrammar.BarePredicateSequenceParses.parsed
        (predicate_success_sound firstResult) tailGrammar

/-- Bare sequence grammar soundness composes with source validity. -/
theorem barePredicates_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : barePredicates input = .ok values next) :
    DeclarativeGrammar.BarePredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨barePredicates_success_sound result, ?_⟩
  have valid := barePredicates_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
