import Solcore.Syntax.Parser.CorePatternCoreOutcomeSuccessSoundnessProperties

/-! Generic exact ordinary-rejection reflection for `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable rejection is either the exact selected recursive-branch
rejection or the final non-consuming dispatcher rejection. -/
theorem patternCore_reject_ordinary_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        parenthesizedPattern nested input = .reject failure rejected →
          parenthesizedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (dotConstructorRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        dotConstructorPattern nested input = .reject failure rejected →
          dotConstructorRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (comptimeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        comptimePattern expression input = .reject failure rejected →
          comptimeRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (qualifiedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        qualifiedPattern nested input = .reject failure rejected →
          qualifiedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : patternCore nested expression input =
      .reject failure rejected) :
    DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    exact False.elim
      (wildcardPattern_ne_reject_of_isSymbol_eq_true underscorePresent result)
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      exact False.elim
        (literalPattern_ne_reject_of_isCoreLiteral_eq_true literalPresent
          result)
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        exact False.elim
          (booleanBinderPattern_ne_reject_of_isBooleanValue_eq_true
            booleanPresent result)
      next booleanAbsent =>
        have noBoolean :=
          not_booleanPatternStartsAt_of_isBooleanValue_eq_false
            (Bool.eq_false_iff.mpr booleanAbsent)
        split at result
        next leftParenPresent =>
          rcases symbolTokenAt_of_isSymbol_eq_true .leftParen
              leftParenPresent with ⟨span, marker⟩
          exact .selected
            (.parenthesized noUnderscore noLiteral noBoolean marker)
            (.parenthesized (parenthesizedRejectSound result))
        next leftParenAbsent =>
          have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            (Bool.eq_false_iff.mpr leftParenAbsent)
          split at result
          next dotPresent =>
            rcases symbolTokenAt_of_isSymbol_eq_true .dot dotPresent with
              ⟨span, marker⟩
            exact .selected
              (.dotConstructor noUnderscore noLiteral noBoolean noLeftParen
                marker)
              (.dotConstructor (dotConstructorRejectSound result))
          next dotAbsent =>
            have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot
              (Bool.eq_false_iff.mpr dotAbsent)
            split at result
            next comptimePresent =>
              rcases contextualTokenAt_of_isContextual_eq_true .comptime
                  comptimePresent with ⟨span, marker⟩
              exact .selected
                (.comptime noUnderscore noLiteral noBoolean noLeftParen
                  noDot marker)
                (.comptime (comptimeRejectSound result))
            next comptimeAbsent =>
              have noComptime := contextualAbsentAt_of_isContextual_eq_false
                .comptime (Bool.eq_false_iff.mpr comptimeAbsent)
              split at result
              next identifierPresent =>
                rcases identifierPresentAt_of_isIdentifier_eq_true
                    identifierPresent with ⟨span, spelling, marker⟩
                exact .selected
                  (.qualified noUnderscore noLiteral noBoolean noLeftParen
                    noDot noComptime marker)
                  (.qualified (qualifiedRejectSound result))
              next identifierAbsent =>
                have noIdentifier := identifierAbsentAt_of_isIdentifier_eq_false
                  (Bool.eq_false_iff.mpr identifierAbsent)
                unfold rejectAt at result
                cases result
                exact .final (.final noUnderscore noLiteral noBoolean
                  noLeftParen noDot noComptime noIdentifier)

end Solcore.Syntax.Parser.PatternInternals
