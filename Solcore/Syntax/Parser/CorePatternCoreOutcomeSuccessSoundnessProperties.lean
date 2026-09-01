import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeGrammar
import Solcore.Syntax.Parser.CorePatternCoreOutcomeLeafSoundnessProperties
import Solcore.Syntax.Parser.CorePatternCoreOutcomePrimitiveProperties

/-! Generic ordinary-success reflection for the ordered `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable success records the selected branch and all earlier
failed guards.  The four recursive branch grammars are supplied by callbacks. -/
theorem patternCore_success_ordinary_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        parenthesizedPattern nested input = .ok pattern output →
          parenthesizedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (dotConstructorSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        dotConstructorPattern nested input = .ok pattern output →
          dotConstructorOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (comptimeSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        comptimePattern expression input = .ok pattern output →
          comptimeOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (qualifiedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        qualifiedPattern nested input = .ok pattern output →
          qualifiedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : patternCore nested expression input = .ok pattern output) :
    DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    rcases symbolTokenAt_of_isSymbol_eq_true .underscore underscorePresent
      with ⟨span, marker⟩
    exact .selected (.wildcard marker)
      (.wildcard (wildcardPattern_success_sound result))
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      have starts := coreLiteralStartsAt_of_isCoreLiteral_eq_true
        literalPresent
      exact .selected (.literal noUnderscore starts)
        (.literal (literalPattern_success_sound result))
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        have starts := booleanPatternStartsAt_of_isBooleanValue_eq_true
          booleanPresent
        exact .selected (.boolean noUnderscore noLiteral starts)
          (.boolean (booleanBinderPattern_success_sound result))
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
            (.parenthesized (parenthesizedSuccessSound result))
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
              (.dotConstructor (dotConstructorSuccessSound result))
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
                (.comptime (comptimeSuccessSound result))
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
                  (.qualified (qualifiedSuccessSound result))
              next identifierAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.PatternInternals
