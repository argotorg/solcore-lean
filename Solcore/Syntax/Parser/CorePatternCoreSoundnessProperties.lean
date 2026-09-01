import Solcore.Syntax.Parser.CoreExpressionAtomDispatcherLookaheadProperties
import Solcore.Syntax.Parser.CorePatternBasicSoundnessProperties
import Solcore.Syntax.Parser.CorePatternComptimeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternConstructorSoundnessProperties
import Solcore.Syntax.Parser.CorePatternDispatcherLookaheadProperties

/-!
Diagnostic reflection and exact ordered soundness for the non-recovering Core
pattern dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- The Core dispatcher reflects through whichever prioritized branch wins. -/
theorem patternCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (patternCore nested expression) := by
  intro input value next result diagnosticFree
  unfold patternCore at result
  split at result
  · exact wildcardPattern_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  · split at result
    · exact literalPattern_reflectsDiagnosticFreeOnSuccess input value next
        result diagnosticFree
    · split at result
      · exact booleanBinderPattern_reflectsDiagnosticFreeOnSuccess input
          value next result diagnosticFree
      · split at result
        · exact parenthesizedPattern_reflectsDiagnosticFreeOnSuccess nested
            nestedReflects input value next result diagnosticFree
        · split at result
          · exact dotConstructorPattern_reflectsDiagnosticFreeOnSuccess
              nested nestedReflects input value next result diagnosticFree
          · split at result
            · exact comptimePattern_reflectsDiagnosticFreeOnSuccess
                expression expressionReflects input value next result
                  diagnosticFree
            · split at result
              · exact qualifiedPattern_reflectsDiagnosticFreeOnSuccess
                  nested nestedReflects input value next result diagnosticFree
              · simp [rejectAt] at result

/--
Every diagnostic-free Core dispatcher success follows its exact independent
branch and carries evidence excluding every earlier executable guard.
-/
theorem patternCore_success_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternCore nested expression input = .ok value next) :
    DeclarativeGrammar.PatternCoreParses nestedParses expressionParses
      fallback input.declarativeRemainder value next.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    exact .wildcard (wildcardPattern_success_sound result)
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      exact .literal noUnderscore (literalPattern_success_sound result)
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        exact .boolean noUnderscore noLiteral
          (booleanBinderPattern_success_sound result)
      next booleanAbsent =>
        have noBoolean :=
          not_booleanPatternStartsAt_of_isBooleanValue_eq_false
            (Bool.eq_false_iff.mpr booleanAbsent)
        split at result
        next leftParenPresent =>
          exact .parenthesized noUnderscore noLiteral noBoolean
            (parenthesizedPattern_success_sound nested nestedParses
              nestedReflects nestedSound diagnosticFree result)
        next leftParenAbsent =>
          have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            (Bool.eq_false_iff.mpr leftParenAbsent)
          split at result
          next dotPresent =>
            exact .dotConstructor noUnderscore noLiteral noBoolean noLeftParen
              (dotConstructorPattern_success_sound nested nestedParses
                fallback argumentsRejectionSound nestedReflects nestedSound
                  nestedShape diagnosticFree result)
          next dotAbsent =>
            have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot
              (Bool.eq_false_iff.mpr dotAbsent)
            split at result
            next comptimePresent =>
              exact .comptime noUnderscore noLiteral noBoolean noLeftParen
                noDot (comptimePattern_success_sound expression
                  expressionParses expressionSound diagnosticFree result)
            next comptimeAbsent =>
              have noComptime := contextualAbsentAt_of_isContextual_eq_false
                .comptime (Bool.eq_false_iff.mpr comptimeAbsent)
              split at result
              next identifierPresent =>
                exact .qualified noUnderscore noLiteral noBoolean noLeftParen
                  noDot noComptime
                    (qualifiedPattern_success_sound nested nestedParses
                      fallback argumentsRejectionSound nestedReflects
                        nestedSound nestedShape diagnosticFree result)
              next identifierAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.PatternInternals
