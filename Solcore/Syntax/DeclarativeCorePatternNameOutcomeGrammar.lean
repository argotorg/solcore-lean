import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeProperties

/-! Ordinary outcomes for the Boolean-first Core pattern name parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Pattern names share the exact Boolean-first ordinary grammar used by
expression names; checked-identifier diagnostics do not alter this shape. -/
abbrev PatternNameOrdinaryParses := ExpressionNameOrdinaryParses

/-- Pattern-name rejection is the same exact three-way token absence. -/
abbrev PatternNameRejects := ExpressionNameRejects

/-- Boolean-first pattern names form a deterministic ordinary outcome. -/
theorem patternNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternNameOrdinaryParses PatternNameRejects :=
  expressionNameDeterministicOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
