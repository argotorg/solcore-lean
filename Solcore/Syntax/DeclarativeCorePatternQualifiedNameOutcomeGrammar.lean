import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties

/-! Ordinary outcomes for qualified names used by Core patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive pattern paths use the exact maximal qualified-name
grammar without the clean checked-identifier side condition. -/
abbrev PatternQualifiedNameOrdinaryParses := QualifiedNameParses

/-- Qualified pattern paths reuse the context-independent exact dotted-name
rejection trace. -/
abbrev PatternQualifiedNameRejects := TypeQualifiedNameRejects

/-- Qualified pattern paths have deterministic ordinary outcomes. -/
theorem patternQualifiedNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternQualifiedNameOrdinaryParses
      PatternQualifiedNameRejects where
  successOutputUnique := QualifiedNameParses.output_unique
  successRejectDisjoint := TypeQualifiedNameRejects.disjointQualified

end Solcore.Syntax.DeclarativeGrammar
