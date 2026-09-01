import Solcore.Syntax.DeclarativeCorePatternPublicOutcomeProperties
import Solcore.Syntax.Parser.CorePatternRecoveryOrdinarySoundnessProperties

/-! Executable lookahead bridges for the public Core pattern boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem peek?_eq_some_of_tokenAt {input : State} {token : Token}
    (present : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor token) : input.peek? = some token := by
  unfold State.peek?
  simp only [present.1, ↓reduceIte, present.2]

/-- A true executable pre-recovery guard gives its exact declarative
boundary. -/
theorem patternBoundaryStops_of_isPatternBoundary
    (input : State) (boundary : isPatternBoundary input = true) :
    DeclarativeGrammar.PatternBoundaryStops input.declarativeRemainder := by
  have stops := patternRecoveryStops_of_isPatternBoundary input boundary
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | rightBrace token => exact .rightBrace token
  | missingToken inside missing =>
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = none at missing
      have atEndFalse : input.atEnd = false := by
        unfold State.atEnd
        exact decide_eq_false (by omega)
      have found : input.peek? = none := by
        unfold State.peek?
        simp only [inside, ↓reduceIte, missing]
      simp [isPatternBoundary, atEndFalse, isSymbol, State.peekKind?, found]
        at boundary

/-- A false executable pre-recovery guard excludes every declarative
boundary. -/
theorem no_patternBoundaryStops_of_isPatternBoundary_eq_false
    (input : State) (boundary : isPatternBoundary input = false) :
    ¬ DeclarativeGrammar.PatternBoundaryStops
      input.declarativeRemainder := by
  intro stops
  have recoveryStop := stops.toRecoveryStop
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [isPatternBoundary, atEndTrue] at boundary
  | comma token
  | rightParen token
  | fatArrow token
  | pipe token
  | rightBrace token =>
      have found := peek?_eq_some_of_tokenAt (by
        simpa [State.declarativeRemainder] using token)
      exact no_patternRecoveryStops_of_nonBoundary_token boundary found
        recoveryStop

end Solcore.Syntax.Parser.PatternInternals
