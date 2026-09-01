import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionAtomRecoveryOrdinarySoundnessProperties

/-! Executable lookahead bridges for the public Core atom recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem peek?_eq_some_of_tokenAt {input : State} {token : Token}
    (present : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor token) : input.peek? = some token := by
  unfold State.peek?
  simp only [present.1, ↓reduceIte, present.2]

/-- A true executable pre-recovery guard gives its exact declarative
boundary. -/
theorem expressionAtomBoundaryStops_of_isAtomBoundary
    (input : State) (boundary : isAtomBoundary input = true) :
    DeclarativeGrammar.ExpressionAtomBoundaryStops
      input.declarativeRemainder := by
  have stops := expressionAtomRecoveryStops_of_isAtomBoundary input boundary
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | rightBracket token => exact .rightBracket token
  | rightBrace token => exact .rightBrace token
  | question token => exact .question token
  | colon token => exact .colon token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | elseKeyword token => exact .elseKeyword token
  | missingToken inside missing =>
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = none at missing
      have atEndFalse : input.atEnd = false := by
        unfold State.atEnd
        exact decide_eq_false (by omega)
      have found : input.peek? = none := by
        unfold State.peek?
        simp only [inside, ↓reduceIte, missing]
      simp [isAtomBoundary, atEndFalse, isSymbol, isKeyword,
        State.peekKind?, found] at boundary

/-- A false executable pre-recovery guard excludes every declarative
boundary. -/
theorem no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false
    (input : State) (boundary : isAtomBoundary input = false) :
    ¬ DeclarativeGrammar.ExpressionAtomBoundaryStops
      input.declarativeRemainder := by
  intro stops
  have recoveryStop := stops.toRecoveryStop
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [isAtomBoundary, atEndTrue] at boundary
  | semicolon token
  | comma token
  | rightParen token
  | rightBracket token
  | rightBrace token
  | question token
  | colon token
  | fatArrow token
  | pipe token
  | elseKeyword token =>
      have found := peek?_eq_some_of_tokenAt (by
        simpa [State.declarativeRemainder] using token)
      exact no_expressionAtomRecoveryStops_of_nonBoundary_token boundary found
        recoveryStop

end Solcore.Syntax.Parser.ExpressionAtomInternals
