import Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Executable reflection of the public parameter recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .parameter present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .parameter parsed).1⟩

/-- A true executable public-boundary guard gives its exact stop. -/
theorem lambdaParameterBoundaryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = true) :
    DeclarativeGrammar.LambdaParameterBoundaryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · rcases tokenAt_of_isSymbol_eq_true .comma comma with
        ⟨span, token⟩
      exact .comma token
    · have commaFalse := Bool.eq_false_iff.mpr comma
      have rightParen : isSymbol input .rightParen = true := by
        simpa [atEndFalse, commaFalse] using boundary
      rcases tokenAt_of_isSymbol_eq_true .rightParen rightParen with
        ⟨span, token⟩
      exact .rightParen token

/-- A false executable guard excludes every public parameter boundary. -/
theorem no_lambdaParameterBoundaryStops_of_guard_eq_false
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = false) :
    ¬ DeclarativeGrammar.LambdaParameterBoundaryStops
      input.declarativeRemainder := by
  intro stops
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundary
  | comma present =>
      have comma : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [comma] at boundary
  | rightParen present =>
      have rightParen : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [rightParen] at boundary

end Solcore.Syntax.Parser
