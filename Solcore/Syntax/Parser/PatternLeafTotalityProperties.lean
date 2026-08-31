import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.LiteralTotalityProperties
import Solcore.Syntax.Parser.PatternProperties

/-! Totality for non-recursive pattern leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

theorem wildcardPattern_ordinary : Parser.Ordinary wildcardPattern := by
  intro input
  rcases (symbol_ordinary .underscore .pattern) input with
    ⟨marker, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := marker.span
        value := .wildcard marker.span
      }, next, by simp only [wildcardPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [wildcardPattern, bind, result]⟩

theorem wildcardPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid wildcardPattern :=
  wildcardPattern_ordinary.invariantFreeOnValid

theorem wildcardPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    wildcardPattern input ≠ .invariant error :=
  wildcardPattern_ordinary.ne_invariant input error

theorem literalPattern_ordinary : Parser.Ordinary literalPattern := by
  intro input
  rcases coreLiteral_ordinary input with
    ⟨literal, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := literal.span
        value := .literal literal
      }, next, by simp only [literalPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [literalPattern, bind, result]⟩

theorem literalPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid literalPattern :=
  literalPattern_ordinary.invariantFreeOnValid

theorem literalPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    literalPattern input ≠ .invariant error :=
  literalPattern_ordinary.ne_invariant input error

theorem booleanBinderPattern_ordinary :
    Parser.Ordinary booleanBinderPattern := by
  intro input
  rcases booleanIdentifier_ordinary input with
    ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · exact Or.inl ⟨{
        span := name.span
        value := .binder name
      }, next, by simp only [booleanBinderPattern, bind, result, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [booleanBinderPattern, bind, result]⟩

theorem booleanBinderPattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid booleanBinderPattern :=
  booleanBinderPattern_ordinary.invariantFreeOnValid

theorem booleanBinderPattern_ne_invariant (input : State)
    (error : ParserInvariantError) :
    booleanBinderPattern input ≠ .invariant error :=
  booleanBinderPattern_ordinary.ne_invariant input error

theorem patternName_ordinary : Parser.Ordinary patternName := by
  intro input
  unfold patternName
  split
  · exact booleanIdentifier_ordinary input
  · exact identifier_ordinary .pattern input

theorem patternName_invariantFreeOnValid :
    Parser.InvariantFreeOnValid patternName :=
  patternName_ordinary.invariantFreeOnValid

theorem patternName_ne_invariant (input : State)
    (error : ParserInvariantError) :
    patternName input ≠ .invariant error :=
  patternName_ordinary.ne_invariant input error

theorem patternName_elementTotalityContract :
    ElementTotalityContract patternName := {
  validFor := patternName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := patternName_preservesTokenWindow
  cursorLtOnSuccess := patternName_cursor_lt_onSuccess
  invariantFree := fun input _ error => patternName_ne_invariant input error
}

/-- Comptime leaves add no invariant beyond the supplied expression parser. -/
theorem comptimePattern_invariantFreeOnValid (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid (comptimePattern expression) := by
  intro input inputValid
  rcases (contextual_ordinary .comptime .pattern) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := contextual_validFor .comptime .pattern input inputValid
    rw [markerResult] at markerValid
    have expressionFree := Parser.invariantFreeOnValid_of_ne_invariant
      expressionContract.invariantFree
    rcases expressionFree afterMarker markerValid.2.1 with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        }, next, by
          simp only [comptimePattern, markerResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [comptimePattern, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [comptimePattern, markerResult]⟩

theorem comptimePattern_ordinary (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor) :
    (∃ pattern next, comptimePattern expression input = .ok pattern next) ∨
    (∃ failure next,
      comptimePattern expression input = .reject failure next) :=
  comptimePattern_invariantFreeOnValid expression expressionContract
    input inputValid

theorem comptimePattern_ne_invariant (expression : Parser Expr)
    (expressionContract : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    comptimePattern expression input ≠ .invariant error :=
  (comptimePattern_invariantFreeOnValid expression expressionContract)
    |>.ne_invariant input inputValid error

end Solcore.Syntax.Parser.PatternInternals
