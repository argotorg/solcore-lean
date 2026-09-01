import Solcore.Syntax.Parser.NamedParameterTotalityProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties
import Solcore.Syntax.Parser.Signature

/-! Totality for reusable function-signature leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem functionParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, functionParameters input = .ok values next) ∨
      (∃ failure next,
        functionParameters input = .reject failure next) := by
  simpa only [functionParameters] using
    delimited_ordinary .leftParen .rightParen true namedParameter
      .parameter .topLevel namedParameter_elementTotalityContract
      input inputValid

theorem functionParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid functionParameters :=
  functionParameters_ordinary

theorem functionParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionParameters input ≠ .invariant error :=
  functionParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- Optional modifier selection is total whether its keyword is present or not. -/
theorem optionalFunctionModifier_ordinary
    (keywordValue : HardKeyword)
    (input : State) (_inputValid : input.ValidFor) :
    (∃ value next,
      optionalFunctionModifier keywordValue input = .ok value next) ∨
      (∃ failure next,
        optionalFunctionModifier keywordValue input = .reject failure next) := by
  by_cases present : isKeyword input keywordValue
  · rcases (keyword_ordinary keywordValue .parameter) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨some marker.span, next, by
        simp only [optionalFunctionModifier, getState, bind, present,
          ↓reduceIte, markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalFunctionModifier, getState, bind, present,
          ↓reduceIte, markerResult]⟩
  · have absent : isKeyword input keywordValue = false := by
      cases found : isKeyword input keywordValue with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalFunctionModifier, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalFunctionModifier_invariantFreeOnValid
    (keywordValue : HardKeyword) :
    Parser.InvariantFreeOnValid (optionalFunctionModifier keywordValue) :=
  optionalFunctionModifier_ordinary keywordValue

theorem optionalFunctionModifier_ne_invariant
    (keywordValue : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalFunctionModifier keywordValue input ≠ .invariant error :=
  (optionalFunctionModifier_invariantFreeOnValid keywordValue).ne_invariant
    input inputValid error

/-- Both optional markers and their policy diagnostics are total. -/
theorem functionModifiers_ordinary
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, functionModifiers location input = .ok value next) ∨
      (∃ failure next,
        functionModifiers location input = .reject failure next) := by
  rcases optionalFunctionModifier_ordinary .publicKw input inputValid with
    ⟨publicMarker, afterPublic, publicResult⟩ |
    ⟨failure, rejected, publicResult⟩
  · have publicReply := optionalFunctionModifier_validFor .publicKw
      input inputValid
    rw [publicResult] at publicReply
    rcases optionalFunctionModifier_ordinary .payableKw afterPublic
        publicReply.2.1 with
      ⟨payableMarker, afterPayable, payableResult⟩ |
      ⟨failure, rejected, payableResult⟩
    · cases location <;> cases publicMarker <;> cases payableMarker <;>
        exact Or.inl ⟨_, _, by
          simp only [functionModifiers, bind, publicResult, payableResult]
          rfl⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [functionModifiers, bind, publicResult, payableResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [functionModifiers, bind, publicResult]⟩

theorem functionModifiers_invariantFreeOnValid
    (location : FunctionLocation) :
    Parser.InvariantFreeOnValid (functionModifiers location) :=
  functionModifiers_ordinary location

theorem functionModifiers_ne_invariant
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionModifiers location input ≠ .invariant error :=
  (functionModifiers_invariantFreeOnValid location).ne_invariant
    input inputValid error

/-- A present return clause reuses total public type parsing. -/
theorem returnClause_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, returnClause input = .ok value next) ∨
      (∃ failure next, returnClause input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := contextual_validFor .returns .typeExpr
        input inputValid
      rw [markerResult] at markerReply
      rcases delimited_ordinary .leftParen .rightParen true typeExpr
          .typeExpr .typeExpr typeExpr_elementTotalityContract afterMarker
          markerReply.2.1 with
        ⟨types, final, typesResult⟩ |
        ⟨failure, rejected, typesResult⟩
      · exact Or.inl ⟨some {
            span := SourceSpan.cover marker.span types.span
            types
          }, final, by
            simp only [returnClause, getState, bind, present, ↓reduceIte,
              markerResult, typesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [returnClause, getState, bind, present, ↓reduceIte,
            markerResult, typesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [returnClause, getState, bind, present, ↓reduceIte,
          markerResult]⟩
  · have absent : isContextual input .returns = false := by
      cases found : isContextual input .returns with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [returnClause, getState, bind, absent, Bool.false_eq_true,
        ↓reduceIte, pure]⟩

theorem returnClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid returnClause :=
  returnClause_ordinary

theorem returnClause_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    returnClause input ≠ .invariant error :=
  returnClause_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
