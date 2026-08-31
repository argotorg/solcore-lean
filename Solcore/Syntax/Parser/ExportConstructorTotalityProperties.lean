import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Totality for export constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExportInternals

/-- A successful syntactically nonempty list satisfies the retained carrier. -/
theorem requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
    {input afterDelimited : State} {values : DelimitedList Identifier}
    (valuesResult : delimitedNoTrailing .leftParen .rightParen false
      (identifier .exportDecl) .exportDecl .topLevel input =
        .ok values afterDelimited) :
    ∃ constructors,
      requireConstructorNames values afterDelimited =
        .ok constructors afterDelimited := by
  have nonempty := delimitedNoTrailing_false_elements_ne_nil_onSuccess
    .leftParen .rightParen (identifier .exportDecl) .exportDecl .topLevel
    valuesResult
  unfold requireConstructorNames
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

theorem requireConstructorNames_ne_invariant_of_delimitedNoTrailing_false_ok
    {input afterDelimited : State} {values : DelimitedList Identifier}
    (valuesResult : delimitedNoTrailing .leftParen .rightParen false
      (identifier .exportDecl) .exportDecl .topLevel input =
        .ok values afterDelimited)
    (error : ParserInvariantError) :
    requireConstructorNames values afterDelimited ≠ .invariant error := by
  intro failed
  rcases requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
      valuesResult with ⟨constructors, result⟩
  rw [result] at failed
  contradiction

theorem constructorSelection_invariantFreeOnValid :
    Parser.InvariantFreeOnValid constructorSelection := by
  intro input inputValid
  by_cases all : input.peekOffsetKind? 1 == some (.symbol .star)
  · rcases (symbol_ordinary .leftParen .exportDecl) input with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingValid := symbol_validFor .leftParen .exportDecl input inputValid
      rw [openingResult] at openingValid
      rcases (symbol_ordinary .star .exportDecl) afterOpening with
        ⟨marker, afterMarker, markerResult⟩ |
        ⟨failure, rejected, markerResult⟩
      · have markerValid := symbol_validFor .star .exportDecl afterOpening
          openingValid.2.1
        rw [markerResult] at markerValid
        rcases (symbol_ordinary .rightParen .exportDecl) afterMarker with
          ⟨closing, final, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover opening.span closing.span
              value := .all marker.span
            }, final, by
              simp only [constructorSelection, getState, bind, all,
                ↓reduceIte, openingResult, markerResult, closingResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [constructorSelection, getState, bind, all,
              ↓reduceIte, openingResult, markerResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [constructorSelection, getState, bind, all,
            ↓reduceIte, openingResult, markerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [constructorSelection, getState, bind, all,
          ↓reduceIte, openingResult]⟩
  · have named :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false := by
      cases found : input.peekOffsetKind? 1 == some (.symbol .star) with
      | false => rfl
      | true => exact False.elim (all found)
    rcases delimitedNoTrailing_ordinary .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
        (identifier_elementTotalityContract .exportDecl) input inputValid with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · rcases requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
        valuesResult with ⟨constructors, constructorsResult⟩
      exact Or.inl ⟨{
          span := values.span
          value := .named constructors
        }, afterValues, by
          simp only [constructorSelection, getState, bind, named,
            Bool.false_eq_true, ↓reduceIte, valuesResult, constructorsResult,
            pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [constructorSelection, getState, bind, named,
          Bool.false_eq_true, ↓reduceIte, valuesResult]⟩

theorem constructorSelection_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ selection next, constructorSelection input = .ok selection next) ∨
    (∃ failure next, constructorSelection input = .reject failure next) :=
  constructorSelection_invariantFreeOnValid input inputValid

theorem constructorSelection_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    constructorSelection input ≠ .invariant error :=
  constructorSelection_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ExportInternals
