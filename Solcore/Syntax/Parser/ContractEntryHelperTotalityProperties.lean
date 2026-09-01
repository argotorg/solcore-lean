import Solcore.Syntax.Parser.ContractEntryProperties
import Solcore.Syntax.Parser.NamedParameterTotalityProperties

/-! Totality for parameter and modifier helpers shared by contract entries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractEntryInternals

theorem entryParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, entryParameters input = .ok values next) ∨
      (∃ failure next, entryParameters input = .reject failure next) := by
  simpa only [entryParameters] using
    delimited_ordinary .leftParen .rightParen true namedParameter
      .parameter .topLevel namedParameter_elementTotalityContract
      input inputValid

theorem entryParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid entryParameters :=
  entryParameters_ordinary

theorem entryParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    entryParameters input ≠ .invariant error :=
  entryParameters_invariantFreeOnValid.ne_invariant input inputValid error

theorem optionalModifier_ordinary
    (modifier : HardKeyword)
    (input : State) (_inputValid : input.ValidFor) :
    (∃ value next, optionalModifier modifier input = .ok value next) ∨
      (∃ failure next,
        optionalModifier modifier input = .reject failure next) := by
  by_cases present : isKeyword input modifier
  · rcases (keyword_ordinary modifier .contractMember) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨some marker.span, next, by
        simp only [optionalModifier, getState, bind, present, ↓reduceIte,
          markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalModifier, getState, bind, present, ↓reduceIte,
          markerResult]⟩
  · have absent : isKeyword input modifier = false := by
      cases found : isKeyword input modifier with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalModifier, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalModifier_invariantFreeOnValid (modifier : HardKeyword) :
    Parser.InvariantFreeOnValid (optionalModifier modifier) :=
  optionalModifier_ordinary modifier

theorem optionalModifier_ne_invariant
    (modifier : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalModifier modifier input ≠ .invariant error :=
  (optionalModifier_invariantFreeOnValid modifier).ne_invariant
    input inputValid error

/-- Public-marker diagnostics preserve validity before optional payable parsing. -/
theorem implicitPublicModifiers_ordinary
    (declaration : HardKeyword)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next,
      implicitPublicModifiers declaration input = .ok value next) ∨
      (∃ failure next,
        implicitPublicModifiers declaration input = .reject failure next) := by
  rcases optionalModifier_ordinary .publicKw input inputValid with
    ⟨publicMarker, afterPublic, publicResult⟩ |
    ⟨failure, rejected, publicResult⟩
  · have publicReply := optionalModifier_validFor .publicKw input inputValid
    rw [publicResult] at publicReply
    cases publicMarker with
    | none =>
        rcases optionalModifier_ordinary .payableKw afterPublic
            publicReply.2.1 with
          ⟨payable, final, payableResult⟩ |
          ⟨failure, rejected, payableResult⟩
        · exact Or.inl ⟨payable, final, by
            simp only [implicitPublicModifiers, bind, publicResult,
              payableResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [implicitPublicModifiers, bind, publicResult,
              payableResult]⟩
    | some span =>
        have spanValid : span.ValidFor afterPublic.file := by
          simpa [Option.ValidFor, publicReply.2.2] using publicReply.1
        let diagnostic : ParseDiagnostic := {
          span
          kind := .constraintViolation (.implicitPublicModifier declaration)
        }
        have emittedValid := publicReply.2.1.emit_validFor diagnostic spanValid
        rcases optionalModifier_ordinary .payableKw
            (afterPublic.emit diagnostic) emittedValid with
          ⟨payable, final, payableResult⟩ |
          ⟨failure, rejected, payableResult⟩
        · exact Or.inl ⟨payable, final, by
            simp only [implicitPublicModifiers, bind, publicResult,
              emitDiagnostic, modifyState, diagnostic, payableResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [implicitPublicModifiers, bind, publicResult,
              emitDiagnostic, modifyState, diagnostic, payableResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [implicitPublicModifiers, bind, publicResult]⟩

theorem implicitPublicModifiers_invariantFreeOnValid
    (declaration : HardKeyword) :
    Parser.InvariantFreeOnValid (implicitPublicModifiers declaration) :=
  implicitPublicModifiers_ordinary declaration

theorem implicitPublicModifiers_ne_invariant
    (declaration : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implicitPublicModifiers declaration input ≠ .invariant error :=
  (implicitPublicModifiers_invariantFreeOnValid declaration).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ContractEntryInternals
