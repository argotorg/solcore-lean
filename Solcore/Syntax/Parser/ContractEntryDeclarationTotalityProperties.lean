import Solcore.Syntax.Parser.ContractEntryHelperTotalityProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

/-! Valid-input totality for constructor and fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem constructorDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .constructorKw .contractMember)
    (keyword_ordinary .constructorKw .contractMember).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    ContractEntryInternals.entryParameters_validFor
    ContractEntryInternals.entryParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (ContractEntryInternals.implicitPublicModifiers_validFor .constructorKw)
    (ContractEntryInternals.implicitPublicModifiers_invariantFreeOnValid
      .constructorKw)
  intro payableMarker
  apply Parser.bind_invariantFreeOnValid
    (isolateBlock_validFor CoreStatement.ValidFor (block .require)
      (block_canonical_validFor .require))
    (BlockInternals.isolateBlock_invariantFreeOnValid
      (block .require) (block_invariantFreeOnValid .require))
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  } : ConstructorDecl)

theorem constructorDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, constructorDecl input = .ok declaration next) ∨
      (∃ failure next, constructorDecl input = .reject failure next) :=
  constructorDecl_invariantFreeOnValid input inputValid

theorem constructorDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    constructorDecl input ≠ .invariant error :=
  constructorDecl_invariantFreeOnValid.ne_invariant input inputValid error

private theorem fallbackTail_invariantFreeOnValid
    (marker : Token) (parameters : DelimitedList FunctionParameter) :
    Parser.InvariantFreeOnValid (do
      let payableMarker ←
        ContractEntryInternals.implicitPublicModifiers .fallbackKw
      let body ← isolateBlock (block .require)
      pure ({
        span := SourceSpan.cover marker.span body.span
        value := { parameters, payableMarker, body }
      } : FallbackDecl)) := by
  apply Parser.bind_invariantFreeOnValid
    (ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw)
    (ContractEntryInternals.implicitPublicModifiers_invariantFreeOnValid
      .fallbackKw)
  intro payableMarker
  apply Parser.bind_invariantFreeOnValid
    (isolateBlock_validFor CoreStatement.ValidFor (block .require)
      (block_canonical_validFor .require))
    (BlockInternals.isolateBlock_invariantFreeOnValid
      (block .require) (block_invariantFreeOnValid .require))
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  } : FallbackDecl)

/-- Parameter diagnostics preserve validity before parsing the fallback tail. -/
theorem fallbackDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, fallbackDecl input = .ok declaration next) ∨
      (∃ failure next, fallbackDecl input = .reject failure next) := by
  rcases (keyword_ordinary .fallbackKw .contractMember) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .fallbackKw .contractMember
      input inputValid
    rw [markerResult] at markerReply
    rcases ContractEntryInternals.entryParameters_ordinary afterMarker
        markerReply.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersReply := ContractEntryInternals.entryParameters_validFor
        afterMarker markerReply.2.1
      rw [parametersResult] at parametersReply
      by_cases empty : parameters.elements.isEmpty
      · rcases fallbackTail_invariantFreeOnValid marker parameters
            afterParameters parametersReply.2.1 with
          ⟨declaration, final, tailResult⟩ |
          ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨declaration, final, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, ↓reduceIte, pure] using tailResult⟩
        · exact Or.inr ⟨failure, rejected, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, ↓reduceIte, pure] using tailResult⟩
      · have parametersValidAfter : DelimitedList.ValidFor
            FunctionParameter.ValidFor afterParameters.file parameters := by
          simpa [parametersReply.2.2] using parametersReply.1
        let diagnostic : ParseDiagnostic := {
          span := parameters.span
          kind := .constraintViolation .fallbackRequiresNoParameters
        }
        have emittedValid := parametersReply.2.1.emit_validFor diagnostic
          parametersValidAfter.1
        rcases fallbackTail_invariantFreeOnValid marker parameters
            (afterParameters.emit diagnostic) emittedValid with
          ⟨declaration, final, tailResult⟩ |
          ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨declaration, final, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, Bool.false_eq_true, ↓reduceIte, emitDiagnostic,
              modifyState, diagnostic] using tailResult⟩
        · exact Or.inr ⟨failure, rejected, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, Bool.false_eq_true, ↓reduceIte, emitDiagnostic,
              modifyState, diagnostic] using tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [fallbackDecl, bind, markerResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [fallbackDecl, bind, markerResult]⟩

theorem fallbackDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid fallbackDecl :=
  fallbackDecl_ordinary

theorem fallbackDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    fallbackDecl input ≠ .invariant error :=
  fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
