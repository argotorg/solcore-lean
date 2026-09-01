import Solcore.Syntax.Parser.EnumBodyTotalityProperties
import Solcore.Syntax.Parser.GenericParametersTotalityProperties

/-! Valid-input totality for complete canonical enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of an enum declaration has an ordinary outcome. -/
theorem enumDecl_invariantFreeOnValid
    (deriveAttribute : Option DeriveAttribute) :
    Parser.InvariantFreeOnValid (enumDecl deriveAttribute) := by
  unfold enumDecl
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .enum .topItem)
    (contextual_ordinary .enum .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    EnumInternals.enumBody_validFor
    EnumInternals.enumBody_invariantFreeOnValid
  intro body
  let startSpan := deriveAttribute.map (fun derive => derive.span)
    |>.getD marker.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover startSpan body.span
    value := {
      deriveAttribute
      name
      parameters
      bodySpan := body.span
      constructors := body.constructors
    }
  } : EnumDecl)

theorem enumDecl_ordinary
    (deriveAttribute : Option DeriveAttribute)
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next,
      enumDecl deriveAttribute input = .ok declaration next) ∨
      (∃ failure next,
        enumDecl deriveAttribute input = .reject failure next) :=
  enumDecl_invariantFreeOnValid deriveAttribute input inputValid

theorem enumDecl_ne_invariant
    (deriveAttribute : Option DeriveAttribute)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    enumDecl deriveAttribute input ≠ .invariant error :=
  (enumDecl_invariantFreeOnValid deriveAttribute).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
