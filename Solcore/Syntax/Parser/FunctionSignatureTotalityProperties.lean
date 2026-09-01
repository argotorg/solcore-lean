import Solcore.Syntax.Parser.FunctionSignatureLeafTotalityProperties
import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.Parser.GenericParametersTotalityProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties

/-! Valid-input totality for complete canonical function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem functionSignature_invariantFreeOnValid
    (location : FunctionLocation) :
    Parser.InvariantFreeOnValid (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .functionKw .topItem)
    (keyword_ordinary .functionKw .topItem).invariantFreeOnValid
  intro functionToken
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid functionParameters_validFor
    functionParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid (functionModifiers_validFor location)
    (functionModifiers_invariantFreeOnValid location)
  intro modifiers
  apply Parser.bind_invariantFreeOnValid returnClause_validFor
    returnClause_invariantFreeOnValid
  intro returnsClause
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover functionToken.span
      (SignatureInternals.signatureEnd parameters modifiers returnsClause
        parsedWhereClause)
    name
    genericParameters
    parameters
    modifiers
    returnsClause
    whereClause := parsedWhereClause
  } : FunctionSignature)

theorem functionSignature_ordinary
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor) :
    (∃ signature next,
      functionSignature location input = .ok signature next) ∨
      (∃ failure next,
        functionSignature location input = .reject failure next) :=
  functionSignature_invariantFreeOnValid location input inputValid

theorem functionSignature_ne_invariant
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionSignature location input ≠ .invariant error :=
  (functionSignature_invariantFreeOnValid location).ne_invariant
    input inputValid error

/-- A complete signature is a strict reusable parser element. -/
theorem functionSignature_elementTotalityContract
    (location : FunctionLocation) :
    ElementTotalityContract (functionSignature location) := {
  validFor := (functionSignature_validFor location).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := functionSignature_preservesTokenWindow location
  cursorLtOnSuccess :=
    FunctionInternals.functionSignature_cursor_lt_onSuccess location
  invariantFree := functionSignature_ne_invariant location
}

end Solcore.Syntax.Parser
