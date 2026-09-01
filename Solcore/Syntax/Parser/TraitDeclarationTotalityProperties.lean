import Solcore.Syntax.Parser.GenericParametersTotalityProperties
import Solcore.Syntax.Parser.TraitBodyTotalityProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties

/-! Valid-input totality for complete canonical trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of a trait declaration has an ordinary outcome. -/
theorem traitDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitDecl := by
  unfold traitDecl
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .trait .topItem)
    (contextual_ordinary .trait .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid genericParameters_validFor
    genericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  apply Parser.bind_invariantFreeOnValid TraitInternals.traitBody_validFor
    TraitInternals.traitBody_invariantFreeOnValid
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      whereClause := parsedWhereClause
      bodySpan := body.span
      methods := body.methods
    }
  } : TraitDecl)

theorem traitDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, traitDecl input = .ok declaration next) ∨
      (∃ failure next, traitDecl input = .reject failure next) :=
  traitDecl_invariantFreeOnValid input inputValid

theorem traitDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitDecl input ≠ .invariant error :=
  traitDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
