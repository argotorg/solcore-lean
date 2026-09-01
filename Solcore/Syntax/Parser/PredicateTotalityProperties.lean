import Solcore.Syntax.Parser.PredicateSequenceTailProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.Parser.TypeNamedTotalityProperties

/-! Valid-input totality for one canonical trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of a trait predicate has an ordinary outcome. -/
theorem predicate_invariantFreeOnValid :
    Parser.InvariantFreeOnValid predicate := by
  unfold predicate
  apply Parser.bind_invariantFreeOnValid typeExpr_validFor
    typeExpr_invariantFreeOnValid
  intro subject
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .colon .typeExpr)
    (symbol_ordinary .colon .typeExpr).invariantFreeOnValid
  intro _colon
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .typeExpr)
    (identifier_ordinary .typeExpr).invariantFreeOnValid
  intro traitName
  apply Parser.bind_invariantFreeOnValid
    (parseNamedTypeArguments_validFor typeExpr typeExpr_validFor
      typeExpr_preservesTokensOnSuccess)
    (fun input inputValid => parseNamedTypeArguments_ordinary typeExpr
      typeExpr_elementTotalityContract input inputValid)
  intro arguments
  let endSpan := match arguments with
    | some values => values.span
    | none => traitName.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover subject.span endSpan
    subject
    traitName
    arguments
  } : Predicate)

theorem predicate_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    predicate input ≠ .invariant error :=
  predicate_invariantFreeOnValid.ne_invariant input inputValid error

/-- Predicate syntax/state laws paired with unconditional totality. -/
theorem predicate_elementTotalityContract :
    ElementTotalityContract predicate := {
  validFor := predicate_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := predicate_preservesTokenWindow
  cursorLtOnSuccess := PredicateInternals.predicate_cursor_lt_onSuccess
  invariantFree := predicate_ne_invariant
}

end Solcore.Syntax.Parser
