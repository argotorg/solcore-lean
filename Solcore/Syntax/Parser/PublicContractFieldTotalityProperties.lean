import Solcore.Syntax.Parser.ContractFieldTotalityProperties
import Solcore.Syntax.Parser.ContractMemberStrictProperties
import Solcore.Syntax.Parser.ContractMemberTotalityProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

/-! Unconditional totality for canonical production contract fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Production fields inherit unconditional totality from public expressions. -/
theorem contractField_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (ContractInternals.contractField expression) :=
  ContractInternals.contractField_invariantFreeOnValid expression
    expression_invariantFreeOnValid

/-- No internal invariant can escape production contract-field parsing. -/
theorem contractField_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    ContractInternals.contractField expression input ≠ .invariant error :=
  contractField_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful production field strictly consumes its leading name. -/
theorem contractField_cursor_lt_onSuccess
    {input final : State} {field : ContractField}
    (parsed : ContractInternals.contractField expression input =
      .ok field final) :
    input.cursor < final.cursor := by
  have mapped : ContractInternals.mapMember
      (ContractInternals.contractField expression)
      ContractInternals.wrapField input =
        .ok (ContractInternals.wrapField field) final := by
    unfold ContractInternals.mapMember
    simp only [bind, parsed, pure]
  exact ContractInternals.contractFieldMember_cursor_lt_onSuccess mapped

/-- Production field syntax/state laws paired with unconditional totality. -/
theorem contractField_elementTotalityContract :
    ElementTotalityContract
      (ContractInternals.contractField expression) := {
  validFor := (ContractInternals.contractField_validFor expression
    (Expr.ValidFor CoreStatement.ValidFor)
    expression_canonical_contract.validFor
    expression_elementTotalityContract.preservesTokenWindow
    expression_canonical_contract.cursorMonotoneOnSuccess).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow :=
    ContractInternals.contractField_preservesTokenWindow expression
      expression_elementTotalityContract.preservesTokenWindow
  cursorLtOnSuccess := contractField_cursor_lt_onSuccess
  invariantFree := contractField_ne_invariant
}

namespace ContractInternals

/--
Fill the production field and enum branches while keeping the three unfinished
member families explicit assumptions.
-/
theorem contractMemberTotalityContract_of_remainingBranches
    (functionFree : Parser.InvariantFreeOnValid (functionDecl .contract))
    (constructorFree : Parser.InvariantFreeOnValid constructorDecl)
    (fallbackFree : Parser.InvariantFreeOnValid fallbackDecl) :
    ContractMemberTotalityContract := {
  field := Solcore.Syntax.Parser.contractField_invariantFreeOnValid
  function := functionFree
  constructor := constructorFree
  fallback := fallbackFree
  enum := enumDecl_invariantFreeOnValid none
}

end ContractInternals
end Solcore.Syntax.Parser
