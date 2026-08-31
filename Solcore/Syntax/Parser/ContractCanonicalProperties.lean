import Solcore.Syntax.Parser.ContractBodyStateProperties
import Solcore.Syntax.Parser.ContractDeclarationProperties

/-! Unconditional canonical contracts for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The completed body proofs discharge every conditional outer input. -/
theorem contractBody_canonical_inputs :
    ContractInternals.ContractBodyParserInputs := {
  validFor := ContractInternals.contractBody_validFor
  preservesTokenWindow := ContractInternals.contractBody_preservesTokenWindow
  cursorMonotoneOnSuccess :=
    ContractInternals.contractBody_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    ContractInternals.contractBody_startsAtCurrentTokenOnSuccess
}

/-- Complete contract declarations satisfy the full canonical parser contract. -/
theorem contractDecl_canonical_contract :
    ContractInternals.ContractDeclParserContract :=
  ContractInternals.contractDecl_contract contractBody_canonical_inputs

theorem contractDecl_canonical_validFor :
    contractDecl.ValidFor
      (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) :=
  contractDecl_canonical_contract.validFor

theorem contractDecl_canonical_preservesTokenWindow :
    Parser.PreservesTokenWindow contractDecl :=
  contractDecl_canonical_contract.preservesTokenWindow

theorem contractDecl_canonical_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess contractDecl :=
  contractDecl_canonical_contract.preservesTokensOnSuccess

theorem contractDecl_canonical_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess contractDecl :=
  contractDecl_canonical_contract.cursorMonotoneOnSuccess

theorem contractDecl_canonical_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span) :=
  contractDecl_canonical_contract.startsAtCurrentTokenOnSuccess

theorem contractDecl_canonical_cursor_lt_onSuccess
    {input final : State} {declaration : ContractDecl}
    (parsed : contractDecl input = .ok declaration final) :
    input.cursor < final.cursor :=
  contractDecl_canonical_contract.cursorLtOnSuccess parsed

end Solcore.Syntax.Parser
