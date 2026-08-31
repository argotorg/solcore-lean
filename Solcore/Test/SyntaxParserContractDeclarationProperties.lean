import Solcore.Syntax.Parser.ContractDeclarationProperties

namespace Tests
open Solcore.Syntax.Parser
example := @ContractInternals.ContractBodyParserInputs
example := @ContractInternals.ContractDeclParserContract
example := @ContractInternals.contractDecl_contract
example (inputs : ContractInternals.ContractBodyParserInputs) :
    Parser.PreservesTokensOnSuccess contractDecl :=
  (ContractInternals.contractDecl_contract inputs).preservesTokensOnSuccess
end Tests
