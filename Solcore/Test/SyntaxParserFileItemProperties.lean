import Solcore.Syntax.Parser.FileItemProperties

namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.parseItemsItem_contract
example (inputs : FileInternals.ContractDeclInputs) :
    Parser.PreservesTokensOnSuccess FileInternals.parseItemsItem :=
  (FileInternals.parseItemsItem_contract inputs).preservesTokensOnSuccess
end Tests
