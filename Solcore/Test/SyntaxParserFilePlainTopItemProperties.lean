import Solcore.Syntax.Parser.FilePlainTopItemProperties

namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.plainTopItem_contract
example (inputs : FileInternals.ContractDeclInputs) :
    Parser.PreservesTokensOnSuccess FileInternals.plainTopItem :=
  (FileInternals.plainTopItem_contract inputs).preservesTokensOnSuccess
end Tests
