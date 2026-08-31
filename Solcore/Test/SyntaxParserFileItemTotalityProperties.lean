import Solcore.Syntax.Parser.FileItemTotalityProperties

/-! External consumers for derive-aware complete-file totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileItemTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @attachDeriveAttribute_invariantFreeOnValid
example := @topItem_invariantFreeOnValid
example := @parseItemsItem_invariantFreeOnValid
example := @parseItemsItemInvariantFree_of_plainTopItemContract
example := @sourceFile_exists_ok_of_plainTopItemContract
example := @parseLexed_exists_ok_of_plainTopItemContract
example := @parseLexed_ne_error_of_plainTopItemContract
example := @parse_exists_ok_of_plainTopItemContract
example := @parse_ne_error_of_plainTopItemContract

example (contract : PlainTopItemTotalityContract) :
    ParseItemsItemInvariantFree :=
  parseItemsItemInvariantFree_of_plainTopItemContract contract

example (contract : PlainTopItemTotalityContract) (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok_of_plainTopItemContract contract file

end Solcore.Test.SyntaxParserFileItemTotalityProperties
