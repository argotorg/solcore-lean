import Solcore.Syntax.Parser.FileItemProperties
import Solcore.Syntax.Parser.FileItemsStateProperties

/-! Canonical state-transition laws for complete-file parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Canonical item parsing makes the file loop preserve its token window. -/
theorem parseItems_canonical_preservesTokenWindow
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.PreservesTokenWindow (parseItems fuel itemsRev) :=
  parseItems_preservesTokenWindow
    (parseItemsItem_contract contract).preservesTokenWindow fuel itemsRev

/-- Canonical item parsing makes the file loop retain its token carrier. -/
theorem parseItems_canonical_preservesTokensOnSuccess
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  parseItems_preservesTokensOnSuccess
    (parseItemsItem_contract contract).preservesTokenWindow fuel itemsRev

/-- Canonical item parsing makes the file loop cursor-monotone. -/
theorem parseItems_canonical_cursorMonotoneOnSuccess
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) :=
  parseItems_cursorMonotoneOnSuccess
    (parseItemsItem_contract contract).cursorMonotoneOnSuccess fuel itemsRev

/-- Canonical complete-file parsing preserves its token window. -/
theorem sourceFile_canonical_preservesTokenWindow
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) :=
  sourceFile_preservesTokenWindow
    (parseItemsItem_contract contract).preservesTokenWindow comments

/-- Canonical complete-file parsing retains its token carrier on success. -/
theorem sourceFile_canonical_preservesTokensOnSuccess
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  sourceFile_preservesTokensOnSuccess
    (parseItemsItem_contract contract).preservesTokenWindow comments

/-- Canonical complete-file parsing is cursor-monotone on success. -/
theorem sourceFile_canonical_cursorMonotoneOnSuccess
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) :=
  sourceFile_cursorMonotoneOnSuccess
    (parseItemsItem_contract contract).cursorMonotoneOnSuccess comments

end Solcore.Syntax.Parser.FileInternals
