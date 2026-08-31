import Solcore.Syntax.Parser.ExportConstructorTotalityProperties
import Solcore.Syntax.Parser.ExportNameTotalityProperties
import Solcore.Syntax.Parser.ExportSelectionItemTotalityProperties

/-! Unconditional valid-input totality for canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem exportDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid exportDecl := by
  let nameContract := ExportInternals.exportName_elementTotalityContract
    ExportInternals.constructorSelection_invariantFreeOnValid
  exact exportDecl_invariantFreeOnValid_of_leafContract
    (exportLeafTotalityContract nameContract)

theorem exportDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, exportDecl input = .ok value next) ∨
    (∃ failure next, exportDecl input = .reject failure next) :=
  exportDecl_invariantFreeOnValid input inputValid

theorem exportDecl_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
