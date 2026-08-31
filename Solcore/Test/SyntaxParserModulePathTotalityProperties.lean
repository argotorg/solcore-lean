import Solcore.Syntax.Parser.ModulePathTotalityProperties

/-! External consumers for module-path totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @modulePath_ordinary
example := @modulePath_ne_invariant
example := @modulePath_invariantFreeOnValid
example := @modulePath_elementTotalityContract

end Tests
