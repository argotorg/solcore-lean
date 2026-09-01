import Solcore.Syntax.Parser.Statement.AssemblyTotalityProperties

/-! Compile-time consumers for Core inline-assembly totality. -/

namespace Solcore.Test.SyntaxParserStatementAssemblyTotalityProperties

open Solcore.Syntax.Parser

example := @assemblyStatement_ordinary
example := @assemblyStatement_invariantFreeOnValid
example := @assemblyStatement_ne_invariant
example := @assemblyStatement_elementTotalityContract
example := @assemblyStatement_fuelElementTotalityContract
example := @assemblyStatement_totalityContract
example := @assemblyStatement_fuelTotalityContract
example := @assemblyStatement_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserStatementAssemblyTotalityProperties
