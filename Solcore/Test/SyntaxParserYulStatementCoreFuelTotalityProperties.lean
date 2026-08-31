import Solcore.Syntax.Parser.Yul.StatementCoreFuelTotalityProperties

/-! Compile-time consumers for complete Yul statement-core totality. -/

namespace Solcore.Test.SyntaxParserYulStatementCoreFuelTotalityProperties

open Solcore.Syntax.Parser

example := @yulStatementCore_fuelTotalityContract
example := @yulStatementCore_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserYulStatementCoreFuelTotalityProperties
