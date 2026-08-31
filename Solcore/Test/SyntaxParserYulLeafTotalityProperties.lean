import Solcore.Syntax.Parser.Yul.LeafTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulLeafTotalityProperties

open Solcore.Syntax.Parser

example := @yulName_ordinary
example := @yulLiteral_ordinary
example := @rejectedMeta_ordinary
example := @yulName_elementTotalityContract
example := @yulLiteral_elementTotalityContract
example := @rejectedMeta_elementTotalityContract

end Solcore.Test.SyntaxParserYulLeafTotalityProperties
