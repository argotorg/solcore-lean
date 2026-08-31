import Solcore.Syntax.Parser.LiteralTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLiteralTotalityProperties

open Solcore.Syntax.Parser

example : Parser.Ordinary coreLiteral :=
  coreLiteral_ordinary

example : Parser.Ordinary booleanIdentifier :=
  booleanIdentifier_ordinary

example : ElementTotalityContract coreLiteral :=
  coreLiteral_elementTotalityContract

example : ElementTotalityContract booleanIdentifier :=
  booleanIdentifier_elementTotalityContract

end Solcore.Test.SyntaxParserLiteralTotalityProperties
