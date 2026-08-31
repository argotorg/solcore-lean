import Solcore.Syntax.Parser.DeclarationCanonicalProperties

/-! External consumers for canonical body-bearing declaration validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @functionDecl_canonical_validFor
example := @constructorDecl_canonical_validFor
example := @fallbackDecl_canonical_validFor
example := @implDecl_canonical_validFor

end Tests
