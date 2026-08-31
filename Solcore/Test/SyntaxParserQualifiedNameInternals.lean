import Solcore.Syntax.Parser.Name

/-! External consumers for proof-visible qualified-name components. -/

namespace Tests

open Solcore.Syntax.Parser

example := @QualifiedNameInternals.finishQualifiedName
example := @QualifiedNameInternals.qualifiedNameTail

end Tests
