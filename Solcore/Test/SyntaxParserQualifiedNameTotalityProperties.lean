import Solcore.Syntax.Parser.QualifiedNameTotalityProperties

/-! External consumers for qualified-name totality. -/

namespace Tests

open Solcore.Syntax.Parser

example :=
  @QualifiedNameInternals.qualifiedNameTail_ordinary_of_remainingCount_lt
example :=
  @QualifiedNameInternals.qualifiedNameTail_ne_invariant_of_remainingCount_lt
example := @QualifiedNameInternals.qualifiedNameTail_production_ordinary
example := @qualifiedName_ordinary
example := @qualifiedName_ne_invariant
example := @qualifiedName_elementTotalityContract

end Tests
