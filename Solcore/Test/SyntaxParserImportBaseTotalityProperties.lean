import Solcore.Syntax.Parser.ImportBaseTotalityProperties

/-! External consumers for basic import-parser totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @ImportInternals.terminator_ordinary
example := @ImportInternals.terminator_ne_invariant
example := @ImportInternals.finish_ordinary
example := @ImportInternals.finish_ne_invariant
example := @ImportInternals.plainImport_ordinary
example := @ImportInternals.plainImport_ne_invariant
example := @ImportInternals.namespaceImport_ordinary
example := @ImportInternals.namespaceImport_ne_invariant

end Tests
