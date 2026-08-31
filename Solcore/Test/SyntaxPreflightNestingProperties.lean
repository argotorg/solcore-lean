import Solcore.Syntax.Parser.Preflight

/-! External consumers for nesting-diagnostic provenance. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @checkNesting_some_span_validFor
example := @checkNesting_lexed_some_span_validFor

end Tests
