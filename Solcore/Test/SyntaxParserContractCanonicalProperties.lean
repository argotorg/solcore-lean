import Solcore.Syntax.Parser.ContractCanonicalProperties

namespace Tests
open Solcore.Syntax.Parser
example := @contractBody_canonical_inputs
example := @contractDecl_canonical_contract
example := @contractDecl_canonical_validFor
example := @contractDecl_canonical_preservesTokenWindow
example := @contractDecl_canonical_preservesTokensOnSuccess
example := @contractDecl_canonical_cursorMonotoneOnSuccess
example := @contractDecl_canonical_startsAtCurrentTokenOnSuccess
example := @contractDecl_canonical_cursor_lt_onSuccess
end Tests
