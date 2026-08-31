import Solcore.Syntax.Parser.DelimitedNonemptyProperties

/-! External consumers for nonempty delimited-result laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @afterDelimitedElement_elements_ne_nil_onSuccess
example := @delimitedWithPolicy_false_elements_ne_nil_onSuccess
example := @delimited_false_elements_ne_nil_onSuccess
example := @delimitedNoTrailing_false_elements_ne_nil_onSuccess

end Tests
