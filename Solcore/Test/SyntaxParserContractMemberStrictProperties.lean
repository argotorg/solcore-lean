import Solcore.Syntax.Parser.ContractMemberStrictProperties

/-! External consumers for strict contract-member cursor progress. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @contractFieldMember_cursor_lt_onSuccess
example := @contractFunctionMember_cursor_lt_onSuccess
example := @contractConstructorMember_cursor_lt_onSuccess
example := @contractFallbackMember_cursor_lt_onSuccess
example := @contractTypeAliasMember_cursor_lt_onSuccess
example := @contractEnumMember_cursor_lt_onSuccess
example := @contractMemberCore_cursor_lt_onSuccess
example := @contractMemberWithAttribute_cursor_lt_onSuccess

example {input final : State} {member : ContractMember}
    (parsed : contractMemberWithAttribute input = .ok member final) :
    input.cursor < final.cursor :=
  contractMemberWithAttribute_cursor_lt_onSuccess parsed

end Solcore.Test.SyntaxParserContractMemberStrictProperties
