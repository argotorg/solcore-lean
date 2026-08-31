import Solcore.Syntax.Parser.ContractProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.contractField_validFor
example := @ContractInternals.contractField_preservesTokenWindow
example := @ContractInternals.contractField_preservesTokensOnSuccess
example := @ContractInternals.contractField_cursorMonotoneOnSuccess
example := @ContractInternals.contractField_startsAtCurrentTokenOnSuccess
example := @ContractInternals.ContractMemberParserContract
example := @ContractInternals.ContractMemberParserContract.preservesTokensOnSuccess
example := @ContractInternals.CanonicalContractMemberContract
example := @ContractInternals.extendContractMemberStart_contract
example := @ContractInternals.attachContractDerive_reply_validFor
example := @ContractInternals.attachContractDerive_preservesTokenWindow
example := @ContractInternals.attachContractDerive_preservesTokensOnSuccess
example := @ContractInternals.attachContractDerive_cursorMonotoneOnSuccess
example := @ContractInternals.attachContractDerive_preservesDeriveStartOnSuccess
example := @ContractInternals.attachContractDerive_spanAlignedOnSuccess
example := @ContractInternals.mapMember_contract
example := @ContractInternals.contractField_canonical_contract
example := @ContractInternals.contractFunction_canonical_contract
example := @ContractInternals.contractConstructor_canonical_contract
example := @ContractInternals.contractFallback_canonical_contract
example := @ContractInternals.contractTypeAlias_canonical_contract
example := @ContractInternals.contractEnum_canonical_contract
example := @ContractInternals.contractMemberParser_canonical_contract
example := @ContractInternals.contractMemberCore_canonical_contract
example := @ContractInternals.contractMemberWithAttribute_canonical_contract
end Tests
