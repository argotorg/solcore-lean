import Solcore.Syntax.DeclarativeContractDeriveAttachmentGrammar
import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for public contract-member dispatch.
The leading-hash branch commits to public derive parsing before parsing and
transforming one core member.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public contract-member success, including pure derive attachment.
The attachment step does not change the core parser's final remainder. -/
inductive ContractMemberOrdinaryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | plain {input output : Remainder} {member : Syntax.ContractMember}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (coreParsed : ContractMemberCoreOrdinaryParses input member output) :
      ContractMemberOrdinaryParses input member output
  | derived {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute}
      {coreMember member : Syntax.ContractMember}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (coreParsed : ContractMemberCoreOrdinaryParses afterDerive coreMember
        output)
      (attached : ContractDeriveAttaches derive coreMember member) :
      ContractMemberOrdinaryParses input member output

/-- Exact first rejecting stage of public contract-member dispatch.  Pure
attachment has no rejecting outcome. -/
inductive ContractMemberRejects : Remainder → Remainder → Prop where
  | plainCoreRejected {input rejected : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (coreRejected : ContractMemberCoreRejects input rejected) :
      ContractMemberRejects input rejected
  | deriveRejected {input rejected : Remainder}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveRejected : DeriveAttributeRejects input rejected) :
      ContractMemberRejects input rejected
  | derivedCoreRejected {input afterDerive rejected : Remainder}
      {derive : Syntax.DeriveAttribute}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (coreRejected : ContractMemberCoreRejects afterDerive rejected) :
      ContractMemberRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
