import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeGrammar
import Solcore.Syntax.DeclarativePlainTopItemOutcomeGrammar
import Solcore.Syntax.DeclarativeTopItemDeriveAttachmentGrammar

/-!
Parser-independent broad ordinary outcomes for public top-item dispatch. The
leading-hash branch commits to derive parsing before plain dispatch and pure
attachment.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public top-item success, including pure derive attachment. The
attachment step does not change the plain parser's final remainder. -/
inductive TopItemOrdinaryParses :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | plain {input output : Remainder} {item : Syntax.TopItem}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (plainParsed : PlainTopItemOrdinaryParses input item output) :
      TopItemOrdinaryParses input item output
  | derived {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute} {plainItem item : Syntax.TopItem}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (plainParsed : PlainTopItemOrdinaryParses afterDerive plainItem output)
      (attached : TopItemDeriveAttaches derive plainItem item) :
      TopItemOrdinaryParses input item output

/-- Exact first rejecting stage of public top-item dispatch. Pure attachment
has no rejecting outcome. -/
inductive TopItemRejects : Remainder → Remainder → Prop where
  | plainRejected {input rejected : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (plainRejected : PlainTopItemRejects input rejected) :
      TopItemRejects input rejected
  | deriveRejected {input rejected : Remainder}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveRejected : DeriveAttributeRejects input rejected) :
      TopItemRejects input rejected
  | derivedPlainRejected {input afterDerive rejected : Remainder}
      {derive : Syntax.DeriveAttribute}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (plainRejected : PlainTopItemRejects afterDerive rejected) :
      TopItemRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
