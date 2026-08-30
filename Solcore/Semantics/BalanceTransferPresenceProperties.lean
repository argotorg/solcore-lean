import Solcore.Semantics.BalanceTransferProperties
import Solcore.Semantics.HostStorageAccountPresence

/-! Account presence survives successful balance-only transitions. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

def transferBalance_preserves_present
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    (success : state.transferBalance sender recipient amount = .ok next)
    (present : PresentAccountAt state target) :
    PresentAccountAt next target := by
  unfold transferBalance at success
  split at success
  · contradiction
  · rename_i senderAccount senderPresent
    split at success
    · contradiction
    · rename_i recipientAccount recipientPresent
      split at success
      · contradiction
      · rename_i debited debitPresent
        split at success
        · cases success
          exact present
        · rename_i nonzero
          split at success
          · cases success
            exact present
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              by_cases targetRecipient : target = recipient
              · subst target
                exact ⟨recipientAccount.withBalance credited,
                  account?_putAccount_same _ _ _⟩
              · by_cases targetSender : target = sender
                · subst target
                  refine ⟨senderAccount.withBalance debited, ?_⟩
                  rw [account?_putAccount_other _ recipient sender _ different]
                  exact account?_putAccount_same _ _ _
                · refine ⟨present.account, ?_⟩
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact present.present

end Solcore.Semantics.WorldState
