import Solcore.Semantics.BalanceTransferProperties
import Solcore.Semantics.CheckedCoreContract

/-! Checked contract installation survives balance-only state transitions. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- A successful balance transfer preserves every installed checked contract. -/
def transferBalance_preserves_installed
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    {contract : CheckedCoreContract}
    (success : state.transferBalance sender recipient amount = .ok next)
    (installed : InstalledCheckedCoreContract state target contract) :
    InstalledCheckedCoreContract next target contract := by
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
          exact installed
        · rename_i nonzero
          split at success
          · cases success
            exact installed
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              have payload := transferBalance_cross_preserves_payload
                senderAccount recipientAccount debited credited
              by_cases targetRecipient : target = recipient
              · subst target
                have accountEq : installed.account = recipientAccount := by
                  exact Option.some.inj
                    (installed.account_present.symm.trans recipientPresent)
                refine {
                  account := recipientAccount.withBalance credited
                  account_present := ?_
                  code_present := ?_
                }
                · exact account?_putAccount_same _ _ _
                · calc
                    (recipientAccount.withBalance credited).code? =
                        recipientAccount.code? := payload.2.2.1
                    _ = installed.account.code? := by rw [accountEq]
                    _ = some contract.code := installed.code_present
              · by_cases targetSender : target = sender
                · subst target
                  have accountEq : installed.account = senderAccount := by
                    exact Option.some.inj
                      (installed.account_present.symm.trans senderPresent)
                  refine {
                    account := senderAccount.withBalance debited
                    account_present := ?_
                    code_present := ?_
                  }
                  · rw [account?_putAccount_other _ recipient sender _ different]
                    exact account?_putAccount_same _ _ _
                  · calc
                      (senderAccount.withBalance debited).code? =
                          senderAccount.code? := payload.1
                      _ = installed.account.code? := by rw [accountEq]
                      _ = some contract.code := installed.code_present
                · refine {
                    account := installed.account
                    account_present := ?_
                    code_present := installed.code_present
                  }
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact installed.account_present

end Solcore.Semantics.WorldState
