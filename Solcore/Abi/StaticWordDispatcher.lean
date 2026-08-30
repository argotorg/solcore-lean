import Solcore.Abi.StaticWordMethodTable
import Solcore.Core.RenamingSyntax
import Solcore.Semantics.CheckedCoreContract

/-! Checked Core dispatchers for validated Static Word ABI method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.Semantics

/-- Calldata shorter than one selector and one static word is malformed. -/
def minimumCallDataSize : Word := ⟨36, by decide⟩

/-- The selector occupies the high four bytes of the first calldata word. -/
def selectorRightShift : Word := ⟨224, by decide⟩

/-- Stable revert payload for malformed calldata. -/
def malformedCalldataReason : Word := Word.zero

/-- Stable revert payload for a selector absent from the validated table. -/
def unknownSelectorReason : Word := ⟨1, by decide⟩

/-- Embed the selector's exact big-endian `Fin (2^32)` view into a Core word. -/
def Selector.toWord (selector : Selector) : Word :=
  ⟨selector.toFin.val,
    Nat.lt_trans selector.toFin.isLt (by decide)⟩

private def returned (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

private def reverted (reason : Word) : Expr :=
  .inRight .word (.inLeft .word (.word reason))

/-- Turn the strict optional calldata read into a total word expression. -/
private def inputWordOrZero (hostIndex : Nat) (offset : Word) : Expr :=
  .caseE
    (.apply (.var hostIndex) (.word offset))
    (.word Word.zero)
    (.var 0)

/-- Move one method implementation beneath the dispatcher's four locals. -/
private def underDispatcherLocals (implementation : WordImplementation) : Expr :=
  implementation.code.program.body
    |>.weakenAt 0
    |>.weakenAt 0
    |>.weakenAt 0
    |>.weakenAt 0

/-- Route with locals `arg`, `selector`, `selectorWindow`, and `size` at
indices zero through three. Host capabilities therefore begin at index four. -/
private def route : List IndexedMethod → Expr
  | [] => reverted unknownSelectorReason
  | entry :: rest =>
      .ifE
        (.binary .wordEq (.var 1) (.word entry.selector.toWord))
        (returned
          (.apply
            (underDispatcherLocals entry.method.implementation)
            (.var 0)))
        (route rest)

/-- Generate the unchecked syntax candidate. The public constructor below
rechecks this exact candidate before exposing executable checked code. -/
def MethodTable.dispatchProgram (table : MethodTable) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.inputDataSize.index) .unit)
      (.ifE
        (.binary .wordGt (.word minimumCallDataSize) (.var 0))
        (reverted malformedCalldataReason)
        (.letE
          (inputWordOrZero
            (HostFunction.inputDataWordBE?.index + 1) Word.zero)
          (.letE
            (.binary .wordShr (.var 0) (.word selectorRightShift))
            (.letE
              (inputWordOrZero
                (HostFunction.inputDataWordBE?.index + 3)
                ⟨4, by decide⟩)
              (route table.entries)))))
}

/-- Recheck generated syntax under the ordinary host checker and expose an
exact `wordOutcomeV1` contract only after successful admission. -/
def MethodTable.generate? (table : MethodTable) : Option CheckedCoreContract := do
  if checked : table.dispatchProgram.checkHost = true then
    some (CheckedCoreContract.wordOutcomeV1
      ⟨table.dispatchProgram, checked⟩ rfl)
  else
    none

end Solcore.Abi.V1
