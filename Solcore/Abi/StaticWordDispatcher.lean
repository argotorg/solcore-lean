import Solcore.Abi.StaticWordMethodTable
import Solcore.Core.RenamingSyntax
import Solcore.ContractRuntime.CheckedCoreContract

/-! Checked Core dispatchers for validated Static Word ABI method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.ContractRuntime

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

private theorem reverted_hasType (context : Context) (reason : Word) :
    HasType context (reverted reason)
      CoreContractEntryProfile.wordOutcomeV1.resultType [] := by
  exact .inRight .word (.inLeft .word .word)

private theorem binaryWordOperands_hasType
    (context : Context) (op : BinaryOp) (left right : Expr)
    (leftTyping : HasType context left .word [])
    (rightTyping : HasType context right .word []) :
    HasType context (.binary op left right) op.resultType [] := by
  apply HasType.binary
  · simpa [BinaryOp.leftType] using leftTyping
  · simpa [BinaryOp.rightType] using rightTyping

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

private theorem route_hasType (entries : List IndexedMethod) :
    HasType
      (Ty.word :: Ty.word :: Ty.word :: Ty.word :: hostContext)
      (route entries)
      CoreContractEntryProfile.wordOutcomeV1.resultType [] := by
  induction entries with
  | nil => exact reverted_hasType _ unknownSelectorReason
  | cons entry rest inductionHypothesis =>
      apply HasType.ifE
      · simpa [BinaryOp.resultType] using
          binaryWordOperands_hasType _ .wordEq _ _
            (HasType.var (by simp)) HasType.word
      · apply HasType.inLeft
        · exact .sum .word .word
        · apply HasType.apply
          · have implementationTyping :=
              Program.checkHost_sound entry.method.implementation.code.checked
            rw [entry.method.implementation.resultType_eq,
              entry.method.implementation.dataDefinitions_eq]
              at implementationTyping
            have first := implementationTyping.weakenAt
              (inserted := .word) 0
            have second := first.weakenAt (inserted := .word) 0
            have third := second.weakenAt (inserted := .word) 0
            have fourth := third.weakenAt (inserted := .word) 0
            simpa [underDispatcherLocals, Context.insertAt] using fourth
          · exact HasType.var (by simp)
      · exact inductionHypothesis

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
        (.caseE
          (.apply
            (.var (HostFunction.inputDataWordBE?.index + 1))
            (.word Word.zero))
          (reverted malformedCalldataReason)
          (.letE
            (.binary .wordShr (.var 0) (.word selectorRightShift))
            (.caseE
              (.apply
                (.var (HostFunction.inputDataWordBE?.index + 3))
                (.word ⟨4, by decide⟩))
              (reverted malformedCalldataReason)
              (route table.entries)))))
}

/-- Every dispatcher generated from a validated method table is accepted by
the same ordinary host checker used for handwritten Core programs. -/
theorem MethodTable.dispatchProgram_checked (table : MethodTable) :
    table.dispatchProgram.checkHost = true := by
  apply Program.checkHost_complete
  constructor
  · change DataEnvironment.WellFormed []
    simp [DataEnvironment.WellFormed]
  · exact .sum .word (.sum .word .word)
  · change HasType hostContext table.dispatchProgram.body
      CoreContractEntryProfile.wordOutcomeV1.resultType []
    apply HasType.letE
    · exact HasType.apply
        (HasType.var hostContext_inputDataSize) HasType.unit
    · apply HasType.ifE
      · simpa [BinaryOp.resultType] using
          binaryWordOperands_hasType _ .wordGt _ _
            HasType.word (HasType.var (by simp))
      · exact reverted_hasType _ malformedCalldataReason
      · apply HasType.caseE (leftType := .unit) (rightType := .word)
        · exact HasType.apply (HasType.var (by simpa using
            hostContext_inputDataWordBE?)) HasType.word
        · exact reverted_hasType _ malformedCalldataReason
        · apply HasType.letE
          · simpa [BinaryOp.resultType] using
              binaryWordOperands_hasType _ .wordShr _ _
                (HasType.var (by simp)) HasType.word
          · apply HasType.caseE (leftType := .unit) (rightType := .word)
            · exact HasType.apply (HasType.var (by simpa using
                hostContext_inputDataWordBE?)) HasType.word
            · exact reverted_hasType _ malformedCalldataReason
            · simpa using route_hasType table.entries

/-- Recheck generated syntax under the ordinary host checker and expose an
exact `wordOutcomeV1` contract only after successful admission. -/
def MethodTable.generate? (table : MethodTable) : Option CheckedCoreContract := do
  if checked : table.dispatchProgram.checkHost = true then
    some (CheckedCoreContract.wordOutcomeV1
      ⟨table.dispatchProgram, checked⟩ rfl)
  else
    none

@[simp] theorem MethodTable.generate?_eq_some (table : MethodTable) :
    table.generate? = some
      (CheckedCoreContract.wordOutcomeV1
        ⟨table.dispatchProgram, table.dispatchProgram_checked⟩ rfl) := by
  simp [MethodTable.generate?, table.dispatchProgram_checked]

/-- Total proof-carrying dispatcher generation after table validation. -/
def MethodTable.generate (table : MethodTable) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨table.dispatchProgram, table.dispatchProgram_checked⟩ rfl

end Solcore.Abi.V1
