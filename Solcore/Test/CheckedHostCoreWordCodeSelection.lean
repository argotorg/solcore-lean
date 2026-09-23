import Solcore.ContractRuntime.WorldStateWordCodeSelectionProperties

/-! Executable regressions for branch-complete selected Word-code classification. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x81, by decide⟩
private def slot : Word := ⟨0x82, by decide⟩
private def oldValue : Word := ⟨0x83, by decide⟩
private def newValue : Word := ⟨0x84, by decide⟩
private def returnedWord : Word := ⟨0x1234, by decide⟩

private def boolProgram : Program := {
  resultType := .bool
  body := .bool true
}

private def wordProgram : Program := {
  resultType := .word
  body := .word returnedWord
}

private theorem boolProgram_checked : boolProgram.checkHost = true := by
  decide

private theorem wordProgram_checked : wordProgram.checkHost = true := by
  decide

private def boolCode : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_checked⟩

private def checkedWordCode : CheckedHostCoreProgram :=
  ⟨wordProgram, wordProgram_checked⟩

private def wordCode : CheckedHostCoreWordProgram :=
  ⟨checkedWordCode, rfl⟩

private def emptyWorld : WorldState := WorldState.empty

private def noCodeWorld : WorldState :=
  WorldState.empty.putAccount codeAddress Account.empty

private def nonWordWorld : WorldState :=
  WorldState.empty.putAccount codeAddress
    (Account.empty.withCode boolCode)

private def wordAccount : Account :=
  (Account.empty.storageWrite slot oldValue).withCode checkedWordCode

private def wordWorld : WorldState :=
  WorldState.empty.putAccount codeAddress wordAccount

private def erasedSelectionMatches (state : WorldState) : Bool :=
  match state.selectWordCode codeAddress, state.code? codeAddress with
  | .codeAbsent, none => true
  | .nonWord selected _, some original =>
      selected.program == original.program
  | .word selected, some original =>
      selected.code.program == original.program
  | _, _ => false

private def wordProjectionMatches
    (state : WorldState) (expected : Bool) : Bool :=
  match (state.selectWordCode codeAddress).toWordCode? with
  | none => !expected
  | some selected => expected && selected.code.program == wordProgram

def testCheckedHostCoreWordCodeSelection : IO Unit := do
  match emptyWorld.selectWordCode codeAddress,
      noCodeWorld.selectWordCode codeAddress with
  | .codeAbsent, .codeAbsent => pure ()
  | _, _ =>
      throw (IO.userError
        "missing Account and Account without code were not codeAbsent")

  match nonWordWorld.selectWordCode codeAddress with
  | .nonWord selected _ =>
      assertTrue (selected.program == boolProgram)
        "nonWord selection did not retain the exact checked program"
  | _ =>
      throw (IO.userError "checked Bool code was not classified nonWord")

  match wordWorld.selectWordCode codeAddress with
  | .word selected =>
      assertTrue
        (selected.code.program == wordProgram &&
          selected.code.program.resultType == .word)
        "Word selection did not retain the exact ADR-0141 refinement"
  | _ =>
      throw (IO.userError "checked Word code was not classified word")

  assertTrue
    (erasedSelectionMatches emptyWorld &&
      erasedSelectionMatches noCodeWorld &&
      erasedSelectionMatches nonWordWorld &&
      erasedSelectionMatches wordWorld)
    "checked-code erasure disagreed with WorldState.code?"

  assertTrue
    (wordProjectionMatches emptyWorld false &&
      wordProjectionMatches noCodeWorld false &&
      wordProjectionMatches nonWordWorld false &&
      wordProjectionMatches wordWorld true)
    "Word projection did not isolate exactly the Word branch"

  let writtenAccount := wordAccount.storageWrite slot newValue
  let writtenWorld :=
    WorldState.empty.putAccount codeAddress writtenAccount
  assertTrue (writtenAccount.storageRead slot == newValue)
    "the storage-write preservation fixture did not update storage"
  match writtenWorld.selectWordCode codeAddress with
  | .word selected =>
      assertTrue
        (selected.code.program == wordCode.code.program &&
          erasedSelectionMatches writtenWorld &&
          wordProjectionMatches writtenWorld true)
        "storage writing changed the Word branch or selected code"
  | _ =>
      throw (IO.userError "storage writing changed the selected branch")

end Tests
