import Solcore.ContractRuntime.CheckedHostCoreWordProgram
import Solcore.Test.ParentIndexedSelectedExecutionFixture

/-! Shared direct-execution fixtures for checked Word return tests. -/

set_option autoImplicit false

namespace Tests.CheckedHostCoreWordProgramExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

def wordCode : CheckedHostCoreWordProgram := ⟨code, rfl⟩

def context : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

def cellWord : Word := ⟨0x1234, by decide⟩

/-- Allocate one Core-local cell, then return an unrelated Word. -/
def cellProgram : Program := {
  resultType := .word
  body :=
    .letE (.newCell .bool (.bool true))
      (.word cellWord)
}

theorem cellProgram_host_checked : cellProgram.checkHost = true := by
  decide

def cellCode : CheckedHostCoreWordProgram :=
  ⟨⟨cellProgram, cellProgram_host_checked⟩, rfl⟩

def canonicalInputSizeReturnData : Bytes :=
  (List.replicate 31 (0 : UInt8) ++ [3]).toByteArray

end Tests.CheckedHostCoreWordProgramExecutionFixture
