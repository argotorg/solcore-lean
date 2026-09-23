import Solcore.ContractRuntime.SelectedCheckedWordExecution
import Solcore.Test.CheckedHostCoreWordProgramExecutionFixture

/-! Shared absent, non-Word, and measured Word selected-execution fixtures. -/

set_option autoImplicit false

namespace Tests.SelectedCheckedWordExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture

def absentContext : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨missingCodeInitialization
      |>.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

def boolProgram : Program := {
  resultType := .bool
  body := .bool true
}

theorem boolProgram_host_checked : boolProgram.checkHost = true := by
  decide

def boolCode : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_host_checked⟩

def nonWordWorkingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode boolCode)
    |>.putAccount storageAddress storageAccount

def nonWordInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := nonWordWorkingWorld
  workingRollback := 201
}

def nonWordContext : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨nonWordInitialization
      |>.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

abbrev Execution (initialContext :
    HostStorageDriver.Context Nat (FrameTrace Nat)) :=
  SelectedCheckedWordExecution initialContext executionInputs

def absentExecution (fuel : Nat) : Execution absentContext :=
  SelectedCheckedWordExecution.start absentContext executionInputs fuel

def nonWordExecution (fuel : Nat) : Execution nonWordContext :=
  SelectedCheckedWordExecution.start nonWordContext executionInputs fuel

def wordExecution (fuel : Nat) : Execution context :=
  SelectedCheckedWordExecution.start context executionInputs fuel

end Tests.SelectedCheckedWordExecutionFixture
