import Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution
import Solcore.Test.SelectedCheckedWordExecutionFixture

/-! Shared parent-indexed selected checked Word fixtures for ADR-0144. -/

set_option autoImplicit false

namespace Tests.ParentIndexedSelectedCheckedWordExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open SelectedCheckedWordExecutionFixture

def missingStorageExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    missingStorageInitialization storageAddress executionInputs fuel

def codeAbsentExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    missingCodeInitialization storageAddress executionInputs fuel

def nonWordExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    nonWordInitialization storageAddress executionInputs fuel

def wordExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    initialization storageAddress executionInputs fuel

/-- Canonical legacy policy used only for the conditional coherence branch. -/
def canonicalWordDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (_ : Store) : FrameOutcome TrapReason :=
  match value with
  | .word word => .returned (encodeWordBytesBE word)
  | _ => .trapped .policyTrap

end Tests.ParentIndexedSelectedCheckedWordExecutionFixture
