import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.Driver
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.Contracts
import Solcore.ContractRuntime.Transactions
import Solcore.ContractRuntime.TopLevel
import Solcore.ContractRuntime.Creation
import Solcore.ContractRuntime.NestedExecution
import Solcore.ContractRuntime.BalancedExecution
import Solcore.ContractRuntime.CallPhases
import Solcore.ContractRuntime.Internal.ScalarLaws
import Solcore.ContractRuntime.Internal.ScalarText
import Solcore.ContractRuntime.Internal.AddressBytes
import Solcore.ContractRuntime.Internal.CheckedCoreProgram
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.DriverLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.EntryOutcomeLaws
import Solcore.ContractRuntime.Internal.TransactionLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.ContractRuntime.Internal.CreationLaws
import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.ContractRuntime.Internal.BalancedLaws
import Solcore.ContractRuntime.Internal.CallPhaseLaws
import Solcore.ContractRuntime.Internal.CodeExecution
import Solcore.ContractRuntime.Internal.ParentIndexedFrames
import Solcore.ContractRuntime.Internal.ParentIndexedExecution
import Solcore.ContractRuntime.Internal.SelectedWordExecution

/-!
# Contract runtime

Checked Core contract execution: accounts and world state, host requests, frames and transactions,
nested calls and creation, commit and rollback, and top-level observations. This layer is distinct
from `Solcore.Core`'s local evaluator and from the source-language judgments of
`Solcore.SourceSemantics`. Read in this order. `docs/guide/contract-runtime.md` lists every file.

1. **State.** `RuntimeScalars`, then `WorldState`.
2. **One frame.** `Frames` holds its outcomes and checkpoints.
3. **Host requests.** `Driver` is the generic loop, and `StorageDriver` the real handler.
4. **Contracts.** `Contracts` holds completion conventions, checked contracts and the environment.
5. **One transaction.** `Transactions`, then `TopLevel`.
6. **Nested execution.** `Creation`, `NestedExecution`, then `BalancedExecution`, the public entry.
7. **Call phases.** `CallPhases`.

The front holds definitions, and the main theorems of each stage: see `Driver`, `TopLevel`,
`NestedExecution`, `BalancedExecution` and `CallPhases`. The laws are in `Internal/`, by family.
`Internal/` also holds the refinement layers that only tests use.
-/
