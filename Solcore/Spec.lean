import Solcore.Feature
import Solcore.Profile
import Solcore.Core
import Solcore.ContractRuntime
import Solcore.Syntax

/-!
Umbrella module for the pure specification side of the project.

Semantic Core and Syntax modules must not import `Solcore.Oracle.Main` or
perform `IO`.
-/
