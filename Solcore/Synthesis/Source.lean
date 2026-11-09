import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Source.Cases
import Solcore.Synthesis.Source.Acceptance
import Solcore.Synthesis.Internal.Assembly
import Solcore.Synthesis.Internal.Enums
import Solcore.Synthesis.Internal.Traits
import Solcore.Synthesis.Internal.MemoryValues
import Solcore.Synthesis.Internal.MemoryCalls
import Solcore.Synthesis.Internal.RevertData
import Solcore.Synthesis.Internal.Integers
import Solcore.Synthesis.Internal.Arrays
import Solcore.Synthesis.Internal.Captures
import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Synthesis.Internal.Loops
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.LanguageFeatures
import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Internal.AbiValues
import Solcore.Synthesis.Internal.AdtStorage
import Solcore.Synthesis.Internal.Calls

/-!
# Source synthesis

Imports checked cases, source emission and replay. Each profile lives in one file of `Internal/`.
-/

/-! Checked Core cases, deterministic Solcore source emission and replay. -/
