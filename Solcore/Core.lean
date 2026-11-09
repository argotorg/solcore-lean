import Solcore.Core.Syntax
import Solcore.Core.Data
import Solcore.Core.Primitive
import Solcore.Core.Typing
import Solcore.Core.Check
import Solcore.Core.Eval
import Solcore.Core.Machine
import Solcore.Core.Host
import Solcore.Core.HostMachine
import Solcore.Core.RuntimeTyping
import Solcore.Core.HostTyping
import Solcore.Core.Correspondence
import Solcore.Core.Fuel
import Solcore.Core.Safety
import Solcore.Core.HostRunner
import Solcore.Core.LanguageResult
import Solcore.Core.Conventions
import Solcore.Core.Mappings
import Solcore.Core.Internal.EvaluationLaws
import Solcore.Core.Internal.MachineLaws
import Solcore.Core.Internal.Simulation
import Solcore.Core.Internal.Preservation
import Solcore.Core.Internal.Renaming
import Solcore.Core.Internal.ByteSelection
import Solcore.Core.Internal.WordComparisons
import Solcore.Core.Internal.PrimitiveLaws
import Solcore.Core.Internal.DerivedForms
import Solcore.Core.Internal.LocalFragment
import Solcore.Core.Internal.HostLaws
import Solcore.Core.Internal.HostPreservation
import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.Internal.MappingLaws

/-!
# Core

The typed language every program compiles to, its semantics, and its safety proofs. Read in this
order. `docs/guide/core.md` lists every file.

1. **Language.** `Syntax`, `Data` and `Primitive`, then `Typing`. `Check` is the same check with
   diagnostics.
2. **Semantics.** `Eval` is the big-step relation and `Machine` the CEK machine. `Host` and
   `HostMachine` add host requests.
3. **Typing of states.** `RuntimeTyping` and `HostTyping` hold the relations the theorems are stated
   over.
4. **Main theorems.** `Safety`: type preservation and finite execution safety. `Correspondence`: the
   evaluator and the machine agree. `Fuel`: exact fuel accounting. `HostRunner`: the same results
   with host requests. `LanguageResult`: checked programs cannot produce a malformed result.
5. **Conventions of compiled code.** `LanguageResult`, `Conventions` and `Mappings`: how the compiler
   encodes source constructs, with no change to the language.
6. **Wire.** `Wire` is the canonical JSON boundary.

Everything else is in `Internal/`, by topic.
-/
