import Solcore.Frontend.RustHull.CallFreeCorrespondence
import Solcore.Frontend.RustHull.BuiltinCorrespondence
import Solcore.Frontend.RustHull.PureFunctionCorrespondence
import Solcore.Frontend.RustHull.PureProgramCorrespondence
import Solcore.Frontend.RustHull.RankedProgramCorrespondence
import Solcore.Frontend.RustHull.NamedFunctionCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage

/-! Independent Hull meaning and its connection to the actual Core compiler.

Accepted programs in the ranked straight-line fragment are
connected without a body-correctness assumption: actual input parsing,
compilation, function installation, parameter initialization, local heap, normal
result and every finite chain of public resumptions are covered. Expression
eligibility is syntactic and includes structured values, conditionals and
nested calls to pure builtins and named functions. Named calls decrease a
function rank, so this theorem covers acyclic call graphs. Pure entry functions
are also connected in arbitrary accepted multi-function programs.
The Word identity family additionally supplies an unconditional source
execution for every Word input. Pure builtin correspondence is compositional.
This module does not claim an unrestricted Hull or contract theorem; external
effects remain explicit source interfaces until their concrete implementations
are related separately.
-/
