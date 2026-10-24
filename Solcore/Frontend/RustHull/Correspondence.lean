import Solcore.Frontend.RustHull.CallFreeCorrespondence
import Solcore.Frontend.RustHull.BuiltinCorrespondence
import Solcore.Frontend.RustHull.NamedFunctionCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage

/-! Independent Hull meaning and its connection to the actual Core compiler.

Accepted single-function programs in the call-free straight-line fragment are
connected without a body-correctness assumption: actual input parsing,
compilation, function installation, parameter initialization, local heap, normal
result and every finite chain of public resumptions are covered. Expression
eligibility is syntactic and includes structured values and conditionals.
The Word identity family additionally supplies an unconditional source
execution for every Word input. Pure builtin correspondence is compositional.
This module does not claim an unrestricted Hull or contract theorem; external
effects remain explicit source interfaces until their concrete implementations
are related separately.
-/
