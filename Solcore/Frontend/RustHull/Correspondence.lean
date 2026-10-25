import Solcore.Frontend.RustHull.CallFreeCorrespondence
import Solcore.Frontend.RustHull.BuiltinCorrespondence
import Solcore.Frontend.RustHull.PureFunctionCorrespondence
import Solcore.Frontend.RustHull.PureProgramCorrespondence
import Solcore.Frontend.RustHull.RankedProgramCorrespondence
import Solcore.Frontend.RustHull.RecursiveProgramCorrespondence
import Solcore.Frontend.RustHull.NamedFunctionCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage

/-! Independent Hull meaning and its connection to the actual Core compiler.

Accepted programs with local variables and structured control are
connected without a body-correctness assumption: actual input parsing,
compilation, function installation, parameter initialization, local heap, normal
result or language fault and every finite chain of public resumptions are covered. Expression
eligibility is syntactic and includes structured values, conditionals and
nested calls to pure builtins and named functions. Assignments update local
variables or nested product fields, retaining the heap on a failed RHS. Blocks, loop initializers,
conditions, bodies, post statements, break and continue use the actual Core loop
closure and retain its self cell across calls and nested loops. Induction on
the independent source execution covers loops and recursive calls whenever
that execution finishes with a value or language fault. The ranked theorem supplies an interface for
acyclic call graphs. Pure entry functions are also connected in arbitrary accepted
multi-function programs. The Word identity and recursive countdown families
additionally supply source executions for every Word input. Pure builtin
correspondence is compositional. Language faults retain their exact reason
and the heap at the failure, including faults in loop stages or call arguments.
Malformed source observations and divergence remain separate proof obligations.
This module does not claim an unrestricted Hull or contract theorem; external
effects remain explicit source interfaces until their concrete implementations
are related separately.
-/
