import Solcore.Frontend.Fragments.Internal.SourceValues
import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.Fragments.Internal.LambdaDepth
import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Resolved.Internal.ScopeLaws
import Solcore.Core.Internal.LocalFragment
import Solcore.Resolved.Internal.LocalFragmentLaws
import Solcore.Frontend.Fragments.Internal.LocalComputations
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.LocalApplication
import Solcore.Frontend.WordLiteral
import Solcore.Frontend.Fragments.Internal.ExpectedLambdas

/-!
# Historical fragments

Imports the historical fragment chain under `Fragments/Internal/`. The current pipeline reaches only
`WordLiteral` from it. It stays because the tests use it.
-/

section
-- leanmerge: from Solcore.Frontend.Fragments.ClosedSource
/-! Closed-source evaluation, ownership, compiled runtime functions, and support. -/
end

section
-- leanmerge: from Solcore.Frontend.Fragments.Local
/-! Local expression, computation, input, cost, and evaluator fragments. -/
end

section
-- leanmerge: from Solcore.Frontend.Fragments.ReturnTree
/-! Conditional, terminal, and typed-let return body/tree fragments. -/
end

section
-- leanmerge: from Solcore.Frontend.Fragments.RuntimeAdapter
/-! Type names, runtime adapter inputs, functions, and expected lambdas. -/
end
