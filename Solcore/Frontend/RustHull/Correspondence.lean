import Solcore.Frontend.RustHull.PureExpressionCorrespondence
import Solcore.Frontend.RustHull.StructuralExpressionCorrespondence
import Solcore.Frontend.RustHull.StraightLineCorrespondence
import Solcore.Frontend.RustHull.NamedFunctionCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage

/-! Independent Hull meaning and its connection to the actual Core compiler.

The Word identity family is connected without a body-correctness assumption:
actual input parsing, compilation, installed function cells, local heap, final
result and any finite chain of public resumptions are covered. The expression,
statement and representation modules expose the compositional obligations used
to extend that connection. This module does not claim an unrestricted Hull or
contract meaning-preservation theorem; external effects remain explicit source
interfaces until their concrete implementations are related separately.
-/
