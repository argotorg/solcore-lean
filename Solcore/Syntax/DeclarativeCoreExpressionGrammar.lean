import Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar
import Solcore.Syntax.DeclarativeCoreExpressionStepGrammar

/-!
Parser-independent composition of one concrete Core expression layer over
supplied recursive expression and block judgments.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One concrete Core expression recursion step, from its ordered atom
dispatcher through maximal postfixes and every operator layer. -/
def CoreExpressionStepWithBlockParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop :=
  CoreExpressionStepParses
    (ExpressionAtomCoreParses nestedParses blockParses) nestedParses

end Solcore.Syntax.DeclarativeGrammar
