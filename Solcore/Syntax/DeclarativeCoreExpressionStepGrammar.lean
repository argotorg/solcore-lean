import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.DeclarativeCoreExpressionPostfixGrammar

/-!
Parser-independent composition of one complete Core expression recursion
step: atom, maximal postfixes, unary operators, binary precedence, and the
right-associative conditional suffix.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete Core expression layer over supplied atom and recursive
expression judgments. -/
def CoreExpressionStepParses
    (atomParses nestedParses :
      Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop :=
  ExpressionLayerParses nestedParses
    (ExpressionPostfixParses atomParses nestedParses)

end Solcore.Syntax.DeclarativeGrammar
