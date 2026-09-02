import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Broad ordinary outcomes for required implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A nonempty angle-delimited list of broad ordinary type expressions,
adapted exactly to the AST's nonempty container. -/
def ImplHeadArgumentsOrdinaryParses
    (input : Remainder)
    (arguments : NonemptyDelimitedList Syntax.TypeExpr)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .less .greater
    TypeExprOrdinaryParses input {
      span := arguments.span
      elements := arguments.elements.toList
    } output

/-- Exact rejection of the committed nonempty, trailing-comma angle list. -/
abbrev ImplHeadArgumentsRejects :=
  DelimitedListRejects .less .greater false true TypeExprOrdinaryParses
    TypeExprRejects

end Solcore.Syntax.DeclarativeGrammar
