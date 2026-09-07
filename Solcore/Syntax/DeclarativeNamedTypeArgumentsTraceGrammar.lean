import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar

/-! Optional named-type argument traces retain a structurally nonempty angle
list. Absence of the opening marker is a silent identity judgment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeArgumentsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (NonemptyDelimitedList Syntax.TypeExpr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .less)) :
      NamedTypeArgumentsTraceParses elementTrace source endByte input none input []
  | present {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic}
      (parsed : TrailingDelimitedListTraceParses .less .greater false elementTrace source endByte input
        { span := arguments.span, elements := arguments.elements.toList } output trace) :
      NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace

end Solcore.Syntax.DeclarativeGrammar
