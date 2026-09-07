import Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceGrammar

/-! Raw named-type success independently composes the checked qualified name,
optional nonempty arguments, and final spelling diagnostics, in that order.
Type-dispatch priority guards are deliberately not part of this raw judgment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : QualifiedName}
      {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
      {nameEvents argumentEvents finishingEvents : List ParseDiagnostic}
      (nameParsed : QualifiedNameTraceParses source endByte input name afterName nameEvents)
      (argumentsParsed : NamedTypeArgumentsTraceParses elementTrace source endByte
        afterName arguments output argumentEvents)
      (finished : NamedTypeFinishingTrace name arguments finishingEvents) :
      NamedTypeTraceParses elementTrace source endByte input (namedTypeTraceValue name arguments)
        output (nameEvents ++ argumentEvents ++ finishingEvents)

end Solcore.Syntax.DeclarativeGrammar
