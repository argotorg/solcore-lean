import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar

/-! Named-type argument rejection is possible only after positive angle-bracket
lookahead. An absent opening delimiter is an unchanged optional success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeArgumentsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (opening : TokenAt input.tokens input.endIndex input.cursor { span := openingSpan, value := .symbol .less })
      (arguments : TrailingDelimitedListTraceRejects .less .greater false .typeExpr elementTrace elementRejects
        source endByte input rejected report trace) :
      NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
