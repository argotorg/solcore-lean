import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent exact unary traces reuse the maximal source-ordered prefix
grammar. Canonical unary tokens are silent; all emitted events and any terminal
report come from the supplied postfix outcome after that complete prefix. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionUnaryTraceParses
    (postfixTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterOperators output : Remainder}
      {operators : List (Located UnaryOp)} {base : Syntax.Expr} {trace : List ParseDiagnostic}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixParsed : postfixTrace source endByte afterOperators base output trace) :
      ExpressionUnaryTraceParses postfixTrace source endByte input
        (applyUnaryOperators operators base) output trace

inductive ExpressionUnaryTraceRejects
    (postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | postfixRejected {input afterOperators rejected : Remainder}
      {operators : List (Located UnaryOp)} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixRejected : postfixRejects source endByte afterOperators rejected report trace) :
      ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
