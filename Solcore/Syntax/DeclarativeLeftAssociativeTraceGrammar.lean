import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent maximal left-associative traces at one binary precedence.
Selected operators are consumed silently; only supplied operand events are
concatenated in source order. The exact terminal report remains uncommitted.
Operand success has no added progress, token-carrier, or numeric-window rule. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LeftAssociativeTailTraceParses
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} {left : Syntax.Expr}
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input) :
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input left left input []
  | next {input afterOperator afterRight output : Remainder}
      {left right expression : Syntax.Expr} {operator : Located BinaryOp}
      {rightEvents tailEvents : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightParsed : operandTrace source endByte afterOperator right afterRight rightEvents)
      (tail : LeftAssociativeTailTraceParses operandTrace precedence source endByte afterRight
        (binaryNode left operator right) expression output tailEvents) :
      LeftAssociativeTailTraceParses operandTrace precedence source endByte input left expression output
        (rightEvents ++ tailEvents)

inductive LeftAssociativeTailTraceRejects
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rightRejected {input afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightRejected : operandRejects source endByte afterOperator rejected report trace) :
      LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input left rejected report trace
  | laterRejected {input afterOperator afterRight rejected : Remainder}
      {left right : Syntax.Expr} {operator : Located BinaryOp} {report : ParseDiagnostic}
      {rightEvents tailEvents : List ParseDiagnostic}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input operator afterOperator)
      (rightParsed : operandTrace source endByte afterOperator right afterRight rightEvents)
      (tailRejected : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
        afterRight (binaryNode left operator right) rejected report tailEvents) :
      LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte input left rejected report
        (rightEvents ++ tailEvents)

inductive LeftAssociativeTraceParses
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterLeft output : Remainder} {left expression : Syntax.Expr}
      {leftEvents tailEvents : List ParseDiagnostic}
      (leftParsed : operandTrace source endByte input left afterLeft leftEvents)
      (tailParsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte
        afterLeft left expression output tailEvents) :
      LeftAssociativeTraceParses operandTrace precedence source endByte input expression output (leftEvents ++ tailEvents)

inductive LeftAssociativeTraceRejects
    (operandTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (precedence : Nat) (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | firstRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (firstRejected : operandRejects source endByte input rejected report trace) :
      LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report trace
  | tailRejected {input afterLeft rejected : Remainder} {left : Syntax.Expr} {report : ParseDiagnostic}
      {leftEvents tailEvents : List ParseDiagnostic}
      (leftParsed : operandTrace source endByte input left afterLeft leftEvents)
      (tailRejected : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte
        afterLeft left rejected report tailEvents) :
      LeftAssociativeTraceRejects operandTrace operandRejects precedence source endByte input rejected report
        (leftEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
