import Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionGrammar
import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceGrammar
import Solcore.Syntax.DeclarativeExpressionNameTraceGrammar
import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceGrammar
import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceGrammar
import Solcore.Syntax.DeclarativeArrayLiteralTraceGrammar
import Solcore.Syntax.DeclarativeProxyExpressionTraceGrammar
import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceGrammar
import Solcore.Syntax.DeclarativeLambdaExpressionTraceGrammar

/-! One prioritized expression-atom layer over supplied expression and block
trace relations. Literal/name leaves and proxy types are concrete; recovering
lambda parameters and return types are also concrete. Final rejection emits no
event. These judgments do not claim recursive expression or block existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionAtomDispatchFinalTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input : Remainder} {report : ParseDiagnostic}
      (reported : RejectAtReports source endByte { head := .expression, tail := [] } .expression input report) :
      ExpressionAtomDispatchFinalTraceRejects source endByte input input report []

def ExpressionAtomDispatchRawTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (branch : ExpressionAtomDispatchBranch) :
    SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop :=
  match branch with
  | .literal => LiteralExpressionTraceParses
  | .name => IdentifierExpressionTraceParses
  | .dotConstructor => DotConstructorTraceParses nestedTrace
  | .proxy => ProxyExpressionTraceParses TypeExprTraceParses
  | .parenthesized => ParenthesizedExpressionTraceParses nestedTrace
  | .array => ArrayLiteralTraceParses nestedTrace
  | .lambda => LambdaExpressionTraceParses blockTrace
  | .final => fun _ _ _ _ _ _ => False

def ExpressionAtomDispatchRawTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (branch : ExpressionAtomDispatchBranch) :
    SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop :=
  match branch with
  | .literal => LiteralExpressionTraceRejects
  | .name => IdentifierExpressionTraceRejects
  | .dotConstructor => DotConstructorTraceRejects nestedTrace nestedRejects
  | .proxy => ProxyExpressionTraceRejects TypeExprTraceRejects
  | .parenthesized => ParenthesizedExpressionTraceRejects nestedTrace nestedRejects
  | .array => ArrayLiteralTraceRejects nestedTrace nestedRejects
  | .lambda => LambdaExpressionTraceRejects blockRejects
  | .final => ExpressionAtomDispatchFinalTraceRejects

inductive ExpressionAtomDispatchTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | selected {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
      (branch : ExpressionAtomDispatchBranch)
      (selection : ExpressionAtomDispatchSelects input branch)
      (parsed : ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch source endByte input value output trace) :
      ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace

inductive ExpressionAtomDispatchTraceRejects
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | selected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (branch : ExpressionAtomDispatchBranch)
      (selection : ExpressionAtomDispatchSelects input branch)
      (rejection : ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch
        source endByte input rejected report trace) :
      ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
