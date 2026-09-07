import Solcore.Syntax.DeclarativeCoreBlockGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent source-ordered diagnostics for Core expression semicolons.
Non-final statements are checked under both policies. Only the final statement
is exempt under `allow`; every missing required semicolon contributes one event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A mandatory statement-termination check emits exactly one constraint
report at the full statement span, or no report when termination is valid. -/
inductive CoreBlockStatementDiagnosticTrace (statement : Syntax.Statement) :
    List ParseDiagnostic → Prop where
  | clean (terminated : CoreBlockStatementTerminated statement) :
      CoreBlockStatementDiagnosticTrace statement []
  | missing (unterminated : ¬ CoreBlockStatementTerminated statement) :
      CoreBlockStatementDiagnosticTrace statement
        [{ span := statement.span, kind := .constraintViolation .expressionRequiresSemicolon }]

/-- Complete tail validation follows written statement order. The separate
singleton constructors make the final-statement policy explicit. -/
inductive CoreBlockTailsDiagnosticTrace :
    CoreBlockTailPolicy → List Syntax.Statement → List ParseDiagnostic → Prop where
  | nil {policy : CoreBlockTailPolicy} : CoreBlockTailsDiagnosticTrace policy [] []
  | lastAllowed {last : Syntax.Statement} : CoreBlockTailsDiagnosticTrace .allow [last] []
  | lastRequired {last : Syntax.Statement} {trace : List ParseDiagnostic}
      (checked : CoreBlockStatementDiagnosticTrace last trace) :
      CoreBlockTailsDiagnosticTrace .require [last] trace
  | cons {policy : CoreBlockTailPolicy} {first second : Syntax.Statement}
      {rest : List Syntax.Statement} {headTrace tailTrace : List ParseDiagnostic}
      (checked : CoreBlockStatementDiagnosticTrace first headTrace)
      (tail : CoreBlockTailsDiagnosticTrace policy (second :: rest) tailTrace) :
      CoreBlockTailsDiagnosticTrace policy (first :: second :: rest) (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
