import Solcore.Syntax.DeclarativeCoreLiteralOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Exact independent silent traces for Core literals and Boolean builtins.
Literal spellings and Boolean identifier-shaped ASTs remain unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def CoreLiteralTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (literal : Syntax.CoreLiteral) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  CoreLiteralParses input literal output ∧ trace = []

def BooleanIdentifierTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (name : Syntax.Identifier) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanIdentifierParses input name output ∧ trace = []

/-- Literal rejection retains its ordinary relation and full uncommitted
`coreLiteral` expectation in expression context, with no added event. -/
def CoreLiteralTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  CoreLiteralRejects input rejected ∧
    RejectAtReports source endByte { head := .coreLiteral, tail := [] }
      .expression rejected diagnostic ∧ trace = []

/-- Boolean absence reuses the existing true/false absence predicate. Its
failure expects an expression, not a Core literal or ordinary identifier. -/
def BooleanIdentifierTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanPatternAbsentAt input ∧ rejected = input ∧
    RejectAtReports source endByte { head := .expression, tail := [] }
      .expression input diagnostic ∧ trace = []

def LiteralExpressionTraceParses (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Syntax.Expr) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  LiteralExpressionParses input value output ∧ trace = []

abbrev LiteralExpressionTraceRejects := CoreLiteralTraceRejects

end Solcore.Syntax.DeclarativeGrammar
