import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent spelling and diagnostic traces for one identifier token. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A written identifier contains the ASCII hyphen character. -/
def IdentifierHyphenSpelling (text : String) : Prop :=
  '-' ∈ text.toList

/-- Checked identifiers emit one located spelling diagnostic exactly when
their written name contains a hyphen, regardless of its multiplicity. -/
inductive IdentifierDiagnosticTrace (name : Syntax.Identifier) :
    List ParseDiagnostic → Prop where
  | clean (absent : ¬ IdentifierHyphenSpelling name.value) :
      IdentifierDiagnosticTrace name []
  | hyphen (present : IdentifierHyphenSpelling name.value) :
      IdentifierDiagnosticTrace name
        [{ span := name.span, kind := .invalidIdentifierHyphen name.value }]

/-- Raw identifier success retains its exact token and emits no event. -/
inductive RawIdentifierTraceParses :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (ordinary : IdentifierParses input name output) :
      RawIdentifierTraceParses input name output []

/-- Checked identifier success pairs the existing token grammar with its
independent spelling trace, in emission order after all earlier diagnostics. -/
inductive IdentifierTraceParses :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      {trace : List ParseDiagnostic}
      (ordinary : IdentifierParses input name output)
      (diagnostics : IdentifierDiagnosticTrace name trace) :
      IdentifierTraceParses input name output trace

end Solcore.Syntax.DeclarativeGrammar
