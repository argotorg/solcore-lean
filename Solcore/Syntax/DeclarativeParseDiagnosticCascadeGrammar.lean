import Solcore.Syntax.DeclarativeDiagnosticCascadeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent normalization of complete, potentially mixed diagnostic traces.
The diagnostic catalog is shared data, not a parser or an execution witness. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Only unexpected-token reports and recovery events have cascade provenance.
Identifier, grammar-constraint, and nesting reports are always protected. -/
def LexicalCascadeCandidate : ParseDiagnosticKind → Prop
  | .unexpected .. | .recovered .. => True
  | _ => False

/-- A removable report needs both a candidate kind and a lexical span witness. -/
def ParseDiagnosticCascadeSuppresses (source : String)
    (lexical : List SourceSpan) (diagnostic : ParseDiagnostic) : Prop :=
  LexicalCascadeCandidate diagnostic.kind ∧
    LexicalCascadeSuppresses source lexical diagnostic.span

/-- Keep or drop each complete report in place, preserving metadata and duplicates. -/
inductive ParseDiagnosticCascadeFilters (source : String) (lexical : List SourceSpan) :
    List ParseDiagnostic → List ParseDiagnostic → Prop where
  | nil : ParseDiagnosticCascadeFilters source lexical [] []
  | keep {diagnostic : ParseDiagnostic} {raw kept : List ParseDiagnostic}
      (retained : ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic)
      (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
      ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) (diagnostic :: kept)
  | drop {diagnostic : ParseDiagnostic} {raw kept : List ParseDiagnostic}
      (suppressed : ParseDiagnosticCascadeSuppresses source lexical diagnostic)
      (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
      ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) kept

end Solcore.Syntax.DeclarativeGrammar
