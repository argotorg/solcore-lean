import Solcore.Syntax.DeclarativeIdentifierCascadeProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Protected spelling events remain exact after mixed-prefix normalization. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserProtectedDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.append
example := @parseDiagnosticCascadeFilters_of_protected
example := @IdentifierDiagnosticTrace.not_candidate
example := @IdentifierDiagnosticTrace.cascadeFilters

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {name : Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    filterParseDiagnostics file lexical trace = trace :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (diagnostics.cascadeFilters file.content (lexical.map (·.span)))

/-- Earlier mixed reports are normalized, then the spelling suffix is retained
unchanged; neither prefix metadata nor suffix order is silently discarded. -/
theorem identifier_suffix_survives
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {name : Identifier} {prior kept trace : List ParseDiagnostic}
    (leading : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) prior kept)
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = kept ++ trace :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (leading.append (diagnostics.cascadeFilters file.content (lexical.map (·.span))))

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {leftName rightName : Identifier} {left right : List ParseDiagnostic}
    (leftTrace : IdentifierDiagnosticTrace leftName left)
    (rightTrace : IdentifierDiagnosticTrace rightName right) :
    filterParseDiagnostics file lexical (left ++ right) = left ++ right :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    ((leftTrace.cascadeFilters file.content (lexical.map (·.span))).append
      (rightTrace.cascadeFilters file.content (lexical.map (·.span))))

end Solcore.Test.SyntaxParserProtectedDiagnosticTraceProperties
