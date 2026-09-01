import Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeFileGrammar

/-! Concrete ordinary grammar for complete canonical Core source files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concrete ordinary top-level item grammar using public Core terms and
isolated public bodies under their exact tail policies. -/
abbrev CoreTopItemOrdinaryParses :=
  TopItemParses CoreExpressionOrdinaryParses
    (IsolatedCoreBlockPublicOrdinaryParses .allow)
    (IsolatedCoreBlockPublicOrdinaryParses .require)

/-- Complete ordinary Core-file grammar with exact comment attachment. -/
abbrev CoreSourceFileOrdinaryParses (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) :=
  SourceFileParses CoreTopItemOrdinaryParses file comments

/-- Parser-independent complete-file judgment from the root token window. -/
def CoreSourceFileOrdinaryParsesFromStart (file : Syntax.SourceFile)
    (tokens : List Syntax.Token) (comments : List Syntax.Comment)
    (parsedFile : Syntax.ParsedFile) : Prop :=
  ∃ output : Remainder,
    CoreSourceFileOrdinaryParses file comments {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := 0
    } parsedFile output

/-- A complete ordinary Core-file derivation reaches its active-window end. -/
theorem CoreSourceFileOrdinaryParses.output_atEnd
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input output : Remainder} {parsedFile : Syntax.ParsedFile}
    (parsed : CoreSourceFileOrdinaryParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor :=
  SourceFileParses.output_atEnd parsed

end Solcore.Syntax.DeclarativeGrammar
