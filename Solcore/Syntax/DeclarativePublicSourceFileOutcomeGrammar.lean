import Solcore.Syntax.DeclarativeNestingOutcomeGrammar
import Solcore.Syntax.DeclarativeSourceFileOutcomeGrammar

/-!
Parser-independent broad syntax outcomes at the public source-file boundary.
The relation intentionally exposes neither parser diagnostics nor the final
remainder hidden by the public result type.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Canonical root token window used after public nesting preflight clears. -/
def sourceFileRootRemainder (tokens : List Syntax.Token) : Remainder := {
  tokens := tokens.toArray
  endIndex := tokens.length
  cursor := 0
}

/-- Exact empty syntax value returned when bounded nesting is exceeded. -/
def nestingExceededParsedFile (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) : Syntax.ParsedFile := {
  source := file.id
  span := SourceSpan.fullFile file
  items := []
  comments
}

/--
Broad syntax-only success at the public token-to-file boundary.

An overflowing nesting preflight returns the canonical empty file without
running the token grammar.  A clear preflight runs the recovery-aware file
grammar from the canonical root window; its final remainder is existentially
hidden because the public syntax result does not retain it.
-/
inductive PublicSourceFileOrdinaryParses
    (file : Syntax.SourceFile) (tokens : List Syntax.Token)
    (comments : List Syntax.Comment) : Syntax.ParsedFile → Prop where
  | nestingExceeded {overflow : NestingOverflow}
      (nesting : NestingExceeds tokens overflow) :
      PublicSourceFileOrdinaryParses file tokens comments
        (nestingExceededParsedFile file comments)
  | sourceFile {parsedFile : Syntax.ParsedFile} {final : Remainder}
      (nesting : NestingClears tokens)
      (parsed : SourceFileOrdinaryParses file comments
        (sourceFileRootRemainder tokens) parsedFile final) :
      PublicSourceFileOrdinaryParses file tokens comments parsedFile

end Solcore.Syntax.DeclarativeGrammar
