import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.TriviaAttachment

/-! Parser-independent grammar for complete comment-attached syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
Exact complete-file grammar over an abstract top-item judgment.

The item loop recognizes raw declarations with empty parser-time comment
fields.  The pure syntax trivia transformation then attaches the complete
source-order comment stream exactly as retained by the canonical AST.
-/
inductive SourceFileParses
    (itemParses : Remainder → Syntax.TopItem → Remainder → Prop)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    Remainder → Syntax.ParsedFile → Remainder → Prop where
  | parsed {input output : Remainder} {rawItems : List Syntax.TopItem}
      (itemsParsed : TopItemsParses itemParses input rawItems output) :
      SourceFileParses itemParses file comments input {
        source := file.id
        span := SourceSpan.fullFile file
        items := rawItems.map
          (Syntax.Trivia.attachTopItemComments file comments)
        comments
      } output

/-- A complete-file derivation consumes its whole active token window. -/
theorem SourceFileParses.output_atEnd
    {itemParses : Remainder → Syntax.TopItem → Remainder → Prop}
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input output : Remainder} {parsedFile : Syntax.ParsedFile}
    (parsed : SourceFileParses itemParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor := by
  cases parsed with
  | parsed itemsParsed => exact itemsParsed.output_atEnd

end Solcore.Syntax.DeclarativeGrammar
