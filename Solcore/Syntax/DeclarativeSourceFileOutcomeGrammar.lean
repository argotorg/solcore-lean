import Solcore.Syntax.DeclarativeFileGrammar
import Solcore.Syntax.DeclarativeFileItemsOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recovery-aware file success followed by the pure source-order
comment attachment used by the canonical AST. -/
inductive SourceFileOrdinaryParses
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    Remainder → Syntax.ParsedFile → Remainder → Prop where
  | parsed {input output : Remainder} {rawItems : List Syntax.TopItem}
      (itemsParsed : FileItemsOrdinaryParses input rawItems output) :
      SourceFileOrdinaryParses file comments input {
        source := file.id
        span := SourceSpan.fullFile file
        items := rawItems.map
          (Syntax.Trivia.attachTopItemComments file comments)
        comments
      } output

/-- Complete-file rejection is exactly the item loop's first rejection. -/
inductive SourceFileRejects : Remainder → Remainder → Prop where
  | itemsRejected {input rejected : Remainder}
      (rejection : FileItemsRejects input rejected) :
      SourceFileRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
