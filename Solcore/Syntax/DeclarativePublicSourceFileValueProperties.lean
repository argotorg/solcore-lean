import Solcore.Syntax.DeclarativePublicSourceFileOutcomeProperties
import Solcore.Syntax.DeclarativeSourceFileExactnessProperties

/-! Exact public syntax values without inventing a public remainder or rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Nesting-branch exclusion and unique top-item values fix the public parsed
file. The hidden raw-grammar remainder is not part of this public conclusion. -/
theorem PublicSourceFileOrdinaryParses.value_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) :
    left = right := by
  cases leftParsed with
  | nestingExceeded leftNesting =>
      cases rightParsed with
      | nestingExceeded => rfl
      | sourceFile rightNesting rightSource =>
          exact False.elim
            (publicSourceFileBranches_disjoint leftNesting rightNesting)
  | sourceFile leftNesting leftSource =>
      cases rightParsed with
      | nestingExceeded rightNesting =>
          exact False.elim
            (publicSourceFileBranches_disjoint rightNesting leftNesting)
      | sourceFile rightNesting rightSource =>
          exact (sourceFileExactOutcomeSpecOfTopItemValues itemValues file
            comments).successValueUnique leftSource rightSource

/-- An exact top-item contract supplies public parsed-file value uniqueness. -/
theorem PublicSourceFileOrdinaryParses.value_unique_of_exact_topItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects)
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) :
    left = right :=
  leftParsed.value_unique_of_topItem itemOutcomes.successValueUnique rightParsed

end Solcore.Syntax.DeclarativeGrammar
