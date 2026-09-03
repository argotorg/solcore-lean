import Solcore.Syntax.DeclarativeImportDeclExactnessProperties
import Solcore.Syntax.DeclarativeExportDeclExactnessProperties
import Solcore.Syntax.DeclarativePlainTopItemExactnessProperties
import Solcore.Syntax.DeclarativeTopItemExactnessProperties
import Solcore.Syntax.DeclarativePublicSourceFileValueProperties

/-! Unconditional complete-file syntax exactness from every declaration branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every prioritized attribute-free declaration now has an exact outcome. -/
theorem plainTopItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects :=
  plainTopItemExactOutcomeSpecOfModuleDeclarations
    importDeclExactOutcomeSpec exportDeclExactOutcomeSpec

/-- Leading derive attributes preserve unconditional top-item exactness. -/
theorem topItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects :=
  topItemExactOutcomeSpecOfPlain plainTopItemExactOutcomeSpec

/-- Recovery-aware file loops have exact source-order AST lists and endpoints. -/
theorem fileItemsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects :=
  fileItemsExactOutcomeSpecOfTopItem topItemExactOutcomeSpec

/-- Fixed source provenance and comments give an exact complete raw-file result. -/
theorem sourceFileExactOutcomeSpec (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments) SourceFileRejects :=
  sourceFileExactOutcomeSpecOfTopItem topItemExactOutcomeSpec file comments

/-- Attribute-free top items have one complete located AST and remainder. -/
theorem PlainTopItemOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TopItem}
    (leftParsed : PlainTopItemOrdinaryParses input left afterLeft)
    (rightParsed : PlainTopItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  plainTopItemExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Derive-aware top items have one complete located AST and remainder. -/
theorem TopItemOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TopItem}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  topItemExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Attribute-free declaration rejection fixes the first failing remainder. -/
theorem PlainTopItemRejects.output_unique {input left right : Remainder}
    (leftRejected : PlainTopItemRejects input left)
    (rightRejected : PlainTopItemRejects input right) : left = right :=
  plainTopItemExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Derive-aware declaration rejection fixes the first failing remainder. -/
theorem TopItemRejects.output_unique {input left right : Remainder}
    (leftRejected : TopItemRejects input left)
    (rightRejected : TopItemRejects input right) : left = right :=
  topItemExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- A recovery-aware file loop fixes the complete forward item list and remainder. -/
theorem FileItemsOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.TopItem}
    (leftParsed : FileItemsOrdinaryParses input left afterLeft)
    (rightParsed : FileItemsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  fileItemsExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Comment attachment preserves unconditional complete source-file exactness. -/
theorem SourceFileOrdinaryParses.result_unique
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input afterLeft afterRight : Remainder} {left right : Syntax.ParsedFile}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  (sourceFileExactOutcomeSpec file comments).successResultUnique leftParsed rightParsed

/-- Public source syntax has one AST, including nesting-overflow and recovery.
No public remainder, diagnostic trace, or rejection payload is part of this relation. -/
theorem PublicSourceFileOrdinaryParses.value_unique
    {file : Syntax.SourceFile} {tokens : List Syntax.Token} {comments : List Syntax.Comment}
    {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) : left = right :=
  leftParsed.value_unique_of_exact_topItem topItemExactOutcomeSpec rightParsed

end Solcore.Syntax.DeclarativeGrammar
