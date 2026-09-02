import Solcore.Syntax.Parser.SourceFileSoundnessProperties
import Solcore.Syntax.Parser.SourceFileOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PublicNestingExceededOutputProperties

/-! External consumers for parametric complete-file grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TopItemKindsAbsentAt
example := @PlainTopItemParses
example := @TopItemParses
example := @TopItemsParses
example := @SourceFileParses
example := @PlainTopItemTokenPresentAt
example := @PlainTopItemBranch
example := @PlainTopItemBranchSelected
example := @PlainTopItemOrdinaryParses
example := @PlainTopItemRejects
example := @plainTopItemDeterministicOutcomeSpec
example := @TopItemDeriveAttaches
example := @TopItemOrdinaryParses
example := @TopItemRejects
example := @topItemDeterministicOutcomeSpec
example := @TopItemRecoveryStops
example := @TopItemRecoveryScanParses
example := @TopItemRecoveryParses
example := @TopItemRecoveryRejects
example := @topItemRecoveryDeterministicOutcomeSpec
example := @TopItemRejectsWithPreservedWindow
example := @FileItemsOrdinaryParses
example := @FileItemsRejects
example := @fileItemsDeterministicOutcomeSpec
example := @SourceFileOrdinaryParses
example := @SourceFileRejects
example := @sourceFileDeterministicOutcomeSpec
example := @sourceFileRootRemainder
example := @nestingExceededParsedFile
example := @PublicSourceFileOrdinaryParses
example := @publicSourceFileOrdinaryParses_iff
example := @PublicSourceFileOrdinaryParses.shape
example := @PublicSourceFileOrdinaryParses.eq_nestingExceededParsedFile
example := @PublicSourceFileOrdinaryParses.sourceFile_of_clears

example := @FileInternals.plainTopItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.plainTopItem_success_sound
example := @FileInternals.plainTopItem_success_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_reject_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_ordinaryOutcome_sound
example := @FileInternals.plainTopItem_ordinaryOutcomeSpec
example := @FileInternals.attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.attachDeriveAttribute_success_ordinaryOutcome_sound
example := @FileInternals.attachDeriveAttribute_total_success
example := @FileInternals.topItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.topItem_success_sound
example := @FileInternals.topItem_success_ordinaryOutcome_sound
example := @FileInternals.topItem_reject_ordinaryOutcome_sound
example := @FileInternals.topItem_ordinaryOutcome_sound
example := @FileInternals.topItem_ordinaryOutcomeSpec
example := @FileInternals.atTopItemStart_eq_true_of_topItemRecoveryBoundary
example := @FileInternals.topItemRecoveryStops_of_guard_eq_true
example := @FileInternals.topItemRecoveryStops_of_advance?_eq_none
example := @FileInternals.no_topItemRecoveryStops_of_nonBoundary_token
example := @FileInternals.recoverTopItemAux_success_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_success_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_reject_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_ordinaryOutcome_sound
example := @FileInternals.recoverTopItem_ordinaryOutcomeSpec
example := @FileInternals.topItemRejectsWithPreservedWindow_of_result
example := @FileInternals.rewoundTopItem_declarativeRemainder_eq
example := @FileInternals.parseItems_success_ordinaryOutcome_sound_strong
example := @FileInternals.parseItems_reject_ordinaryOutcome_sound
example := @FileInternals.parseItems_ordinaryOutcome_sound
example := @FileInternals.parseItems_ordinaryOutcomeSpec
example := @FileInternals.sourceFile_success_ordinaryOutcome_sound
example := @FileInternals.sourceFile_reject_ordinaryOutcome_sound
example := @FileInternals.sourceFile_ordinaryOutcome_sound
example := @FileInternals.sourceFile_ordinaryOutcomeSpec
example := @parseLexed_ok_publicSourceFileOrdinary_sound
example := @parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor
example := @parse_ok_publicSourceFileOrdinary_sound
example := @parse_ok_publicSourceFileOrdinary_sound_and_validFor
example := @nestingExceededParseOutput
example := @parseLexed_eq_ok_of_nestingExceeds
example := @parseLexed_ok_eq_nestingExceededParseOutput
example := @parseLexed_ok_parseDiagnostics_eq_of_nestingExceeds
example := @FileInternals.parseItems_success_sound_of_diagnosticFree
example := @FileInternals.sourceFile_success_sound
example := @FileInternals.sourceFile_success_sound_and_validFor

example := @TopItemsParses.output_atEnd
example := @SourceFileParses.output_atEnd

example
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Block → Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {comments : List Comment} {input next : State} {parsedFile : ParsedFile}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    SourceFileParses
          (TopItemParses expressionParses allowBodyParses requiredBodyParses)
          input.file comments input.declarativeRemainder parsedFile
            next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile :=
  FileInternals.sourceFile_success_sound_and_validFor expressionParses
    allowBodyParses requiredBodyParses expressionReflects expressionSound
    allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
    inputValid commentsValid diagnosticFree result

example
    {itemParses : Remainder → TopItem → Remainder → Prop}
    {file : SourceFile} {comments : List Comment}
    {input output : Remainder} {parsedFile : ParsedFile}
    (parsed : SourceFileParses itemParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor :=
  parsed.output_atEnd

end Solcore.Test.SyntaxParserFileSoundnessProperties
