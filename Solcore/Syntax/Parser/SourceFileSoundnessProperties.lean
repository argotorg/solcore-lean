import Solcore.Syntax.DeclarativeFileGrammar
import Solcore.Syntax.Parser.FileCompleteProperties
import Solcore.Syntax.Parser.FileItemsSoundnessProperties
import Solcore.Syntax.Parser.TopItemSoundnessProperties

/-! Parametric diagnostic-free soundness for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/--
Every diagnostic-free complete-file success follows the strict top-item
grammar and the exact pure comment-attachment transformation.
-/
theorem sourceFile_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
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
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.SourceFileParses
      (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
        requiredBodyParses)
      input.file comments input.declarativeRemainder parsedFile
        next.declarativeRemainder := by
  unfold sourceFile at result
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error => simp [itemsResult] at result
  | reject failure rejected => simp [itemsResult] at result
  | ok rawItems afterItems =>
      simp only [itemsResult] at result
      cases result
      rcases parseItems_success_sound_of_diagnosticFree
          (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
            requiredBodyParses)
          (fun itemFree itemResult =>
            topItem_success_sound expressionParses allowBodyParses
              requiredBodyParses expressionReflects expressionSound
              allowBodyReflects allowBodySound requiredBodyReflects
              requiredBodySound itemFree
                (by simpa only [parseItemsItem] using itemResult))
          (fun itemResult itemFree =>
            topItem_reflectsDiagnosticFreeOnSuccess expressionReflects
              allowBodyReflects requiredBodyReflects _ _ _
                (by simpa only [parseItemsItem] using itemResult) itemFree)
          diagnosticFree itemsResult with
        ⟨suffix, itemsEq, itemsGrammar⟩
      have rawItemsEq : rawItems = suffix := by
        simpa using itemsEq
      subst rawItems
      exact .parsed itemsGrammar

/-- Complete-file grammar soundness composes with canonical source validity. -/
theorem sourceFile_success_sound_and_validFor
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
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
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.SourceFileParses
        (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
          requiredBodyParses)
        input.file comments input.declarativeRemainder parsedFile
          next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile := by
  refine ⟨sourceFile_success_sound expressionParses allowBodyParses
    requiredBodyParses expressionReflects expressionSound allowBodyReflects
    allowBodySound requiredBodyReflects requiredBodySound diagnosticFree result,
    ?_⟩
  have valid := sourceFile_complete_reply_validFor inputValid commentsValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.FileInternals
