import Solcore.Syntax.Parser.SourceFileSoundnessProperties

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

example := @FileInternals.plainTopItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.plainTopItem_success_sound
example := @FileInternals.attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.topItem_reflectsDiagnosticFreeOnSuccess
example := @FileInternals.topItem_success_sound
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
