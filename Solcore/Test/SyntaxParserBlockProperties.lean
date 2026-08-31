import Solcore.Syntax.Parser.Block

/-! External consumers for canonical Core-block progress contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @coreBlock_preservesTokensOnSuccess
example := @coreBlock_preservesTokenWindow
example := @coreBlock_cursor_lt_onSuccess
example := @coreBlock_cursorMonotoneOnSuccess
example := @coreBlock_startsAtCurrentTokenOnSuccess
example := @coreBlock_validFor
example := @BlockInternals.captureBlockTail_validFor
example := @BlockInternals.captureBlock?_validFor
example := @BlockInternals.captureBlock?_startsAtCurrentToken
example := @hasBalancedBlockCapture
example := @isolateBlock_validFor
example := @isolateBlock_preservesTokensOnSuccess
example := @isolateBlock_preservesTokenWindow
example := @isolateBlock_cursor_lt_onSuccess_of_balancedCapture
example := @isolateBlock_cursorMonotoneOnSuccess
example := @isolateBlock_startsAtCurrentTokenOnSuccess

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (coreBlock statement policy) :=
  coreBlock_preservesTokenWindow statement policy statementShape

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (coreBlock statement policy) :=
  coreBlock_preservesTokensOnSuccess statement policy statementShape

example (statementValid : SourceFile → Statement → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (valid : statement.ValidFor statementValid)
    (shape : Parser.PreservesTokensOnSuccess statement)
    (spanValid : ∀ file retained,
      statementValid file retained → retained.span.ValidFor file) :
    (coreBlock statement policy).ValidFor (Block.ValidFor statementValid) :=
  coreBlock_validFor statementValid statement policy valid shape spanValid

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : Block}
    (result : coreBlock statement policy input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  ⟨coreBlock_preservesTokensOnSuccess statement policy statementShape
      input body next result,
    coreBlock_cursor_lt_onSuccess statement policy result⟩

example (parser : Parser Block)
    (shape : Parser.PreservesTokensOnSuccess parser)
    (monotone : Parser.CursorMonotoneOnSuccess parser) :
    Parser.PreservesTokensOnSuccess (isolateBlock parser) ∧
      Parser.CursorMonotoneOnSuccess (isolateBlock parser) :=
  ⟨isolateBlock_preservesTokensOnSuccess parser shape,
    isolateBlock_cursorMonotoneOnSuccess parser monotone⟩

example (parser : Parser Block)
    (shape : Parser.PreservesTokenWindow parser) :
    Parser.PreservesTokenWindow (isolateBlock parser) :=
  isolateBlock_preservesTokenWindow parser shape

example (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Block)
    (valid : parser.ValidFor (Block.ValidFor statementValid)) :
    (isolateBlock parser).ValidFor (Block.ValidFor statementValid) :=
  isolateBlock_validFor statementValid parser valid

example (parser : Parser Block)
    (starts : Parser.StartsAtCurrentTokenOnSuccess parser (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess (isolateBlock parser) (·.span) :=
  isolateBlock_startsAtCurrentTokenOnSuccess parser starts

example (parser : Parser Block) {input next : State} {body : Block}
    (captured : hasBalancedBlockCapture input = true)
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor :=
  isolateBlock_cursor_lt_onSuccess_of_balancedCapture parser captured result

example {input : State} {captured : BlockInternals.CapturedBlock}
    (inputValid : input.ValidFor)
    (result : BlockInternals.captureBlock? input = some captured) :
    captured.span.ValidFor input.file ∧
      input.cursor < captured.window.endIndex ∧
      captured.window.endIndex ≤ input.window.endIndex ∧
      captured.window.endIndex ≤ input.tokens.size ∧
      captured.window.endByte ≤ input.file.content.utf8ByteSize ∧
      isUtf8Boundary input.file.content captured.window.endByte = true ∧
      (input.enterWindow input.cursor captured.window).ValidFor := by
  have valid :=
    BlockInternals.captureBlock?_validFor inputValid result
  exact ⟨valid.span, valid.cursor_lt_endIndex, valid.endIndex_le_window,
    valid.endIndex_le_tokens, valid.endByte_le_source,
    valid.endByte_boundary, valid.entered⟩

end Tests
