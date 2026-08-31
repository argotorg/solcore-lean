import Solcore.Syntax.Lexer.Properties

/-! External compile consumers for the public lexical contract. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example {α : Type} (file : SourceFile) (spanOf : α → SourceSpan)
    (items : List α)
    (spanValid : ∀ item ∈ items, (spanOf item).ValidFor file)
    (spanNonempty : ∀ item ∈ items,
      (spanOf item).startByte < (spanOf item).endByte)
    (ordered : items.Pairwise fun left right =>
      (spanOf left).endByte ≤ (spanOf right).startByte) :
    SpanSequence.ValidFor file spanOf 0 items :=
  SpanSequence.ValidFor.of_forall_pairwise spanValid
    (fun item _member => Nat.zero_le (spanOf item).startByte)
    spanNonempty ordered

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    (state.finish file).ValidFor file :=
  ordered.finish_validFor

example (file : SourceFile) (fuel : Nat) (state : State)
    (lexed : LexedFile) (ordered : state.OrderedValidFor file)
    (result : lexLoop file fuel state = .ok lexed) :
    lexed.ValidFor file :=
  lexLoop_ok_validFor file fuel state lexed ordered result

example (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) : lexed.ValidFor file :=
  lex_ok_validFor file lexed result

example (file : SourceFile) :
    ∃ lexed, lex file = .ok lexed ∧ lexed.ValidFor file :=
  lex_total_validFor file

end Tests
