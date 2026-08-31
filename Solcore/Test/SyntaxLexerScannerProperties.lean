import Solcore

/-! External compile consumers for canonical lexer scanner laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (leading trailing : List Char) :
    byteSize (leading ++ trailing) =
      byteSize leading + byteSize trailing :=
  byteSize_append leading trailing

example (predicate : Char → Bool) (characters : List Char) :
    characters =
      (takeWhile predicate characters).consumed ++
        (takeWhile predicate characters).remaining :=
  takeWhile_partition predicate characters

example (predicate : Char → Bool) (startByte : Nat)
    (characters : List Char) :
    let scan := takeWhile predicate characters
    Advances startByte characters
      (startByte + byteSize scan.consumed) scan.remaining :=
  takeWhile_advances predicate startByte characters

example (text : String) (keyword : HardKeyword)
    (recognized : HardKeyword.ofString? text = some keyword) :
    keyword.spelling = text :=
  HardKeyword.spelling_eq_of_ofString?_eq_some text keyword recognized

end Tests
