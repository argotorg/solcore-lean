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

example (file : SourceFile) :
    CursorSuffix file 0 file.content.toList :=
  CursorSuffix.initial file

example (file : SourceFile) (cursor : Nat) (remaining : List Char)
    (suffix : CursorSuffix file cursor remaining) :
    file.content.utf8ByteSize = cursor + byteSize remaining :=
  suffix.remainingByteSize

example (file : SourceFile) (cursor : Nat) (remaining : List Char)
    (suffix : CursorSuffix file cursor remaining) :
    isUtf8Boundary file.content cursor = true :=
  suffix.boundary

example (file : SourceFile) (startByte : Nat) (input : List Char)
    (suffix : CursorSuffix file startByte input)
    (predicate : Char → Bool) :
    let scan := takeWhile predicate input
    (sourceSpan file startByte
      (startByte + byteSize scan.consumed)).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (takeWhile_advances predicate startByte input)

example (file : SourceFile) (cursor : Nat) (characters : List Char)
    (suffix : CursorSuffix file cursor characters) :
    let scan := scanLineComment cursor characters
    (sourceSpan file cursor scan.endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanLineComment_advances cursor characters)

example (file : SourceFile) (cursor depth : Nat)
    (characters bodyRev : List Char) (endByte : Nat)
    (body remaining : List Char)
    (suffix : CursorSuffix file cursor characters)
    (result : scanBlockComment cursor depth characters bodyRev =
      .closed endByte body remaining) :
    (sourceSpan file cursor endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanBlockComment_closed_advances cursor depth characters bodyRev
      endByte body remaining result)

example (file : SourceFile) (closing : Char) (cursor : Nat)
    (characters spellingRev : List Char) (scan : MetaScan)
    (suffix : CursorSuffix file cursor characters)
    (result : scanDelimitedMeta closing cursor characters spellingRev =
      some scan) :
    (sourceSpan file cursor scan.endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanDelimitedMeta_some_advances closing cursor characters spellingRev
      scan result)

example (file : SourceFile) (startByte endByte : Nat)
    (input remaining : List Char) (spelling decoded : String)
    (suffix : CursorSuffix file startByte ('"' :: input))
    (result : scanQuotedString startByte input =
      .closed endByte spelling decoded remaining) :
    (sourceSpan file startByte endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanQuotedString_closed_advances startByte input endByte spelling
      decoded remaining result)

end Tests
