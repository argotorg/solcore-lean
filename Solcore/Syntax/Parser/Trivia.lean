import Solcore.Syntax.Parser.Result

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Rust 1.97.0 `char::is_whitespace`, used by comment attachment. -/
def isRustWhitespace (character : Char) : Bool :=
  let value := character.val.toNat
  (0x09 ≤ value && value ≤ 0x0D) || value == 0x20 ||
    value == 0x85 || value == 0xA0 || value == 0x1680 ||
    (0x2000 ≤ value && value ≤ 0x200A) ||
    value == 0x2028 || value == 0x2029 || value == 0x202F ||
    value == 0x205F || value == 0x3000

/-- Validated UTF-8 byte slicing equivalent to Rust `str::get`. -/
def utf8Slice? (source : String) (startByte endByte : Nat) : Option String :=
  if startByte ≤ endByte && endByte ≤ source.utf8ByteSize &&
      isUtf8Boundary source startByte && isUtf8Boundary source endByte then
    String.fromUTF8?
      (source.toByteArray.extract startByte endByte)
  else
    none

private def allRustWhitespace (text : String) : Bool :=
  text.toList.all isRustWhitespace

private def lineBreakCountChars : List Char → Nat
  | [] => 0
  | '\r' :: '\n' :: rest => lineBreakCountChars rest + 1
  | '\r' :: rest | '\n' :: rest => lineBreakCountChars rest + 1
  | _ :: rest => lineBreakCountChars rest

/-- Count CRLF as one break and lone CR/LF as one, exactly as upstream. -/
def lineBreakCount (text : String) : Nat :=
  lineBreakCountChars text.toList

private def lineStartByteAux :
    Nat → Nat → Nat → List Char → Nat
  | _, _, lastStart, [] => lastStart
  | limit, cursor, lastStart, character :: rest =>
      if cursor ≥ limit then
        lastStart
      else
        let next := cursor + character.utf8Size
        let updated :=
          if character == '\r' || character == '\n' then next else lastStart
        lineStartByteAux limit next updated rest

private def lineStartByte (source : String) (limit : Nat) : Nat :=
  lineStartByteAux limit 0 0 source.toList

private def gapHasCode (source : String)
    (startByte endByte : Nat) : Bool :=
  match utf8Slice? source startByte endByte with
  | some gap => !allRustWhitespace gap
  | none => true

private def codeBeforeCommentAux (source : String)
    (lineStart targetStart : Nat) : List Comment → Nat → Bool
  | [], cursor => gapHasCode source cursor targetStart
  | previous :: rest, cursor =>
      if previous.span.startByte ≥ targetStart then
        gapHasCode source cursor targetStart
      else if previous.span.startByte < lineStart ||
          previous.span.endByte > targetStart then
        codeBeforeCommentAux source lineStart targetStart rest cursor
      else if gapHasCode source cursor previous.span.startByte then
        true
      else
        codeBeforeCommentAux source lineStart targetStart rest
          previous.span.endByte

private def commentHasCodeBeforeItOnLine (source : String)
    (comments : List Comment) (comment : Comment) : Bool :=
  let lineStart := lineStartByte source comment.span.startByte
  codeBeforeCommentAux source lineStart comment.span.startByte
    comments lineStart

private def attachBeforeAux (source : String) (allComments : List Comment) :
    Nat → List Comment → List Comment → List Comment
  | _, [], attached => attached
  | cursor, comment :: rest, attached =>
      match utf8Slice? source comment.span.endByte cursor with
      | none => attached
      | some gap =>
          if !allRustWhitespace gap || lineBreakCount gap > 1 ||
              commentHasCodeBeforeItOnLine source allComments comment then
            attached
          else
            attachBeforeAux source allComments comment.span.startByte rest
              (comment :: attached)

/-- Consecutive source comments directly documenting a declaration. -/
def commentsDirectlyBefore (source : String) (comments : List Comment)
    (declarationStart : Nat) : List Comment :=
  let candidates := (comments.filter fun comment =>
    comment.span.endByte ≤ declarationStart).reverse
  attachBeforeAux source comments declarationStart candidates []

/-- Attach leading comments without changing a top item's source span. -/
def attachTopItemComments (file : SourceFile) (comments : List Comment)
    (item : TopItem) : TopItem := {
  item with
  leadingComments := commentsDirectlyBefore file.content comments
    item.span.startByte
}

end Solcore.Syntax.Parser
