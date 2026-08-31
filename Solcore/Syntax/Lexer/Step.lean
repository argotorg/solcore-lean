import Solcore.Syntax.Lexer.State

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

private def emitTextToken (file : SourceFile) (state : State)
    (kind : TokenKind) (remaining : List Char) : State :=
  let endByte := state.cursor + kind.spelling.utf8ByteSize
  state.emitToken file endByte remaining kind

private def scanLine (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  let scan := scanLineComment (state.cursor + 2) remaining
  state.emitComment file scan.endByte scan.remaining .line
    (String.ofList scan.body)

private def scanBlock (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanBlockComment (state.cursor + 2) 1 remaining [] with
  | .closed endByte body rest =>
      state.emitComment file endByte rest .block (String.ofList body)
  | .unterminated =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .unterminatedBlockComment

private def scanBacktick (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanDelimitedMeta '`' (state.cursor + 1) remaining ['`'] with
  | some scan =>
      state.emitToken file scan.endByte scan.remaining
        (.yulMetaBacktick scan.spelling)
  | none =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .invalidToken

private def scanInterpolation (file : SourceFile) (state : State)
    (remaining : List Char) : Option State :=
  match scanDelimitedMeta '}' (state.cursor + 2) remaining ['{', '$'] with
  | some scan =>
      some (state.emitToken file scan.endByte scan.remaining
        (.yulMetaInterpolation scan.spelling))
  | none => none

private def scanQuoted (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanQuotedString state.cursor remaining with
  | .closed endByte spelling _decoded rest =>
      state.emitToken file endByte rest (.stringLiteral spelling)
  | .invalidEscape _ _ _escape tokenEndByte rest =>
      state.recover file state.cursor tokenEndByte tokenEndByte rest
        .invalidStringEscape
  | .invalidPrefix endByte rest =>
      state.recover file state.cursor endByte endByte rest
        .invalidToken
  | .unterminated =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .invalidToken

private def scanDecimal (file : SourceFile) (state : State)
    (characters : List Char) : State :=
  let scan := takeWhile isAsciiDigit characters
  let spelling := String.ofList scan.consumed
  emitTextToken file state (.decimalLiteral spelling) scan.remaining

private def scanHexadecimal? (file : SourceFile) (state : State)
    (remaining : List Char) : Option State :=
  match remaining with
  | 'x' :: digit :: rest =>
      if isAsciiHexDigit digit then
        let tail := takeWhile isAsciiHexDigit rest
        let spelling := String.ofList ('0' :: 'x' :: digit :: tail.consumed)
        some (emitTextToken file state (.hexadecimalLiteral spelling)
          tail.remaining)
      else none
  | _ => none

private def scanLetterName (file : SourceFile) (state : State)
    (first : Char) (remaining : List Char) : State :=
  let scan := scanLetterIdentifier first remaining
  emitTextToken file state scan.kind scan.remaining

private def scanMarkedName (file : SourceFile) (state : State)
    (first : Char) (remaining : List Char) : State :=
  let scan := scanMarkedYulIdentifier first remaining
  emitTextToken file state scan.kind scan.remaining

private def emitSymbol (file : SourceFile) (state : State)
    (symbol : Symbol) (remaining : List Char) : State :=
  emitTextToken file state (.symbol symbol) remaining

/--
Perform one maximal-munch transition. Callers only use this on nonempty input;
every branch consumes at least one source character.
-/
def step (file : SourceFile) (state : State) : State :=
  match state.remaining with
  | [] => state
  | first :: rest =>
      if isWhitespace first then
        state.skipTo (state.cursor + first.utf8Size) rest
      else
        match first, rest with
        | '/', '/' :: tail => scanLine file state tail
        | '/', '*' :: tail => scanBlock file state tail
        | '`', tail => scanBacktick file state tail
        | '"', tail => scanQuoted file state tail
        | '$', '{' :: tail =>
            match scanInterpolation file state tail with
            | some next => next
            | none => scanMarkedName file state '$' ('{' :: tail)
        | '0', tail =>
            match scanHexadecimal? file state tail with
            | some next => next
            | none => scanDecimal file state ('0' :: tail)
        | digit, tail =>
            if isAsciiDigit digit then
              scanDecimal file state (digit :: tail)
            else if isCoreIdentifierStart digit then
              scanLetterName file state digit tail
            else
              match digit, tail with
              | '_', next :: after =>
                  if isYulIdentifierContinue next then
                    scanMarkedName file state '_' (next :: after)
                  else
                    emitSymbol file state .underscore (next :: after)
              | '_', [] => emitSymbol file state .underscore []
              | '$', after => scanMarkedName file state '$' after
              | left, right :: after =>
                  match multiSymbol? left right with
                  | some symbol => emitSymbol file state symbol after
                  | none =>
                      match singleSymbol? left with
                      | some symbol =>
                          emitSymbol file state symbol (right :: after)
                      | none =>
                          state.recover file state.cursor
                            (state.cursor + left.utf8Size)
                            (state.cursor + left.utf8Size) (right :: after)
                            .invalidToken
              | character, [] =>
                  match singleSymbol? character with
                  | some symbol => emitSymbol file state symbol []
                  | none =>
                      state.recover file state.cursor
                        (state.cursor + character.utf8Size)
                        (state.cursor + character.utf8Size) []
                        .invalidToken

end Solcore.Syntax.Lexer
