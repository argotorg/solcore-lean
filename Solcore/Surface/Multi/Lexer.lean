import Solcore.Surface.Multi.Diagnostic

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The successful raw output of the module-local Multi Surface lexer. -/
structure LexedModule where
  source : SourceId
  tokens : List Token
  comments : List Comment
  deriving Repr, BEq, DecidableEq

/-- The exact result and semantic transition count of one lexer execution. -/
structure LexExecution where
  result : Except LexicalDiagnostic LexedModule
  actualUnits : Nat
  deriving Repr

/-- The fixed m2c-v1 lexer transition bound for `sourceBytes` bytes. -/
def lexBound (sourceBytes : Nat) : Nat :=
  16 * (sourceBytes + 1)

@[simp] theorem lexBound_equation (sourceBytes : Nat) :
    lexBound sourceBytes = 16 * (sourceBytes + 1) :=
  rfl

namespace Lexer

private def sourceSpan (file : WorkspaceFile)
    (startByte endByte : Nat) : SourceSpan := {
  source := file.id
  startByte
  endByte
}

private def byteSize (characters : List Char) : Nat :=
  (String.ofList characters).utf8ByteSize

private def isAsciiLower (character : Char) : Bool :=
  'a' <= character && character <= 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' <= character && character <= 'Z'

private def isAsciiLetter (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isAsciiDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' <= character && character <= 'f') ||
    ('A' <= character && character <= 'F')

private def isIdentifierContinue (character : Char) : Bool :=
  isAsciiLetter character || isAsciiDigit character || character == '_'

private def isPragmaContinuation (character : Char) : Bool :=
  isIdentifierContinue character || character == '-'

private def isWhitespace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' ||
    character == '\r' || character.toNat == 12

private def takeWhile (predicate : Char -> Bool) : List Char -> List Char
  | [] => []
  | character :: rest =>
      if predicate character then
        character :: takeWhile predicate rest
      else
        []

private theorem takeWhile_length_pos
    (predicate : Char -> Bool)
    (character : Char)
    (rest : List Char)
    (accepted : predicate character = true) :
    0 < (takeWhile predicate (character :: rest)).length := by
  simp [takeWhile, accepted]

private theorem drop_length_lt_of_pos
    (characters : List Char)
    (count : Nat)
    (positive : 0 < count)
    (nonempty : characters ≠ []) :
    (characters.drop count).length < characters.length := by
  simp only [List.length_drop]
  have charactersPositive : 0 < characters.length :=
    List.length_pos_iff.mpr nonempty
  omega

private def startsWith : List Char -> List Char -> Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && startsWith expectedRest actualRest

private def hasPragmaBoundary (remaining : List Char) : Bool :=
  match remaining with
  | [] => true
  | character :: _ => !isPragmaContinuation character

private def pragmaMatch? (characters : List Char) : Option PragmaKind :=
  let matchesKind (kind : PragmaKind) : Bool :=
    let spelling := kind.spelling.toList
    startsWith spelling characters &&
      hasPragmaBoundary (characters.drop spelling.length)
  if matchesKind .noCoverageCondition then
    some .noCoverageCondition
  else if matchesKind .noPattersonCondition then
    some .noPattersonCondition
  else if matchesKind .noBoundedVariableCondition then
    some .noBoundedVariableCondition
  else if matchesKind .noGenericInstanceFor then
    some .noGenericInstanceFor
  else
    none

/-- Canonical hard-keyword classification after an ASCII identifier wins. -/
def classifyIdentifier (text : String) : TokenKind :=
  match HardKeyword.ofString? text with
  | some keyword => .hardKeyword keyword
  | none => .identifier text

@[simp] theorem classifyIdentifier_equation (text : String) :
    classifyIdentifier text =
      match HardKeyword.ofString? text with
      | some keyword => .hardKeyword keyword
      | none => .identifier text :=
  rfl

private def pendingAfter (kind : TokenKind) : Bool :=
  kind == .hardKeyword .assemblyKw

private def multiSymbol? (first second : Char) : Option Symbol :=
  match first, second with
  | ':', '=' => some .colonEqual
  | '-', '>' => some .arrow
  | '=', '>' => some .fatArrow
  | '=', '=' => some .equalEqual
  | '!', '=' => some .notEqual
  | '>', '=' => some .greaterEqual
  | '<', '=' => some .lessEqual
  | '&', '&' => some .logicalAnd
  | '|', '|' => some .logicalOr
  | '+', '=' => some .plusEqual
  | '-', '=' => some .minusEqual
  | '^', '=' => some .caretEqual
  | '&', '=' => some .ampEqual
  | '|', '=' => some .pipeEqual
  | '%', '=' => some .percentEqual
  | _, _ => none

private def singleSymbol? : Char -> Option Symbol
  | '+' => some .plus
  | '-' => some .minus
  | '*' => some .star
  | '/' => some .slash
  | '%' => some .percent
  | '!' => some .bang
  | '<' => some .less
  | '>' => some .greater
  | '=' => some .equal
  | '|' => some .pipe
  | '&' => some .amp
  | '^' => some .caret
  | '@' => some .at
  | '?' => some .question
  | '.' => some .dot
  | ':' => some .colon
  | ';' => some .semicolon
  | ',' => some .comma
  | '(' => some .leftParen
  | ')' => some .rightParen
  | '{' => some .leftBrace
  | '}' => some .rightBrace
  | '[' => some .leftBracket
  | ']' => some .rightBracket
  | '_' => some .underscore
  | _ => none

private structure LineScanResult where
  endByte : Nat
  consumedCharacters : Nat
  units : Nat

private def scanLineComment : Nat -> List Char -> LineScanResult
  | cursor, [] => {
      endByte := cursor
      consumedCharacters := 0
      units := 0
    }
  | cursor, '\n' :: _ => {
      endByte := cursor
      consumedCharacters := 0
      units := 0
    }
  | cursor, character :: rest =>
      let tail := scanLineComment (cursor + character.utf8Size) rest
      {
        endByte := tail.endByte
        consumedCharacters := tail.consumedCharacters + 1
        units := tail.units + 1
      }

private inductive BlockScanResult where
  | closed
      (endByte : Nat)
      (consumedCharacters : Nat)
      (units : Nat)
  | unterminated (units : Nat)

private def scanBlockComment : Nat -> Nat -> List Char -> BlockScanResult
  | _, _, [] => .unterminated 0
  | cursor, depth, '/' :: '*' :: rest =>
      match scanBlockComment (cursor + 2) (depth + 1) rest with
      | .closed endByte consumed units =>
          .closed endByte (consumed + 2) (units + 1)
      | .unterminated units => .unterminated (units + 1)
  | cursor, 1, '*' :: '/' :: _ =>
      .closed (cursor + 2) 2 1
  | cursor, depth + 2, '*' :: '/' :: rest =>
      match scanBlockComment (cursor + 2) (depth + 1) rest with
      | .closed endByte consumed units =>
          .closed endByte (consumed + 2) (units + 1)
      | .unterminated units => .unterminated (units + 1)
  | cursor, depth, character :: rest =>
      match scanBlockComment (cursor + character.utf8Size) depth rest with
      | .closed endByte consumed units =>
          .closed endByte (consumed + 1) (units + 1)
      | .unterminated units => .unterminated (units + 1)

private inductive StringScanResult where
  | closed
      (endByte : Nat)
      (consumedCharacters : Nat)
      (decoded : String)
      (units : Nat)
  | invalidEscape
      (diagnostic : LexicalDiagnostic)
      (units : Nat)
  | unterminated (units : Nat)

private def scanString (file : WorkspaceFile) :
    Nat -> List Char -> List Char -> StringScanResult
  | _, [], _ => .unterminated 0
  | cursor, '"' :: _, decodedRev =>
      .closed (cursor + 1) 1 (String.ofList decodedRev.reverse) 1
  | cursor, '\\' :: [], _ =>
      .invalidEscape
        (.invalidStringEscape
          (sourceSpan file cursor (cursor + 1)) none)
        1
  | cursor, '\\' :: escaped :: rest, decodedRev =>
      let next := cursor + 1 + escaped.utf8Size
      let decoded? :=
        match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none
      match decoded? with
      | none =>
          .invalidEscape
            (.invalidStringEscape
              (sourceSpan file cursor next) (some escaped))
            1
      | some decoded =>
          match scanString file next rest (decoded :: decodedRev) with
          | .closed endByte consumed value units =>
              .closed endByte (consumed + 2) value (units + 1)
          | .invalidEscape diagnostic units =>
              .invalidEscape diagnostic (units + 1)
          | .unterminated units => .unterminated (units + 1)
  | cursor, character :: rest, decodedRev =>
      match scanString file (cursor + character.utf8Size) rest
          (character :: decodedRev) with
      | .closed endByte consumed value units =>
          .closed endByte (consumed + 1) value (units + 1)
      | .invalidEscape diagnostic units =>
          .invalidEscape diagnostic (units + 1)
      | .unterminated units => .unterminated (units + 1)

private inductive AssemblyMode where
  | normal (braceDepth : Nat)
  | lineComment (braceDepth : Nat)
  | blockComment
      (braceDepth : Nat)
      (commentDepth : Nat)
      (outermostOpen : Nat)
  | string (braceDepth : Nat) (openQuote : Nat)

private inductive AssemblyScanResult where
  | closed
      (closeByte : Nat)
      (endByte : Nat)
      (consumedCharacters : Nat)
      (units : Nat)
  | failed
      (diagnostic : LexicalDiagnostic)
      (units : Nat)

private def scanAssembly (file : WorkspaceFile) (openBrace : Nat) :
    AssemblyMode -> Nat -> List Char -> AssemblyScanResult
  | .string _ openQuote, _, [] =>
      .failed
        (.unterminatedAssemblyString
          (sourceSpan file openQuote file.content.utf8ByteSize))
        0
  | .blockComment _ _ outermostOpen, _, [] =>
      .failed
        (.unterminatedAssemblyComment
          (sourceSpan file outermostOpen file.content.utf8ByteSize))
        0
  | .normal _, _, []
  | .lineComment _, _, [] =>
      .failed
        (.unterminatedAssemblyBlock
          (sourceSpan file openBrace file.content.utf8ByteSize))
        0
  | .normal 1, cursor, '}' :: _ =>
      .closed cursor (cursor + 1) 1 1
  | .normal depth, cursor, '{' :: rest =>
      match scanAssembly file openBrace (.normal (depth + 1))
          (cursor + 1) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .normal (depth + 2), cursor, '}' :: rest =>
      match scanAssembly file openBrace (.normal (depth + 1))
          (cursor + 1) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .normal depth, cursor, '/' :: '/' :: rest =>
      match scanAssembly file openBrace (.lineComment depth)
          (cursor + 2) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .normal depth, cursor, '/' :: '*' :: rest =>
      match scanAssembly file openBrace
          (.blockComment depth 1 cursor) (cursor + 2) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .normal depth, cursor, '"' :: rest =>
      match scanAssembly file openBrace (.string depth cursor)
          (cursor + 1) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .normal depth, cursor, character :: rest =>
      match scanAssembly file openBrace (.normal depth)
          (cursor + character.utf8Size) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .lineComment depth, cursor, '\n' :: rest =>
      match scanAssembly file openBrace (.normal depth) (cursor + 1) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .lineComment depth, cursor, character :: rest =>
      match scanAssembly file openBrace (.lineComment depth)
          (cursor + character.utf8Size) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .blockComment braceDepth commentDepth outermostOpen,
      cursor, '/' :: '*' :: rest =>
      match scanAssembly file openBrace
          (.blockComment braceDepth (commentDepth + 1) outermostOpen)
          (cursor + 2) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .blockComment braceDepth 1 _,
      cursor, '*' :: '/' :: rest =>
      match scanAssembly file openBrace (.normal braceDepth)
          (cursor + 2) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .blockComment braceDepth (commentDepth + 2) outermostOpen,
      cursor, '*' :: '/' :: rest =>
      match scanAssembly file openBrace
          (.blockComment braceDepth (commentDepth + 1) outermostOpen)
          (cursor + 2) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .blockComment braceDepth commentDepth outermostOpen,
      cursor, character :: rest =>
      match scanAssembly file openBrace
          (.blockComment braceDepth commentDepth outermostOpen)
          (cursor + character.utf8Size) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .string depth _, cursor, '"' :: rest =>
      match scanAssembly file openBrace (.normal depth) (cursor + 1) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .string depth openQuote, cursor, '\\' :: escaped :: rest =>
      match scanAssembly file openBrace (.string depth openQuote)
          (cursor + 1 + escaped.utf8Size) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 2) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .string depth openQuote, cursor, '\\' :: [] =>
      match scanAssembly file openBrace (.string depth openQuote)
          (cursor + 1) [] with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)
  | .string depth openQuote, cursor, character :: rest =>
      match scanAssembly file openBrace (.string depth openQuote)
          (cursor + character.utf8Size) rest with
      | .closed closeByte endByte consumed units =>
          .closed closeByte endByte (consumed + 1) (units + 1)
      | .failed diagnostic units => .failed diagnostic (units + 1)

private structure CountedResult where
  result : Except LexicalDiagnostic LexedModule
  units : Nat

private def successfulResult (file : WorkspaceFile)
    (tokensRev : List Token) (commentsRev : List Comment) : CountedResult := {
  result := .ok {
    source := file.id
    tokens := tokensRev.reverse
    comments := commentsRev.reverse
  }
  units := 0
}

private def failedResult (diagnostic : LexicalDiagnostic)
    (units : Nat) : CountedResult := {
  result := .error diagnostic
  units
}

private def addUnits (amount : Nat) (result : CountedResult) : CountedResult := {
  result := result.result
  units := amount + result.units
}

private def tokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (kind : TokenKind) : Token := {
  span := sourceSpan file startByte endByte
  payload := kind
}

private def commentAt (file : WorkspaceFile) (startByte endByte : Nat)
    (kind : CommentKind) : Comment := {
  span := sourceSpan file startByte endByte
  payload := kind
}

private def lexLoop (file : WorkspaceFile) :
    (fuel cursor : Nat) -> (characters : List Char) -> Bool ->
      List Token -> List Comment -> characters.length < fuel -> CountedResult
  | 0, _, characters, _, _, _, sufficient =>
      False.elim (Nat.not_lt_zero characters.length sufficient)
  | _ + 1, _, [], _, tokensRev, commentsRev, _ =>
      successfulResult file tokensRev commentsRev
  | fuel + 1, cursor, character :: rest, pendingAssembly,
      tokensRev, commentsRev, sufficient =>
      let characters := character :: rest
      have restSufficient : rest.length < fuel := by
        simp only [List.length_cons] at sufficient
        omega
      if whitespace : isWhitespace character then
        addUnits 1 <| lexLoop file fuel (cursor + character.utf8Size) rest
          pendingAssembly tokensRev commentsRev restSufficient
      else
        match characters with
        | '/' :: '/' :: body =>
            let scanned := scanLineComment (cursor + 2) body
            let comment := commentAt file cursor scanned.endByte .line
            addUnits (scanned.units + 1) <|
              lexLoop file fuel scanned.endByte
                (characters.drop (scanned.consumedCharacters + 2))
                pendingAssembly tokensRev (comment :: commentsRev) (by
                  have progress := drop_length_lt_of_pos characters
                    (scanned.consumedCharacters + 2) (by omega) (by simp)
                  simp only [characters] at progress ⊢
                  omega)
        | '/' :: '*' :: body =>
            match scanBlockComment (cursor + 2) 1 body with
            | .unterminated units =>
                failedResult
                  (.unterminatedBlockComment
                    (sourceSpan file cursor file.content.utf8ByteSize))
                  (units + 1)
            | .closed endByte consumed units =>
                let comment := commentAt file cursor endByte .block
                addUnits (units + 1) <|
                  lexLoop file fuel endByte (characters.drop (consumed + 2))
                    pendingAssembly tokensRev (comment :: commentsRev) (by
                      have progress := drop_length_lt_of_pos characters
                        (consumed + 2) (by omega) (by simp)
                      simp only [characters] at progress ⊢
                      omega)
        | '"' :: body =>
            match scanString file (cursor + 1) body [] with
            | .invalidEscape diagnostic units =>
                failedResult diagnostic (units + 1)
            | .unterminated units =>
                failedResult
                  (.unterminatedString
                    (sourceSpan file cursor file.content.utf8ByteSize))
                  (units + 1)
            | .closed endByte consumed decoded units =>
                let total := consumed + 1
                let spelling := String.ofList (characters.take total)
                let kind := TokenKind.stringLiteral spelling decoded
                let token := tokenAt file cursor endByte kind
                addUnits (units + 1) <|
                  lexLoop file fuel endByte (characters.drop total)
                    false (token :: tokensRev) commentsRev (by
                      have progress := drop_length_lt_of_pos characters total
                        (by simp [total]) (by simp)
                      simp only [characters] at progress ⊢
                      omega)
        | '{' :: body =>
            if pendingAssembly then
              match scanAssembly file cursor (.normal 1) (cursor + 1) body with
              | .failed diagnostic units =>
                  failedResult diagnostic (units + 1)
              | .closed closeByte endByte consumed units =>
                  let outer := sourceSpan file cursor endByte
                  let slice : AssemblySlice := {
                    span := outer
                    payload := {
                      openBrace := sourceSpan file cursor (cursor + 1)
                      contents := sourceSpan file (cursor + 1) closeByte
                      closeBrace := sourceSpan file closeByte endByte
                    }
                  }
                  let token := tokenAt file cursor endByte (.assemblyBlock slice)
                  addUnits (units + 1) <|
                    lexLoop file fuel endByte
                      (characters.drop (consumed + 1)) false
                      (token :: tokensRev) commentsRev (by
                        have progress := drop_length_lt_of_pos characters
                          (consumed + 1) (by omega) (by simp)
                        simp only [characters] at progress ⊢
                        omega)
            else
              let endByte := cursor + 1
              let token := tokenAt file cursor endByte (.symbol .leftBrace)
              addUnits 1 <|
                lexLoop file fuel endByte rest false
                  (token :: tokensRev) commentsRev restSufficient
        | _ =>
            match pragmaMatch? characters with
            | some kind =>
                let count := kind.spelling.toList.length
                let endByte := cursor + kind.spelling.utf8ByteSize
                let token := tokenAt file cursor endByte (.pragmaName kind)
                addUnits count <|
                  lexLoop file fuel endByte (characters.drop count) false
                    (token :: tokensRev) commentsRev (by
                      have countPositive : 0 < count := by
                        cases kind <;> decide
                      have progress := drop_length_lt_of_pos characters count
                        countPositive (by simp)
                      simp only [characters] at progress ⊢
                      omega)
            | none =>
                if letter : isAsciiLetter character then
                  let spellingChars := takeWhile isIdentifierContinue characters
                  let text := String.ofList spellingChars
                  let endByte := cursor + byteSize spellingChars
                  let kind := classifyIdentifier text
                  let token := tokenAt file cursor endByte kind
                  addUnits spellingChars.length <|
                    lexLoop file fuel endByte
                      (characters.drop spellingChars.length) (pendingAfter kind)
                      (token :: tokensRev) commentsRev (by
                        have continuation :
                            isIdentifierContinue character = true := by
                          simp [isIdentifierContinue, letter]
                        have countPositive : 0 < spellingChars.length := by
                          exact takeWhile_length_pos isIdentifierContinue
                            character rest continuation
                        have progress := drop_length_lt_of_pos characters
                          spellingChars.length countPositive (by simp)
                        simp only [characters] at progress ⊢
                        omega)
                else if digitStart : isAsciiDigit character then
                  match characters with
                  | '0' :: 'x' :: digit :: _ =>
                      if isAsciiHexDigit digit then
                        let digitsChars :=
                          takeWhile isAsciiHexDigit (characters.drop 2)
                        let digits := String.ofList digitsChars
                        let spelling := "0x" ++ digits
                        let count := digitsChars.length + 2
                        let endByte := cursor + spelling.utf8ByteSize
                        let kind := TokenKind.hexadecimalLiteral spelling digits
                        let token := tokenAt file cursor endByte kind
                        addUnits count <|
                          lexLoop file fuel endByte (characters.drop count) false
                            (token :: tokensRev) commentsRev (by
                              have progress := drop_length_lt_of_pos characters
                                count (by simp [count]) (by simp)
                              simp only [characters] at progress ⊢
                              omega)
                      else
                        let digitsChars := takeWhile isAsciiDigit characters
                        let digits := String.ofList digitsChars
                        let endByte := cursor + digits.utf8ByteSize
                        let kind := TokenKind.decimalLiteral digits digits
                        let token := tokenAt file cursor endByte kind
                        addUnits digitsChars.length <|
                          lexLoop file fuel endByte
                            (characters.drop digitsChars.length) false
                            (token :: tokensRev) commentsRev (by
                              have countPositive : 0 < digitsChars.length := by
                                exact takeWhile_length_pos isAsciiDigit
                                  character rest digitStart
                              have progress := drop_length_lt_of_pos characters
                                digitsChars.length countPositive (by simp)
                              simp only [characters] at progress ⊢
                              omega)
                  | _ =>
                      let digitsChars := takeWhile isAsciiDigit characters
                      let digits := String.ofList digitsChars
                      let endByte := cursor + digits.utf8ByteSize
                      let kind := TokenKind.decimalLiteral digits digits
                      let token := tokenAt file cursor endByte kind
                      addUnits digitsChars.length <|
                        lexLoop file fuel endByte
                          (characters.drop digitsChars.length) false
                          (token :: tokensRev) commentsRev (by
                            have countPositive : 0 < digitsChars.length := by
                              exact takeWhile_length_pos isAsciiDigit
                                character rest digitStart
                            have progress := drop_length_lt_of_pos characters
                              digitsChars.length countPositive (by simp)
                            simp only [characters] at progress ⊢
                            omega)
                else
                  match rest with
                  | next :: tail =>
                      match multiSymbol? character next with
                      | some symbol =>
                          let endByte := cursor + 2
                          let token := tokenAt file cursor endByte (.symbol symbol)
                          addUnits 1 <|
                            lexLoop file fuel endByte tail false
                              (token :: tokensRev) commentsRev (by
                                exact Nat.lt_trans (by simp) restSufficient)
                      | none =>
                          match singleSymbol? character with
                          | some symbol =>
                              let endByte := cursor + 1
                              let token := tokenAt file cursor endByte (.symbol symbol)
                              addUnits 1 <|
                                lexLoop file fuel endByte (next :: tail) false
                                  (token :: tokensRev) commentsRev restSufficient
                          | none =>
                              failedResult
                                (.invalidCharacter
                                  (sourceSpan file cursor
                                    (cursor + character.utf8Size)) character)
                                1
                  | [] =>
                      match singleSymbol? character with
                      | some symbol =>
                          let endByte := cursor + 1
                          let token := tokenAt file cursor endByte (.symbol symbol)
                          addUnits 1 <|
                            lexLoop file fuel endByte [] false
                              (token :: tokensRev) commentsRev (by omega)
                      | none =>
                          failedResult
                            (.invalidCharacter
                              (sourceSpan file cursor
                                (cursor + character.utf8Size)) character)
                            1

/-- Execute the pure lexer and retain its exact semantic transition count. -/
def execute (file : WorkspaceFile) : LexExecution :=
  let characters := file.content.toList
  let counted := lexLoop file (characters.length + 1) 0 characters false [] []
    (by omega)
  {
    result := counted.result
    actualUnits := counted.units
  }

end Lexer

/-- Execute the pure module-local lexer with exact resource accounting. -/
def lexModuleWithUnits (file : WorkspaceFile) : LexExecution :=
  Lexer.execute file

/-- Execute the pure module-local Multi Surface lexer. -/
def lexModule (file : WorkspaceFile) : Except LexicalDiagnostic LexedModule :=
  (lexModuleWithUnits file).result

/-- The exact semantic transition count used by `lexModule`. -/
def lexActualUnits (file : WorkspaceFile) : Nat :=
  (lexModuleWithUnits file).actualUnits

@[simp] theorem lexModule_equation (file : WorkspaceFile) :
    lexModule file = (lexModuleWithUnits file).result :=
  rfl

@[simp] theorem lexActualUnits_equation (file : WorkspaceFile) :
    lexActualUnits file = (lexModuleWithUnits file).actualUnits :=
  rfl

end Solcore.Surface.Multi
