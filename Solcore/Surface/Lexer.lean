import Solcore.Surface.Token

set_option autoImplicit false

namespace Solcore.Surface

inductive LexErrorKind where
  | invalidCharacter (character : Char)
  | unterminatedBlockComment
  deriving Repr, BEq, DecidableEq

structure LexError where
  code : String
  span : SourceSpan
  kind : LexErrorKind
  deriving Repr, BEq, DecidableEq

inductive LexerInvariant where
  | fuelExhausted (span : SourceSpan)
  | invalidOutput (lexed : Lexed)
  deriving Repr, BEq

inductive LexFailure where
  | source (error : LexError)
  | internal (invariant : LexerInvariant)
  deriving Repr, BEq

namespace Lexer

private def sourceSpan (file : SourceFile) (startByte endByte : Nat) : SourceSpan := {
  source := file.path
  startByte
  endByte
}

private def isWhitespace (character : Char) : Bool :=
  character = ' ' ||
    character = '\t' ||
    character = '\r' ||
    character = '\n' ||
    character.toNat == 12

private def isAsciiLower (character : Char) : Bool :=
  'a' ≤ character && character ≤ 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' ≤ character && character ≤ 'Z'

private def isAsciiDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentifierStart (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isIdentifierContinue (character : Char) : Bool :=
  isIdentifierStart character || isAsciiDigit character || character = '_'

private def charactersByteSize (characters : List Char) : Nat :=
  characters.foldl (fun size character => size + character.utf8Size) 0

private def takeWhile (predicate : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | character :: rest =>
      if predicate character then
        let (taken, remaining) := takeWhile predicate rest
        (character :: taken, remaining)
      else
        ([], character :: rest)

private theorem takeWhile_remainder_length_le
    (predicate : Char → Bool)
    (characters : List Char) :
    (takeWhile predicate characters).2.length ≤ characters.length := by
  induction characters with
  | nil =>
      simp [takeWhile]
  | cons character rest inductionHypothesis =>
      simp only [takeWhile]
      split
      · exact Nat.le_trans inductionHypothesis (Nat.le_succ _)
      · simp

private def classifyIdentifier (text : String) : TokenKind :=
  match text with
  | "function" => .keywordFunction
  | "let" => .keywordLet
  | "if" => .keywordIf
  | "else" => .keywordElse
  | "return" => .keywordReturn
  | _ => .identifier text

private def token
    (file : SourceFile)
    (kind : TokenKind)
    (startByte endByte : Nat) : Token := {
  kind
  span := sourceSpan file startByte endByte
}

private def invalidCharacter
    (file : SourceFile)
    (offset : Nat)
    (character : Char) : LexError := {
  code := "SL0001"
  span := sourceSpan file offset (offset + character.utf8Size)
  kind := .invalidCharacter character
}

private def skipBlockComment
    (file : SourceFile)
    (commentStart : Nat) :
    List Char → Nat → Nat → Except LexError (List Char × Nat)
  | [], _, currentByte =>
      .error {
        code := "SL0002"
        span := sourceSpan file commentStart currentByte
        kind := .unterminatedBlockComment
      }
  | '/' :: '*' :: rest, depth, currentByte =>
      skipBlockComment file commentStart rest (depth + 1) (currentByte + 2)
  | '*' :: '/' :: rest, depth, currentByte =>
      if depth == 1 then
        .ok (rest, currentByte + 2)
      else
        skipBlockComment file commentStart rest (depth - 1) (currentByte + 2)
  | character :: rest, depth, currentByte =>
      skipBlockComment file commentStart rest depth (currentByte + character.utf8Size)

private theorem skipBlockComment_remainder_length_le
    (file : SourceFile)
    (commentStart : Nat)
    (characters remaining : List Char)
    (depth currentByte endByte : Nat)
    (success :
      skipBlockComment file commentStart characters depth currentByte =
        .ok (remaining, endByte)) :
    remaining.length ≤ characters.length := by
  induction characters, depth, currentByte using skipBlockComment.induct
      generalizing remaining endByte with
  | case1 =>
      simp [skipBlockComment] at success
  | case2 rest depth currentByte inductionHypothesis =>
      simp only [skipBlockComment] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by
          simp only [List.length_cons]
          omega)
  | case3 rest depth currentByte depthIsOne =>
      simp [skipBlockComment, depthIsOne] at success
      rw [← success.1]
      simp only [List.length_cons]
      omega
  | case4 rest depth currentByte depthIsNotOne inductionHypothesis =>
      simp [skipBlockComment, depthIsNotOne] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by
          simp only [List.length_cons]
          omega)
  | case5 character rest depth currentByte notOpen notClose
      inductionHypothesis =>
      simp only [skipBlockComment] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by simp)

private def lexAux
    (file : SourceFile) :
    Nat → List Char → Nat → List Token → List Comment → Except LexFailure Lexed
  | _, [], _, tokens, comments =>
      .ok {
        tokens := tokens.reverse
        comments := comments.reverse
      }
  | 0, character :: _, offset, _, _ =>
      .error (.internal (.fuelExhausted
        (sourceSpan file offset (offset + character.utf8Size))))
  | fuel + 1, characters, offset, tokens, comments =>
      match characters with
      | [] =>
          .ok {
            tokens := tokens.reverse
            comments := comments.reverse
          }
      | '/' :: '/' :: rest =>
          let (body, remaining) := takeWhile (· != '\n') rest
          let endByte := offset + 2 + charactersByteSize body
          let comment : Comment := {
            kind := .line
            span := sourceSpan file offset endByte
          }
          lexAux file fuel remaining endByte tokens (comment :: comments)
      | '/' :: '*' :: rest =>
          match skipBlockComment file offset rest 1 (offset + 2) with
          | .error error => .error (.source error)
          | .ok (remaining, endByte) =>
              let comment : Comment := {
                kind := .block
                span := sourceSpan file offset endByte
              }
              lexAux file fuel remaining endByte tokens (comment :: comments)
      | '0' :: 'x' :: first :: rest =>
          if isAsciiHexDigit first then
            let (tail, remaining) := takeWhile isAsciiHexDigit rest
            let digits := first :: tail
            let digitText := String.ofList digits
            let endByte := offset + 2 + charactersByteSize digits
            lexAux file fuel remaining endByte
              (token file (.hexadecimal digitText) offset endByte :: tokens) comments
          else
            let endByte := offset + 1
            lexAux file fuel ('x' :: first :: rest) endByte
              (token file (.decimal "0") offset endByte :: tokens) comments
      | character :: rest =>
          if isWhitespace character then
            lexAux file fuel rest (offset + character.utf8Size) tokens comments
          else if isIdentifierStart character then
            let (tail, remaining) := takeWhile isIdentifierContinue rest
            let characters := character :: tail
            let text := String.ofList characters
            let endByte := offset + charactersByteSize characters
            lexAux file fuel remaining endByte
              (token file (classifyIdentifier text) offset endByte :: tokens) comments
          else if isAsciiDigit character then
            let (tail, remaining) := takeWhile isAsciiDigit rest
            let digits := character :: tail
            let digitText := String.ofList digits
            let endByte := offset + charactersByteSize digits
            lexAux file fuel remaining endByte
              (token file (.decimal digitText) offset endByte :: tokens) comments
          else
            match character, rest with
            | '-', '>' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .arrow offset (offset + 2) :: tokens) comments
            | '=', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .equalEqual offset (offset + 2) :: tokens) comments
            | '!', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .bangEqual offset (offset + 2) :: tokens) comments
            | '<', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .lessEqual offset (offset + 2) :: tokens) comments
            | '>', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .greaterEqual offset (offset + 2) :: tokens) comments
            | '=', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .equal offset (offset + 1) :: tokens) comments
            | '!', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .bang offset (offset + 1) :: tokens) comments
            | '<', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .less offset (offset + 1) :: tokens) comments
            | '>', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .greater offset (offset + 1) :: tokens) comments
            | '+', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .plus offset (offset + 1) :: tokens) comments
            | '-', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .minus offset (offset + 1) :: tokens) comments
            | '*', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .star offset (offset + 1) :: tokens) comments
            | '/', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .slash offset (offset + 1) :: tokens) comments
            | '%', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .percent offset (offset + 1) :: tokens) comments
            | '&', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .ampersand offset (offset + 1) :: tokens) comments
            | '^', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .caret offset (offset + 1) :: tokens) comments
            | '|', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .pipe offset (offset + 1) :: tokens) comments
            | '(', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .leftParen offset (offset + 1) :: tokens) comments
            | ')', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .rightParen offset (offset + 1) :: tokens) comments
            | '{', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .leftBrace offset (offset + 1) :: tokens) comments
            | '}', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .rightBrace offset (offset + 1) :: tokens) comments
            | ':', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .colon offset (offset + 1) :: tokens) comments
            | ';', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .semicolon offset (offset + 1) :: tokens) comments
            | ',', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .comma offset (offset + 1) :: tokens) comments
            | invalid, _ =>
                .error (.source (invalidCharacter file offset invalid))

private def lexUnchecked (file : SourceFile) : Except LexFailure Lexed :=
  let characters := file.content.toList
  lexAux file (characters.length + 1) characters 0 [] []

def lex (file : SourceFile) : Except LexFailure Lexed :=
  match lexUnchecked file with
  | .error failure => .error failure
  | .ok lexed =>
      if lexed.spansValidFor file then
        .ok lexed
      else
        .error (.internal (.invalidOutput lexed))

theorem lex_success_valid
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    lexed.ValidFor file := by
  unfold lex at success
  split at success
  · contradiction
  · rename_i unchecked
    split at success
    · rename_i valid
      cases success
      exact (Lexed.spansValidFor_eq_true_iff lexed file).mp valid
    · contradiction

end Lexer

end Solcore.Surface
