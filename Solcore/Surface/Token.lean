import Solcore.Surface.Source

set_option autoImplicit false

namespace Solcore.Surface

inductive TokenKind where
  | keywordFunction
  | keywordLet
  | keywordIf
  | keywordElse
  | keywordReturn
  | identifier (text : String)
  | decimal (digits : String)
  | hexadecimal (digits : String)
  | arrow
  | equal
  | equalEqual
  | bang
  | bangEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  | plus
  | minus
  | star
  | slash
  | percent
  | ampersand
  | caret
  | pipe
  | leftParen
  | rightParen
  | leftBrace
  | rightBrace
  | colon
  | semicolon
  | comma
  deriving Repr, BEq, DecidableEq

namespace TokenKind

private def isAsciiLower (character : Char) : Bool :=
  'a' ≤ character && character ≤ 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' ≤ character && character ≤ 'Z'

private def isAsciiDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isAsciiLetter (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentifierText (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest =>
      isAsciiLetter first &&
        rest.all fun character =>
          isAsciiLetter character || isAsciiDigit character || character = '_'

private def isHardKeyword (value : String) : Bool :=
  value == "function" ||
    value == "let" ||
    value == "if" ||
    value == "else" ||
    value == "return"

def text : TokenKind → String
  | .keywordFunction => "function"
  | .keywordLet => "let"
  | .keywordIf => "if"
  | .keywordElse => "else"
  | .keywordReturn => "return"
  | .identifier value => value
  | .decimal digits => digits
  | .hexadecimal digits => "0x" ++ digits
  | .arrow => "->"
  | .equal => "="
  | .equalEqual => "=="
  | .bang => "!"
  | .bangEqual => "!="
  | .less => "<"
  | .lessEqual => "<="
  | .greater => ">"
  | .greaterEqual => ">="
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .percent => "%"
  | .ampersand => "&"
  | .caret => "^"
  | .pipe => "|"
  | .leftParen => "("
  | .rightParen => ")"
  | .leftBrace => "{"
  | .rightBrace => "}"
  | .colon => ":"
  | .semicolon => ";"
  | .comma => ","

def isIdentifier : TokenKind → Bool
  | .identifier _ => true
  | _ => false

def isCanonical : TokenKind → Bool
  | .identifier value => isIdentifierText value && !isHardKeyword value
  | .decimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiDigit
  | .hexadecimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiHexDigit
  | _ => true

def Canonical (kind : TokenKind) : Prop :=
  kind.isCanonical = true

theorem isCanonical_eq_true_iff (kind : TokenKind) :
    kind.isCanonical = true ↔ kind.Canonical := by
  rfl

end TokenKind

structure Token where
  kind : TokenKind
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

namespace Token

def text (token : Token) : String :=
  token.kind.text

def ValidFor (token : Token) (file : SourceFile) : Prop :=
  token.kind.Canonical ∧
    token.span.ValidFor file ∧
    file.content.toByteArray.extract token.span.startByte token.span.endByte =
      token.text.toByteArray

def isValidFor (token : Token) (file : SourceFile) : Bool :=
  token.kind.isCanonical &&
    token.span.isValidFor file &&
    decide
      (file.content.toByteArray.extract token.span.startByte token.span.endByte =
        token.text.toByteArray)

theorem isValidFor_eq_true_iff (token : Token) (file : SourceFile) :
    token.isValidFor file = true ↔ token.ValidFor file := by
  simp [isValidFor, ValidFor, TokenKind.isCanonical_eq_true_iff,
    SourceSpan.isValidFor_eq_true_iff, and_assoc]

end Token

inductive CommentKind where
  | line
  | block
  deriving Repr, BEq, DecidableEq

structure Comment where
  kind : CommentKind
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

namespace Comment

private def linePayloadValid : List UInt8 → Bool
  | 47 :: 47 :: body => !(body.contains 10)
  | _ => false

private def blockBodyValid : List UInt8 → Nat → Bool
  | [], _ => false
  | 47 :: 42 :: rest, depth =>
      blockBodyValid rest (depth + 1)
  | 42 :: 47 :: rest, depth =>
      if depth == 1 then
        rest.isEmpty
      else
        blockBodyValid rest (depth - 1)
  | _ :: rest, depth =>
      blockBodyValid rest depth

private def blockPayloadValid : List UInt8 → Bool
  | 47 :: 42 :: rest => blockBodyValid rest 1
  | _ => false

def payloadValid (comment : Comment) (file : SourceFile) : Bool :=
  let sourceBytes := file.content.toByteArray
  let payload :=
    (sourceBytes.extract comment.span.startByte comment.span.endByte).data.toList
  match comment.kind with
  | .line =>
      linePayloadValid payload &&
        (comment.span.endByte == sourceBytes.size ||
          sourceBytes.data[comment.span.endByte]? == some 10)
  | .block =>
      blockPayloadValid payload

def ValidFor (comment : Comment) (file : SourceFile) : Prop :=
  comment.span.ValidFor file ∧ comment.payloadValid file = true

def isValidFor (comment : Comment) (file : SourceFile) : Bool :=
  comment.span.isValidFor file && comment.payloadValid file

theorem isValidFor_eq_true_iff (comment : Comment) (file : SourceFile) :
    comment.isValidFor file = true ↔ comment.ValidFor file := by
  simp [isValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff]

end Comment

structure Lexed where
  tokens : List Token
  comments : List Comment
  deriving Repr, BEq, DecidableEq

namespace Lexed

private def spansOrdered : List SourceSpan → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      first.endByte ≤ second.startByte &&
        spansOrdered (second :: rest)

private def spansDisjoint (first second : SourceSpan) : Bool :=
  first.endByte ≤ second.startByte ||
    second.endByte ≤ first.startByte

private def crossDisjoint (lexed : Lexed) : Bool :=
  lexed.tokens.all fun token =>
    lexed.comments.all fun comment =>
      spansDisjoint token.span comment.span

private def isAsciiWhitespaceByte (byte : UInt8) : Bool :=
  byte == 9 || byte == 10 || byte == 12 || byte == 13 || byte == 32

private def coversByte (span : SourceSpan) (index : Nat) : Bool :=
  span.startByte ≤ index && index < span.endByte

private def sourcePartitioned (lexed : Lexed) (file : SourceFile) : Bool :=
  let spans :=
    lexed.tokens.map (·.span) ++ lexed.comments.map (·.span)
  let bytes := file.content.toByteArray
  (List.range bytes.size).all fun index =>
    spans.any (fun span => coversByte span index) ||
      match bytes.data[index]? with
      | some byte => isAsciiWhitespaceByte byte
      | none => false

def ValidFor (lexed : Lexed) (file : SourceFile) : Prop :=
  (∀ token ∈ lexed.tokens, token.ValidFor file) ∧
    (∀ comment ∈ lexed.comments, comment.ValidFor file) ∧
    spansOrdered (lexed.tokens.map (·.span)) = true ∧
    spansOrdered (lexed.comments.map (·.span)) = true ∧
    crossDisjoint lexed = true ∧
    sourcePartitioned lexed file = true

def isValidFor (lexed : Lexed) (file : SourceFile) : Bool :=
  lexed.tokens.all (·.isValidFor file) &&
    lexed.comments.all (·.isValidFor file) &&
    spansOrdered (lexed.tokens.map (·.span)) &&
    spansOrdered (lexed.comments.map (·.span)) &&
    crossDisjoint lexed &&
    sourcePartitioned lexed file

def spansValidFor (lexed : Lexed) (file : SourceFile) : Bool :=
  lexed.isValidFor file

theorem isValidFor_eq_true_iff (lexed : Lexed) (file : SourceFile) :
    lexed.isValidFor file = true ↔ lexed.ValidFor file := by
  simp [isValidFor, ValidFor, Token.isValidFor_eq_true_iff,
    Comment.isValidFor_eq_true_iff, and_assoc]

theorem spansValidFor_eq_true_iff (lexed : Lexed) (file : SourceFile) :
    lexed.spansValidFor file = true ↔ lexed.ValidFor file := by
  exact isValidFor_eq_true_iff lexed file

end Lexed

end Solcore.Surface
