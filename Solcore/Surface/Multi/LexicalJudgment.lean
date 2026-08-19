import Solcore.Surface.Multi.Diagnostic

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace LexicalJudgment

/-- The source byte at one UTF-8 byte offset. -/
def byteAt (file : WorkspaceFile) (offset : Nat) : Option UInt8 :=
  file.content.toByteArray.data[offset]?

/-- The exact source span determined by a file and two byte cursors. -/
def sourceSpan (file : WorkspaceFile) (startByte endByte : Nat) : SourceSpan := {
  source := file.id
  startByte
  endByte
}

/-- A well-ordered UTF-8-boundary range within one source file. -/
def SourceRange (file : WorkspaceFile) (startByte endByte : Nat) : Prop :=
  startByte ≤ endByte ∧
    endByte ≤ file.content.utf8ByteSize ∧
    isUtf8Boundary file.content startByte = true ∧
    isUtf8Boundary file.content endByte = true

/-- Exact source bytes and UTF-8 boundaries for a written text slice. -/
def SourceTextAt (file : WorkspaceFile) (startByte endByte : Nat)
    (text : String) : Prop :=
  SourceRange file startByte endByte ∧
    file.content.toByteArray.extract startByte endByte = text.toByteArray

/-- One exact source byte at a cursor. -/
def ByteAt (file : WorkspaceFile) (cursor : Nat) (byte : UInt8) : Prop :=
  byteAt file cursor = some byte

/-- Two exact consecutive ASCII source bytes. -/
def BytePairAt (file : WorkspaceFile) (cursor : Nat)
    (first second : UInt8) : Prop :=
  ByteAt file cursor first ∧ ByteAt file (cursor + 1) second

/-- One decoded Unicode scalar and its exact UTF-8 cursor movement. -/
def ScalarAt (file : WorkspaceFile) (startByte : Nat)
    (character : Char) (endByte : Nat) : Prop :=
  startByte < endByte ∧
    SourceTextAt file startByte endByte (String.singleton character)

/-- ASCII letters used by identifiers. -/
def AsciiLetter (character : Char) : Prop :=
  ('A' ≤ character ∧ character ≤ 'Z') ∨
    ('a' ≤ character ∧ character ≤ 'z')

/-- ASCII decimal digits. -/
def AsciiDigit (character : Char) : Prop :=
  '0' ≤ character ∧ character ≤ '9'

/-- ASCII hexadecimal digits. -/
def AsciiHexDigit (character : Char) : Prop :=
  AsciiDigit character ∨
    ('a' ≤ character ∧ character ≤ 'f') ∨
    ('A' ≤ character ∧ character ≤ 'F')

/-- The exact discarded whitespace repertoire. -/
def WhitespaceCharacter (character : Char) : Prop :=
  character = ' ' ∨ character = '\t' ∨ character = '\n' ∨
    character = '\r' ∨ character.toNat = 12

/-- Identifier continuation characters, including the first-character class. -/
def IdentifierContinue (character : Char) : Prop :=
  AsciiLetter character ∨ AsciiDigit character ∨ character = '_'

/-- The extra hyphen admitted only by a pragma-name boundary check. -/
def PragmaContinuation (character : Char) : Prop :=
  IdentifierContinue character ∨ character = '-'

/-- A nonempty decimal spelling. -/
def DecimalText (text : String) : Prop :=
  text.toList ≠ [] ∧ ∀ character ∈ text.toList, AsciiDigit character

/-- A nonempty hexadecimal digit suffix. -/
def HexadecimalDigits (text : String) : Prop :=
  text.toList ≠ [] ∧ ∀ character ∈ text.toList, AsciiHexDigit character

/-- One discarded whitespace scalar. -/
def WhitespaceAt (file : WorkspaceFile) (startByte endByte : Nat) : Prop :=
  ∃ character,
    ScalarAt file startByte character endByte ∧
      WhitespaceCharacter character

/-- The complete pragma spelling is followed by its exact lexical boundary. -/
def PragmaBoundaryAt (file : WorkspaceFile) (cursor : Nat) : Prop :=
  ∀ character next,
    ScalarAt file cursor character next → ¬ PragmaContinuation character

/-- One complete pragma-name candidate, including its boundary condition. -/
def PragmaSpellingAt (file : WorkspaceFile) (startByte endByte : Nat)
    (kind : PragmaKind) : Prop :=
  SourceTextAt file startByte endByte kind.spelling ∧
    PragmaBoundaryAt file endByte

/-- Classification of a complete ASCII identifier spelling. -/
inductive IdentifierClassifies : String → TokenKind → Prop where
  | hardKeyword (keyword : HardKeyword) :
      IdentifierClassifies keyword.spelling (.hardKeyword keyword)
  | identifier (text : String)
      (notKeyword : HardKeyword.ofString? text = none) :
      IdentifierClassifies text (.identifier text)

/-- One identifier-language candidate with hard-keyword classification. -/
def IdentifierTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ text kind,
    pathSegmentTextValid text = true ∧
      SourceTextAt file startByte endByte text ∧
      IdentifierClassifies text kind ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := kind
      }

/-- One complete pragma-name token candidate. -/
def PragmaTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ kind,
    PragmaSpellingAt file startByte endByte kind ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .pragmaName kind
      }

/-- One decimal-literal token candidate. -/
def DecimalTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ digits,
    DecimalText digits ∧
      SourceTextAt file startByte endByte digits ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .decimalLiteral digits digits
      }

/-- One hexadecimal-literal token candidate. -/
def HexadecimalTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ digits,
    HexadecimalDigits digits ∧
      SourceTextAt file startByte endByte ("0x" ++ digits) ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .hexadecimalLiteral ("0x" ++ digits) digits
      }

/-- Strict ordinary-string contents through the first closing quote. -/
inductive StringContents (file : WorkspaceFile) : Nat → Nat → String → Prop where
  | close (cursor : Nat)
      (quote : ByteAt file cursor 34) :
      StringContents file cursor (cursor + 1) ""
  | scalar
      (cursor next endByte : Nat)
      (character : Char)
      (decodedTail : String)
      (scalar : ScalarAt file cursor character next)
      (notQuote : character ≠ '"')
      (notBackslash : character ≠ '\\')
      (tail : StringContents file next endByte decodedTail) :
      StringContents file cursor endByte
        (String.singleton character ++ decodedTail)
  | escapedNewline
      (cursor endByte : Nat)
      (decodedTail : String)
      (escape : BytePairAt file cursor 92 110)
      (tail : StringContents file (cursor + 2) endByte decodedTail) :
      StringContents file cursor endByte ("\n" ++ decodedTail)
  | escapedTab
      (cursor endByte : Nat)
      (decodedTail : String)
      (escape : BytePairAt file cursor 92 116)
      (tail : StringContents file (cursor + 2) endByte decodedTail) :
      StringContents file cursor endByte ("\t" ++ decodedTail)
  | escapedQuote
      (cursor endByte : Nat)
      (decodedTail : String)
      (escape : BytePairAt file cursor 92 34)
      (tail : StringContents file (cursor + 2) endByte decodedTail) :
      StringContents file cursor endByte ("\"" ++ decodedTail)
  | escapedBackslash
      (cursor endByte : Nat)
      (decodedTail : String)
      (escape : BytePairAt file cursor 92 92)
      (tail : StringContents file (cursor + 2) endByte decodedTail) :
      StringContents file cursor endByte ("\\" ++ decodedTail)

/-- A prefix containing only ordinary scalars and the four valid escapes. -/
inductive StringScanPrefix (file : WorkspaceFile) : Nat → Nat → Prop where
  | refl (cursor : Nat) : StringScanPrefix file cursor cursor
  | scalar
      (cursor next endByte : Nat)
      (character : Char)
      (scalar : ScalarAt file cursor character next)
      (notQuote : character ≠ '"')
      (notBackslash : character ≠ '\\')
      (tail : StringScanPrefix file next endByte) :
      StringScanPrefix file cursor endByte
  | escapedNewline
      (cursor endByte : Nat)
      (escape : BytePairAt file cursor 92 110)
      (tail : StringScanPrefix file (cursor + 2) endByte) :
      StringScanPrefix file cursor endByte
  | escapedTab
      (cursor endByte : Nat)
      (escape : BytePairAt file cursor 92 116)
      (tail : StringScanPrefix file (cursor + 2) endByte) :
      StringScanPrefix file cursor endByte
  | escapedQuote
      (cursor endByte : Nat)
      (escape : BytePairAt file cursor 92 34)
      (tail : StringScanPrefix file (cursor + 2) endByte) :
      StringScanPrefix file cursor endByte
  | escapedBackslash
      (cursor endByte : Nat)
      (escape : BytePairAt file cursor 92 92)
      (tail : StringScanPrefix file (cursor + 2) endByte) :
      StringScanPrefix file cursor endByte

/-- The first unsupported or incomplete escape at one string cursor. -/
inductive InvalidStringEscapeAt (file : WorkspaceFile) :
    Nat → Nat → Option Char → Prop where
  | unsupported
      (cursor endByte : Nat)
      (character : Char)
      (backslash : ByteAt file cursor 92)
      (escaped : ScalarAt file (cursor + 1) character endByte)
      (unsupported :
        character ≠ 'n' ∧ character ≠ 't' ∧
          character ≠ '"' ∧ character ≠ '\\') :
      InvalidStringEscapeAt file cursor endByte (some character)
  | endOfFile
      (cursor : Nat)
      (backslash : ByteAt file cursor 92)
      (atEnd : cursor + 1 = file.content.utf8ByteSize) :
      InvalidStringEscapeAt file cursor (cursor + 1) none

/-- One successfully decoded ordinary-string token candidate. -/
def StringTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ spelling decoded,
    ByteAt file startByte 34 ∧
      StringContents file (startByte + 1) endByte decoded ∧
      SourceTextAt file startByte endByte spelling ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .stringLiteral spelling decoded
      }

/-- One transition while an ordinary nested block comment remains open. -/
inductive BlockCommentRun (file : WorkspaceFile) :
    Nat → Nat → Nat → Nat → Prop where
  | refl (depth cursor : Nat) :
      BlockCommentRun file depth cursor depth cursor
  | nestedOpen
      (depth cursor finalDepth endByte : Nat)
      (positive : 0 < depth)
      (opener : BytePairAt file cursor 47 42)
      (tail :
        BlockCommentRun file (depth + 1) (cursor + 2)
          finalDepth endByte) :
      BlockCommentRun file depth cursor finalDepth endByte
  | nestedClose
      (depth cursor finalDepth endByte : Nat)
      (nested : 1 < depth)
      (closer : BytePairAt file cursor 42 47)
      (tail :
        BlockCommentRun file (depth - 1) (cursor + 2)
          finalDepth endByte) :
      BlockCommentRun file depth cursor finalDepth endByte
  | scalar
      (depth cursor next finalDepth endByte : Nat)
      (character : Char)
      (positive : 0 < depth)
      (notOpener : ¬ BytePairAt file cursor 47 42)
      (notCloser : ¬ BytePairAt file cursor 42 47)
      (scalar : ScalarAt file cursor character next)
      (tail : BlockCommentRun file depth next finalDepth endByte) :
      BlockCommentRun file depth cursor finalDepth endByte

/-- One complete, arbitrarily nested outer block comment. -/
def BlockCommentSpanAt (file : WorkspaceFile) (startByte endByte : Nat) : Prop :=
  BytePairAt file startByte 47 42 ∧
    ∃ closeCursor,
      BlockCommentRun file 1 (startByte + 2) 1 closeCursor ∧
        BytePairAt file closeCursor 42 47 ∧
        endByte = closeCursor + 2 ∧
        SourceRange file startByte endByte

/-- An outer block comment whose positive nesting depth reaches end of file. -/
def UnterminatedBlockCommentAt (file : WorkspaceFile)
    (startByte : Nat) : Prop :=
  BytePairAt file startByte 47 42 ∧
    ∃ depth,
      0 < depth ∧
        BlockCommentRun file 1 (startByte + 2) depth
          file.content.utf8ByteSize

/-- A line comment ending immediately before the first LF or at end of file. -/
def LineCommentSpanAt (file : WorkspaceFile) (startByte endByte : Nat) : Prop :=
  BytePairAt file startByte 47 47 ∧
    SourceRange file startByte endByte ∧
    startByte + 2 ≤ endByte ∧
    (∀ cursor, startByte + 2 ≤ cursor → cursor < endByte →
      ¬ ByteAt file cursor 10) ∧
    (endByte = file.content.utf8ByteSize ∨ ByteAt file endByte 10)

/-- One retained line-comment candidate. -/
def LineCommentAt (file : WorkspaceFile) (startByte endByte : Nat)
    (comment : Comment) : Prop :=
  LineCommentSpanAt file startByte endByte ∧
    comment = {
      span := sourceSpan file startByte endByte
      payload := .line
    }

/-- One retained nested-block-comment candidate. -/
def BlockCommentAt (file : WorkspaceFile) (startByte endByte : Nat)
    (comment : Comment) : Prop :=
  BlockCommentSpanAt file startByte endByte ∧
    comment = {
      span := sourceSpan file startByte endByte
      payload := .block
    }

/-- The complete state required by the opaque assembly-block scanner. -/
inductive AssemblyScannerState where
  | normal (braceDepth : Nat)
  | lineComment (braceDepth : Nat)
  | blockComment
      (braceDepth : Nat)
      (commentDepth : Nat)
      (outermostOpen : Nat)
  | string (braceDepth : Nat) (openQuote : Nat)
  deriving Repr, BEq, DecidableEq

/-- One exact assembly scanner state transition. -/
inductive AssemblyStep (file : WorkspaceFile) :
    AssemblyScannerState → Nat → AssemblyScannerState → Nat → Prop where
  | openBrace
      (depth cursor : Nat)
      (positive : 0 < depth)
      (brace : ByteAt file cursor 123) :
      AssemblyStep file (.normal depth) cursor
        (.normal (depth + 1)) (cursor + 1)
  | nestedCloseBrace
      (depth cursor : Nat)
      (nested : 1 < depth)
      (brace : ByteAt file cursor 125) :
      AssemblyStep file (.normal depth) cursor
        (.normal (depth - 1)) (cursor + 1)
  | openLineComment
      (depth cursor : Nat)
      (positive : 0 < depth)
      (opener : BytePairAt file cursor 47 47) :
      AssemblyStep file (.normal depth) cursor
        (.lineComment depth) (cursor + 2)
  | openBlockComment
      (depth cursor : Nat)
      (positive : 0 < depth)
      (opener : BytePairAt file cursor 47 42) :
      AssemblyStep file (.normal depth) cursor
        (.blockComment depth 1 cursor) (cursor + 2)
  | openString
      (depth cursor : Nat)
      (positive : 0 < depth)
      (quote : ByteAt file cursor 34) :
      AssemblyStep file (.normal depth) cursor
        (.string depth cursor) (cursor + 1)
  | normalScalar
      (depth cursor next : Nat)
      (character : Char)
      (positive : 0 < depth)
      (notOpenBrace : ¬ ByteAt file cursor 123)
      (notCloseBrace : ¬ ByteAt file cursor 125)
      (notQuote : ¬ ByteAt file cursor 34)
      (notLineComment : ¬ BytePairAt file cursor 47 47)
      (notBlockComment : ¬ BytePairAt file cursor 47 42)
      (scalar : ScalarAt file cursor character next) :
      AssemblyStep file (.normal depth) cursor (.normal depth) next
  | lineFeed
      (depth cursor : Nat)
      (positive : 0 < depth)
      (feed : ByteAt file cursor 10) :
      AssemblyStep file (.lineComment depth) cursor
        (.normal depth) (cursor + 1)
  | lineScalar
      (depth cursor next : Nat)
      (character : Char)
      (positive : 0 < depth)
      (notFeed : character ≠ '\n')
      (scalar : ScalarAt file cursor character next) :
      AssemblyStep file (.lineComment depth) cursor
        (.lineComment depth) next
  | nestedBlockOpen
      (braceDepth commentDepth outermostOpen cursor : Nat)
      (bracePositive : 0 < braceDepth)
      (commentPositive : 0 < commentDepth)
      (opener : BytePairAt file cursor 47 42) :
      AssemblyStep file
        (.blockComment braceDepth commentDepth outermostOpen) cursor
        (.blockComment braceDepth (commentDepth + 1) outermostOpen)
        (cursor + 2)
  | nestedBlockClose
      (braceDepth commentDepth outermostOpen cursor : Nat)
      (bracePositive : 0 < braceDepth)
      (nested : 1 < commentDepth)
      (closer : BytePairAt file cursor 42 47) :
      AssemblyStep file
        (.blockComment braceDepth commentDepth outermostOpen) cursor
        (.blockComment braceDepth (commentDepth - 1) outermostOpen)
        (cursor + 2)
  | outerBlockClose
      (braceDepth outermostOpen cursor : Nat)
      (bracePositive : 0 < braceDepth)
      (closer : BytePairAt file cursor 42 47) :
      AssemblyStep file
        (.blockComment braceDepth 1 outermostOpen) cursor
        (.normal braceDepth) (cursor + 2)
  | blockScalar
      (braceDepth commentDepth outermostOpen cursor next : Nat)
      (character : Char)
      (bracePositive : 0 < braceDepth)
      (commentPositive : 0 < commentDepth)
      (notOpener : ¬ BytePairAt file cursor 47 42)
      (notCloser : ¬ BytePairAt file cursor 42 47)
      (scalar : ScalarAt file cursor character next) :
      AssemblyStep file
        (.blockComment braceDepth commentDepth outermostOpen) cursor
        (.blockComment braceDepth commentDepth outermostOpen) next
  | closeString
      (depth openQuote cursor : Nat)
      (positive : 0 < depth)
      (quote : ByteAt file cursor 34) :
      AssemblyStep file (.string depth openQuote) cursor
        (.normal depth) (cursor + 1)
  | escapedStringScalar
      (depth openQuote cursor next : Nat)
      (character : Char)
      (positive : 0 < depth)
      (backslash : ByteAt file cursor 92)
      (escaped : ScalarAt file (cursor + 1) character next) :
      AssemblyStep file (.string depth openQuote) cursor
        (.string depth openQuote) next
  | trailingStringBackslash
      (depth openQuote cursor : Nat)
      (positive : 0 < depth)
      (backslash : ByteAt file cursor 92)
      (atEnd : cursor + 1 = file.content.utf8ByteSize) :
      AssemblyStep file (.string depth openQuote) cursor
        (.string depth openQuote) (cursor + 1)
  | stringScalar
      (depth openQuote cursor next : Nat)
      (character : Char)
      (positive : 0 < depth)
      (notQuote : character ≠ '"')
      (notBackslash : character ≠ '\\')
      (scalar : ScalarAt file cursor character next) :
      AssemblyStep file (.string depth openQuote) cursor
        (.string depth openQuote) next

/-- A finite composition of exact assembly scanner transitions. -/
inductive AssemblyRun (file : WorkspaceFile) :
    AssemblyScannerState → Nat → AssemblyScannerState → Nat → Prop where
  | refl (state : AssemblyScannerState) (cursor : Nat) :
      AssemblyRun file state cursor state cursor
  | step
      (state nextState finalState : AssemblyScannerState)
      (cursor next endByte : Nat)
      (transition : AssemblyStep file state cursor nextState next)
      (tail : AssemblyRun file nextState next finalState endByte) :
      AssemblyRun file state cursor finalState endByte

/-- One balanced opaque assembly slice with exact delimiter and interior spans. -/
def AssemblySliceAt (file : WorkspaceFile) (startByte endByte : Nat)
    (slice : AssemblySlice) : Prop :=
  ByteAt file startByte 123 ∧
    ∃ closeCursor,
      AssemblyRun file (.normal 1) (startByte + 1)
          (.normal 1) closeCursor ∧
        ByteAt file closeCursor 125 ∧
        endByte = closeCursor + 1 ∧
        SourceRange file startByte endByte ∧
        slice = {
          span := sourceSpan file startByte endByte
          payload := {
            openBrace := sourceSpan file startByte (startByte + 1)
            contents := sourceSpan file (startByte + 1) closeCursor
            closeBrace := sourceSpan file closeCursor endByte
          }
        }

/-- One opaque assembly-block token with the same span as its slice. -/
def AssemblyTokenAt (file : WorkspaceFile) (startByte endByte : Nat)
    (token : Token) : Prop :=
  ∃ slice,
    AssemblySliceAt file startByte endByte slice ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .assemblyBlock slice
      }

/-- An assembly scan reaching end of file inside an open string. -/
def UnterminatedAssemblyStringAt (file : WorkspaceFile)
    (openBrace openQuote : Nat) : Prop :=
  ByteAt file openBrace 123 ∧
    ∃ depth,
      0 < depth ∧
        AssemblyRun file (.normal 1) (openBrace + 1)
          (.string depth openQuote) file.content.utf8ByteSize

/-- An assembly scan reaching end of file inside an open nested comment. -/
def UnterminatedAssemblyCommentAt (file : WorkspaceFile)
    (openBrace outermostOpen : Nat) : Prop :=
  ByteAt file openBrace 123 ∧
    ∃ braceDepth commentDepth,
      0 < braceDepth ∧ 0 < commentDepth ∧
        AssemblyRun file (.normal 1) (openBrace + 1)
          (.blockComment braceDepth commentDepth outermostOpen)
          file.content.utf8ByteSize

/-- An assembly scan reaching end of file with only braces or a line comment open. -/
inductive UnterminatedAssemblyBlockAt (file : WorkspaceFile) : Nat → Prop where
  | normal
      (openBrace depth : Nat)
      (brace : ByteAt file openBrace 123)
      (positive : 0 < depth)
      (run : AssemblyRun file (.normal 1) (openBrace + 1)
        (.normal depth) file.content.utf8ByteSize) :
      UnterminatedAssemblyBlockAt file openBrace
  | lineComment
      (openBrace depth : Nat)
      (brace : ByteAt file openBrace 123)
      (positive : 0 < depth)
      (run : AssemblyRun file (.normal 1) (openBrace + 1)
        (.lineComment depth) file.content.utf8ByteSize) :
      UnterminatedAssemblyBlockAt file openBrace

/-- The fixed equal-length lexical candidate priority classes. -/
inductive CandidateClass where
  | comment
  | string
  | pragmaName
  | identifier
  | numericLiteral
  | multiCharacterSymbol
  | singleCharacterSymbol
  deriving Repr, BEq, DecidableEq

namespace CandidateClass

/-- Lower ranks have priority when candidate byte lengths are equal. -/
def rank : CandidateClass → Nat
  | .comment => 0
  | .string => 1
  | .pragmaName => 2
  | .identifier => 3
  | .numericLiteral => 4
  | .multiCharacterSymbol => 5
  | .singleCharacterSymbol => 6

end CandidateClass

/-- The priority class of one exact symbol spelling. -/
def symbolCandidateClass : Symbol → CandidateClass
  | .colonEqual | .arrow | .fatArrow
  | .equalEqual | .notEqual | .greaterEqual | .lessEqual
  | .logicalAnd | .logicalOr
  | .plusEqual | .minusEqual | .caretEqual | .ampEqual | .pipeEqual
  | .percentEqual => .multiCharacterSymbol
  | .plus | .minus | .star | .slash | .percent | .bang
  | .less | .greater | .equal | .pipe | .amp | .caret
  | .at | .question | .dot | .colon | .semicolon | .comma
  | .leftParen | .rightParen | .leftBrace | .rightBrace
  | .leftBracket | .rightBracket | .underscore => .singleCharacterSymbol

/-- One symbol token candidate, with comment and assembly priority guards. -/
def SymbolTokenAt (file : WorkspaceFile) (pendingAssembly : Bool)
    (startByte endByte : Nat) (token : Token) : Prop :=
  ∃ symbol,
    SourceTextAt file startByte endByte symbol.spelling ∧
      (symbol = .slash →
        ¬ BytePairAt file startByte 47 47 ∧
          ¬ BytePairAt file startByte 47 42) ∧
      (pendingAssembly = true → symbol ≠ .leftBrace) ∧
      token = {
        span := sourceSpan file startByte endByte
        payload := .symbol symbol
      }

/-- One token or retained-comment candidate at a byte cursor. -/
inductive Candidate where
  | comment (comment : Comment)
  | token (candidateClass : CandidateClass) (token : Token)
  deriving Repr, BEq, DecidableEq

namespace Candidate

/-- The exact span carried by a candidate. -/
def span : Candidate → SourceSpan
  | .comment value => value.span
  | .token _ value => value.span

/-- The candidate's fixed equal-length priority class. -/
def candidateClass : Candidate → CandidateClass
  | .comment _ => .comment
  | .token candidateClass _ => candidateClass

end Candidate

/-- Every successful lexical-language candidate at one cursor. -/
inductive CandidateAt (file : WorkspaceFile) (pendingAssembly : Bool)
    (startByte : Nat) : Candidate → Prop where
  | lineComment
      (endByte : Nat)
      (comment : Comment)
      (recognized : LineCommentAt file startByte endByte comment) :
      CandidateAt file pendingAssembly startByte (.comment comment)
  | blockComment
      (endByte : Nat)
      (comment : Comment)
      (recognized : BlockCommentAt file startByte endByte comment) :
      CandidateAt file pendingAssembly startByte (.comment comment)
  | string
      (endByte : Nat)
      (token : Token)
      (recognized : StringTokenAt file startByte endByte token) :
      CandidateAt file pendingAssembly startByte (.token .string token)
  | pragmaName
      (endByte : Nat)
      (token : Token)
      (recognized : PragmaTokenAt file startByte endByte token) :
      CandidateAt file pendingAssembly startByte (.token .pragmaName token)
  | identifier
      (endByte : Nat)
      (token : Token)
      (recognized : IdentifierTokenAt file startByte endByte token) :
      CandidateAt file pendingAssembly startByte (.token .identifier token)
  | decimal
      (endByte : Nat)
      (token : Token)
      (recognized : DecimalTokenAt file startByte endByte token) :
      CandidateAt file pendingAssembly startByte
        (.token .numericLiteral token)
  | hexadecimal
      (endByte : Nat)
      (token : Token)
      (recognized : HexadecimalTokenAt file startByte endByte token) :
      CandidateAt file pendingAssembly startByte
        (.token .numericLiteral token)
  | symbol
      (endByte : Nat)
      (symbol : Symbol)
      (token : Token)
      (recognized : SymbolTokenAt file pendingAssembly startByte endByte token)
      (kind : token.payload = .symbol symbol) :
      CandidateAt file pendingAssembly startByte
        (.token (symbolCandidateClass symbol) token)

/-- Strictly better maximal-munch choice, including the fixed tie order. -/
def CandidateOutranks (preferred other : Candidate) : Prop :=
  other.span.endByte < preferred.span.endByte ∨
    (other.span.endByte = preferred.span.endByte ∧
      preferred.candidateClass.rank < other.candidateClass.rank)

/-- A candidate wins against every candidate from the same source cursor. -/
def CandidateWinsAt (file : WorkspaceFile) (pendingAssembly : Bool)
    (startByte : Nat) (candidate : Candidate) : Prop :=
  CandidateAt file pendingAssembly startByte candidate ∧
    ∀ other,
      CandidateAt file pendingAssembly startByte other →
        other = candidate ∨ CandidateOutranks candidate other

/-- The exact post-token state for contextual assembly-block recognition. -/
def PendingAfterToken (token : Token) (pendingAssembly : Bool) : Prop :=
  (token.payload = .hardKeyword .assemblyKw ∧ pendingAssembly = true) ∨
    (token.payload ≠ .hardKeyword .assemblyKw ∧ pendingAssembly = false)

/-- Characters that can begin at least one normal lexical language. -/
def LexemeStartCharacter (character : Char) : Prop :=
  WhitespaceCharacter character ∨
    AsciiLetter character ∨
    AsciiDigit character ∨
    character = '"' ∨
    ∃ (symbol : Symbol) (tail : List Char),
      symbol.spelling.toList = character :: tail

/--
A successful source prefix partitioned into discarded whitespace, winning
maximal-munch candidates, and contextual opaque assembly blocks.
-/
inductive LexesPrefix (file : WorkspaceFile) :
    Nat → Bool → List Token → List Comment → Prop where
  | start : LexesPrefix file 0 false [] []
  | whitespace
      (cursor next : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (whitespace : WhitespaceAt file cursor next) :
      LexesPrefix file next pendingAssembly tokens comments
  | comment
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (comment : Comment)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (winner :
        CandidateWinsAt file pendingAssembly cursor (.comment comment)) :
      LexesPrefix file comment.span.endByte pendingAssembly
        tokens (comments ++ [comment])
  | token
      (cursor : Nat)
      (pendingAssembly nextPending : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (candidateClass : CandidateClass)
      (token : Token)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (winner :
        CandidateWinsAt file pendingAssembly cursor
          (.token candidateClass token))
      (nextState : PendingAfterToken token nextPending) :
      LexesPrefix file token.span.endByte nextPending
        (tokens ++ [token]) comments
  | assemblyBlock
      (cursor endByte : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (token : Token)
      (prior : LexesPrefix file cursor true tokens comments)
      (recognized : AssemblyTokenAt file cursor endByte token) :
      LexesPrefix file endByte false (tokens ++ [token]) comments

end LexicalJudgment

/--
The successful independent byte-partition judgment for one workspace file.
The pending assembly state may remain set at logical end of file.
-/
inductive Lexes : WorkspaceFile → List Token → List Comment → Prop where
  | complete
      (file : WorkspaceFile)
      (tokens : List Token)
      (comments : List Comment)
      (pendingAssembly : Bool)
      (partition :
        LexicalJudgment.LexesPrefix file file.content.utf8ByteSize
          pendingAssembly tokens comments) :
      Lexes file tokens comments

namespace LexicalDiagnostic

open LexicalJudgment

/--
Independent applicability of each lexical failure after one shared successful
prefix. Each local scanner premise reaches the first point where its rule can
no longer continue.
-/
inductive Applies (file : WorkspaceFile) : LexicalDiagnostic → Prop where
  | invalidCharacter
      (cursor next : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (character : Char)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (scalar : ScalarAt file cursor character next)
      (invalid : ¬ LexemeStartCharacter character) :
      Applies file
        (.invalidCharacter (sourceSpan file cursor next) character)
  | unterminatedBlockComment
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (openToEnd : UnterminatedBlockCommentAt file cursor)
      (range : SourceRange file cursor file.content.utf8ByteSize) :
      Applies file
        (.unterminatedBlockComment
          (sourceSpan file cursor file.content.utf8ByteSize))
  | unterminatedString
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file cursor pendingAssembly tokens comments)
      (quote : ByteAt file cursor 34)
      (validToEnd :
        StringScanPrefix file (cursor + 1) file.content.utf8ByteSize)
      (range : SourceRange file cursor file.content.utf8ByteSize) :
      Applies file
        (.unterminatedString
          (sourceSpan file cursor file.content.utf8ByteSize))
  | invalidStringEscape
      (stringStart escapeStart escapeEnd : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (character : Option Char)
      (prior :
        LexesPrefix file stringStart pendingAssembly tokens comments)
      (quote : ByteAt file stringStart 34)
      (validPrefix :
        StringScanPrefix file (stringStart + 1) escapeStart)
      (invalidEscape :
        InvalidStringEscapeAt file escapeStart escapeEnd character)
      (range : SourceRange file escapeStart escapeEnd) :
      Applies file
        (.invalidStringEscape
          (sourceSpan file escapeStart escapeEnd) character)
  | unterminatedAssemblyString
      (openBrace openQuote : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file openBrace true tokens comments)
      (openToEnd : UnterminatedAssemblyStringAt file openBrace openQuote)
      (range : SourceRange file openQuote file.content.utf8ByteSize) :
      Applies file
        (.unterminatedAssemblyString
          (sourceSpan file openQuote file.content.utf8ByteSize))
  | unterminatedAssemblyComment
      (openBrace outermostOpen : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file openBrace true tokens comments)
      (openToEnd :
        UnterminatedAssemblyCommentAt file openBrace outermostOpen)
      (range : SourceRange file outermostOpen file.content.utf8ByteSize) :
      Applies file
        (.unterminatedAssemblyComment
          (sourceSpan file outermostOpen file.content.utf8ByteSize))
  | unterminatedAssemblyBlock
      (openBrace : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (prior : LexesPrefix file openBrace true tokens comments)
      (openToEnd : UnterminatedAssemblyBlockAt file openBrace)
      (range : SourceRange file openBrace file.content.utf8ByteSize) :
      Applies file
        (.unterminatedAssemblyBlock
          (sourceSpan file openBrace file.content.utf8ByteSize))

end LexicalDiagnostic

end Solcore.Surface.Multi
