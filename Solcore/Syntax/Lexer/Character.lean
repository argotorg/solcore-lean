import Solcore.Syntax.Lexer.Scan
import Solcore.Syntax.Unicode.Letter
import Solcore.Syntax.Unicode.Number

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Exact whitespace repertoire skipped by the pinned Rust lexer. -/
def isWhitespace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' ||
    character == '\r' || character.toNat == 12

def isAsciiDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' <= character && character <= 'f') ||
    ('A' <= character && character <= 'F')

/-- Core identifiers start with a Unicode 16.0 Letter. -/
def isCoreIdentifierStart (character : Char) : Bool :=
  Unicode.isLetter character

/-- Core identifier continuations are Unicode Letter, Number, or `_`. -/
def isCoreIdentifierContinue (character : Char) : Bool :=
  Unicode.isLetter character || Unicode.isNumber character || character == '_'

/-- Yul adds `$` to the Core continuation repertoire. -/
def isYulIdentifierContinue (character : Char) : Bool :=
  isCoreIdentifierContinue character || character == '$'

/-- Longest prefix selected by a character predicate. -/
structure TextScan where
  consumed : List Char
  remaining : List Char
  deriving Repr, BEq

private def takeWhileRev
    (predicate : Char → Bool) : List Char → List Char → TextScan
  | [], consumedRev => {
      consumed := consumedRev.reverse
      remaining := []
    }
  | characters@(character :: rest), consumedRev =>
      if predicate character then
        takeWhileRev predicate rest (character :: consumedRev)
      else
        {
          consumed := consumedRev.reverse
          remaining := characters
        }

/-- Tail-recursive longest-prefix selection. -/
def takeWhile (predicate : Char → Bool) (characters : List Char) : TextScan :=
  takeWhileRev predicate characters []

private theorem takeWhileRev_partition (predicate : Char → Bool)
    (characters consumedRev : List Char) :
    let scan := takeWhileRev predicate characters consumedRev
    consumedRev.reverse ++ characters = scan.consumed ++ scan.remaining := by
  induction characters generalizing consumedRev with
  | nil => simp [takeWhileRev]
  | cons character rest inductionHypothesis =>
      simp only [takeWhileRev]
      split
      · rw [← inductionHypothesis (character :: consumedRev)]
        simp [List.reverse_cons, List.append_assoc]
      · simp

theorem takeWhile_partition (predicate : Char → Bool)
    (characters : List Char) :
    characters =
      (takeWhile predicate characters).consumed ++
        (takeWhile predicate characters).remaining := by
  simpa [takeWhile] using takeWhileRev_partition predicate characters []

theorem takeWhile_advances (predicate : Char → Bool)
    (startByte : Nat) (characters : List Char) :
    let scan := takeWhile predicate characters
    Advances startByte characters
      (startByte + byteSize scan.consumed) scan.remaining := by
  refine ⟨(takeWhile predicate characters).consumed, ?_, rfl⟩
  exact takeWhile_partition predicate characters

/-- Result of either the Core or Yul identifier regular expression. -/
structure IdentifierScan where
  kind : TokenKind
  remaining : List Char
  deriving Repr, BEq

private def scanHyphenGroups : Nat → List Char → List Char → TextScan
  | 0, consumedRev, remaining => {
      consumed := consumedRev.reverse
      remaining
    }
  | fuel + 1, consumedRev, '-' :: next :: rest =>
      if isCoreIdentifierStart next then
        let plain := takeWhile isCoreIdentifierContinue rest
        let nextRev :=
          ('-' :: next :: plain.consumed).foldl
            (fun prior character => character :: prior) consumedRev
        scanHyphenGroups fuel
          nextRev plain.remaining
      else
        {
          consumed := consumedRev.reverse
          remaining := '-' :: next :: rest
        }
  | _ + 1, consumedRev, remaining => {
      consumed := consumedRev.reverse
      remaining
    }

/-- Scan a name whose first Unicode Letter has already been consumed. -/
def scanLetterIdentifier (first : Char) (remaining : List Char) : IdentifierScan :=
  let plain := takeWhile isCoreIdentifierContinue remaining
  match plain.remaining with
  | '$' :: rest =>
      let tail := takeWhile isYulIdentifierContinue rest
      let text := String.ofList (first :: plain.consumed ++ '$' :: tail.consumed)
      {
        kind := .yulIdentifier text
        remaining := tail.remaining
      }
  | rest =>
      let full :=
        scanHyphenGroups (rest.length + 1)
          (first :: plain.consumed).reverse rest
      let text := String.ofList full.consumed
      let kind :=
        match HardKeyword.ofString? text with
        | some keyword => TokenKind.keyword keyword
        | none => .identifier text
      {
        kind
        remaining := full.remaining
      }

/-- Scan a Yul name after its first `_` or `$` marker. -/
def scanMarkedYulIdentifier
    (first : Char) (remaining : List Char) : IdentifierScan :=
  let tail := takeWhile isYulIdentifierContinue remaining
  {
    kind := .yulIdentifier (String.ofList (first :: tail.consumed))
    remaining := tail.remaining
  }

/-- Recognize every two-character symbol before its one-character prefix. -/
def multiSymbol? (first second : Char) : Option Symbol :=
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
  | '*', '=' => some .starEqual
  | '/', '=' => some .slashEqual
  | '^', '=' => some .caretEqual
  | '&', '=' => some .ampEqual
  | '|', '=' => some .pipeEqual
  | '%', '=' => some .percentEqual
  | '~', '=' => some .tildeEqual
  | _, _ => none

/-- Recognize every one-character punctuation or operator symbol. -/
def singleSymbol? : Char → Option Symbol
  | '+' => some .plus
  | '-' => some .minus
  | '*' => some .star
  | '/' => some .slash
  | '%' => some .percent
  | '!' => some .bang
  | '~' => some .tilde
  | '<' => some .less
  | '>' => some .greater
  | '=' => some .equal
  | '|' => some .pipe
  | '&' => some .amp
  | '^' => some .caret
  | '@' => some .at
  | '?' => some .question
  | '#' => some .hash
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

end Solcore.Syntax.Lexer
