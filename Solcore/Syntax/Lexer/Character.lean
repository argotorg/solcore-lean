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

private theorem reverse_foldl_prepend (characters consumedRev : List Char) :
    (characters.foldl (fun prior character => character :: prior)
      consumedRev).reverse = consumedRev.reverse ++ characters := by
  induction characters generalizing consumedRev with
  | nil => simp
  | cons character rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      simp [List.reverse_cons, List.append_assoc]

private theorem scanHyphenGroups_partition
    (fuel : Nat) (consumedRev remaining : List Char) :
    let scan := scanHyphenGroups fuel consumedRev remaining
    consumedRev.reverse ++ remaining = scan.consumed ++ scan.remaining := by
  fun_induction scanHyphenGroups fuel consumedRev remaining with
  | case1 => simp
  | case2 fuel consumedRev next rest plain nextRev _isStart
      inductionHypothesis =>
      dsimp only at inductionHypothesis ⊢
      rw [← inductionHypothesis]
      rw [reverse_foldl_prepend]
      rw [takeWhile_partition isCoreIdentifierContinue rest]
      simp [nextRev, List.append_assoc]
  | case3 => simp
  | case4 => simp

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

private theorem scanLetterIdentifier_exact (first : Char)
    (remaining : List Char) :
    let scan := scanLetterIdentifier first remaining
    ∃ consumed,
      first :: remaining = consumed ++ scan.remaining ∧
        scan.kind.spelling = String.ofList consumed := by
  fun_cases scanLetterIdentifier first remaining with
  | case1 plain rest plainRemaining tail text =>
      dsimp only
      refine ⟨first :: plain.consumed ++ '$' :: tail.consumed, ?_, rfl⟩
      have plainPartition :
          remaining = plain.consumed ++ plain.remaining := by
        simpa only [plain] using
          takeWhile_partition isCoreIdentifierContinue remaining
      have tailPartition : rest = tail.consumed ++ tail.remaining := by
        simpa only [tail] using
          takeWhile_partition isYulIdentifierContinue rest
      rw [plainPartition]
      rw [plainRemaining]
      rw [tailPartition]
      simp [List.append_assoc]
  | case2 plain _notYul full text kind =>
      dsimp only
      refine ⟨full.consumed, ?_, ?_⟩
      · calc
          first :: remaining =
              (first :: plain.consumed) ++ plain.remaining := by
            have plainPartition :
                remaining = plain.consumed ++ plain.remaining := by
              simpa only [plain] using
                takeWhile_partition isCoreIdentifierContinue remaining
            rw [plainPartition]
            simp
          _ = full.consumed ++ full.remaining := by
            simpa [full] using
              scanHyphenGroups_partition (plain.remaining.length + 1)
                (first :: plain.consumed).reverse plain.remaining
      · dsimp only [kind]
        split
        · rename_i keyword recognized
          change keyword.spelling = String.ofList full.consumed
          exact HardKeyword.spelling_eq_of_ofString?_eq_some
            text keyword recognized
        · change text = String.ofList full.consumed
          rfl

private theorem scanMarkedYulIdentifier_exact (first : Char)
    (remaining : List Char) :
    let scan := scanMarkedYulIdentifier first remaining
    ∃ consumed,
      first :: remaining = consumed ++ scan.remaining ∧
        scan.kind.spelling = String.ofList consumed := by
  unfold scanMarkedYulIdentifier
  dsimp only
  refine ⟨first :: (takeWhile isYulIdentifierContinue remaining).consumed,
    ?_, rfl⟩
  exact congrArg (List.cons first)
    (takeWhile_partition isYulIdentifierContinue remaining)

/--
A letter-led identifier scan consumes exactly the bytes represented by its
returned token spelling, including Yul and hard-keyword branches.
-/
theorem scanLetterIdentifier_advances (cursor : Nat) (first : Char)
    (remaining : List Char) :
    let scan := scanLetterIdentifier first remaining
    Advances cursor (first :: remaining)
      (cursor + scan.kind.spelling.utf8ByteSize) scan.remaining := by
  rcases scanLetterIdentifier_exact first remaining with
    ⟨consumed, partition, spelling⟩
  refine ⟨consumed, partition, ?_⟩
  simp [byteSize, spelling]

/--
A marked Yul identifier scan consumes exactly the bytes represented by its
returned token spelling.
-/
theorem scanMarkedYulIdentifier_advances (cursor : Nat) (first : Char)
    (remaining : List Char) :
    let scan := scanMarkedYulIdentifier first remaining
    Advances cursor (first :: remaining)
      (cursor + scan.kind.spelling.utf8ByteSize) scan.remaining := by
  rcases scanMarkedYulIdentifier_exact first remaining with
    ⟨consumed, partition, spelling⟩
  refine ⟨consumed, partition, ?_⟩
  simp [byteSize, spelling]

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
