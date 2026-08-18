import Solcore.Surface.Parser
import Solcore.Surface.Wire.V1.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

/-!
Closed Surface diagnostic values for the v1 publication boundary.

The public token and expectation types do not reuse their internal
counterparts.  Payload-bearing tokens carry the same refined atoms as the
published syntax tree, so future internal constructors and noncanonical
payloads fail projection explicitly.
-/

inductive TokenKind where
  | keywordFunction
  | keywordLet
  | keywordIf
  | keywordElse
  | keywordReturn
  | identifier (text : IdentifierText)
  | decimal (digits : DecimalDigits)
  | hexadecimal (digits : HexadecimalDigits)
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

def toSurface : TokenKind -> Solcore.Surface.TokenKind
  | .keywordFunction => .keywordFunction
  | .keywordLet => .keywordLet
  | .keywordIf => .keywordIf
  | .keywordElse => .keywordElse
  | .keywordReturn => .keywordReturn
  | .identifier text => .identifier text.value
  | .decimal digits => .decimal digits.value
  | .hexadecimal digits => .hexadecimal digits.value
  | .arrow => .arrow
  | .equal => .equal
  | .equalEqual => .equalEqual
  | .bang => .bang
  | .bangEqual => .bangEqual
  | .less => .less
  | .lessEqual => .lessEqual
  | .greater => .greater
  | .greaterEqual => .greaterEqual
  | .plus => .plus
  | .minus => .minus
  | .star => .star
  | .slash => .slash
  | .percent => .percent
  | .ampersand => .ampersand
  | .caret => .caret
  | .pipe => .pipe
  | .leftParen => .leftParen
  | .rightParen => .rightParen
  | .leftBrace => .leftBrace
  | .rightBrace => .rightBrace
  | .colon => .colon
  | .semicolon => .semicolon
  | .comma => .comma

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.TokenKind -> Option TokenKind
  | .keywordFunction => some .keywordFunction
  | .keywordLet => some .keywordLet
  | .keywordIf => some .keywordIf
  | .keywordElse => some .keywordElse
  | .keywordReturn => some .keywordReturn
  | .identifier value => .identifier <$> IdentifierText.ofString? value
  | .decimal value => .decimal <$> DecimalDigits.ofString? value
  | .hexadecimal value => .hexadecimal <$> HexadecimalDigits.ofString? value
  | .arrow => some .arrow
  | .equal => some .equal
  | .equalEqual => some .equalEqual
  | .bang => some .bang
  | .bangEqual => some .bangEqual
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual
  | .plus => some .plus
  | .minus => some .minus
  | .star => some .star
  | .slash => some .slash
  | .percent => some .percent
  | .ampersand => some .ampersand
  | .caret => some .caret
  | .pipe => some .pipe
  | .leftParen => some .leftParen
  | .rightParen => some .rightParen
  | .leftBrace => some .leftBrace
  | .rightBrace => some .rightBrace
  | .colon => some .colon
  | .semicolon => some .semicolon
  | .comma => some .comma
  | _ => none

@[simp] theorem ofSurface?_toSurface (kind : TokenKind) :
    ofSurface? kind.toSurface = some kind := by
  cases kind <;> simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceKind : Solcore.Surface.TokenKind}
    {kind : TokenKind}
    (projection : ofSurface? surfaceKind = some kind) :
    kind.toSurface = surfaceKind := by
  cases surfaceKind with
  | identifier value =>
      cases textProjection : IdentifierText.ofString? value with
      | none => simp [ofSurface?, textProjection] at projection
      | some text =>
          simp [ofSurface?, textProjection] at projection
          subst kind
          simp [toSurface,
            IdentifierText.value_eq_of_ofString?_eq_some textProjection]
  | decimal value =>
      cases digitsProjection : DecimalDigits.ofString? value with
      | none => simp [ofSurface?, digitsProjection] at projection
      | some digits =>
          simp [ofSurface?, digitsProjection] at projection
          subst kind
          simp [toSurface,
            DecimalDigits.value_eq_of_ofString?_eq_some digitsProjection]
  | hexadecimal value =>
      cases digitsProjection : HexadecimalDigits.ofString? value with
      | none => simp [ofSurface?, digitsProjection] at projection
      | some digits =>
          simp [ofSurface?, digitsProjection] at projection
          subst kind
          simp [toSurface,
            HexadecimalDigits.value_eq_of_ofString?_eq_some digitsProjection]
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
    arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
    greater | greaterEqual | plus | minus | star | slash | percent |
    ampersand | caret | pipe | leftParen | rightParen | leftBrace |
    rightBrace | colon | semicolon | comma =>
      simp [ofSurface?] at projection
      subst kind
      rfl

theorem exists_ofSurface?_eq_some_of_canonical
    (surfaceKind : Solcore.Surface.TokenKind)
    (canonical : surfaceKind.Canonical) :
    ∃ kind, ofSurface? surfaceKind = some kind := by
  cases surfaceKind with
  | identifier value =>
      have valid : identifierTextValid value = true := by
        rw [identifierTextValid_eq_tokenKind_isCanonical]
        exact canonical
      let text : IdentifierText := { value, valid }
      refine ⟨.identifier text, ?_⟩
      simp [ofSurface?, IdentifierText.ofString?, valid, text]
  | decimal value =>
      have valid : decimalDigitsValid value = true := by
        rw [decimalDigitsValid_eq_tokenKind_isCanonical]
        exact canonical
      let digits : DecimalDigits := { value, valid }
      refine ⟨.decimal digits, ?_⟩
      simp [ofSurface?, DecimalDigits.ofString?, valid, digits]
  | hexadecimal value =>
      have valid : hexadecimalDigitsValid value = true := by
        rw [hexadecimalDigitsValid_eq_tokenKind_isCanonical]
        exact canonical
      let digits : HexadecimalDigits := { value, valid }
      refine ⟨.hexadecimal digits, ?_⟩
      simp [ofSurface?, HexadecimalDigits.ofString?, valid, digits]
  | keywordFunction => exact ⟨.keywordFunction, rfl⟩
  | keywordLet => exact ⟨.keywordLet, rfl⟩
  | keywordIf => exact ⟨.keywordIf, rfl⟩
  | keywordElse => exact ⟨.keywordElse, rfl⟩
  | keywordReturn => exact ⟨.keywordReturn, rfl⟩
  | arrow => exact ⟨.arrow, rfl⟩
  | equal => exact ⟨.equal, rfl⟩
  | equalEqual => exact ⟨.equalEqual, rfl⟩
  | bang => exact ⟨.bang, rfl⟩
  | bangEqual => exact ⟨.bangEqual, rfl⟩
  | less => exact ⟨.less, rfl⟩
  | lessEqual => exact ⟨.lessEqual, rfl⟩
  | greater => exact ⟨.greater, rfl⟩
  | greaterEqual => exact ⟨.greaterEqual, rfl⟩
  | plus => exact ⟨.plus, rfl⟩
  | minus => exact ⟨.minus, rfl⟩
  | star => exact ⟨.star, rfl⟩
  | slash => exact ⟨.slash, rfl⟩
  | percent => exact ⟨.percent, rfl⟩
  | ampersand => exact ⟨.ampersand, rfl⟩
  | caret => exact ⟨.caret, rfl⟩
  | pipe => exact ⟨.pipe, rfl⟩
  | leftParen => exact ⟨.leftParen, rfl⟩
  | rightParen => exact ⟨.rightParen, rfl⟩
  | leftBrace => exact ⟨.leftBrace, rfl⟩
  | rightBrace => exact ⟨.rightBrace, rfl⟩
  | colon => exact ⟨.colon, rfl⟩
  | semicolon => exact ⟨.semicolon, rfl⟩
  | comma => exact ⟨.comma, rfl⟩

end TokenKind

inductive ParseExpectation where
  | token (kind : TokenKind)
  | identifier
  | type
  | expression
  | argumentOrRightParen
  | commaOrRightParen
  | bindingOrReturn
  | endOfFile
  deriving Repr, BEq, DecidableEq

namespace ParseExpectation

def toSurface : ParseExpectation -> Solcore.Surface.ParseExpectation
  | .token kind => .token kind.toSurface
  | .identifier => .identifier
  | .type => .type
  | .expression => .expression
  | .argumentOrRightParen => .argumentOrRightParen
  | .commaOrRightParen => .commaOrRightParen
  | .bindingOrReturn => .bindingOrReturn
  | .endOfFile => .endOfFile

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.ParseExpectation -> Option ParseExpectation
  | .token kind => .token <$> TokenKind.ofSurface? kind
  | .identifier => some .identifier
  | .type => some .type
  | .expression => some .expression
  | .argumentOrRightParen => some .argumentOrRightParen
  | .commaOrRightParen => some .commaOrRightParen
  | .bindingOrReturn => some .bindingOrReturn
  | .endOfFile => some .endOfFile
  | _ => none

@[simp] theorem ofSurface?_toSurface (expectation : ParseExpectation) :
    ofSurface? expectation.toSurface = some expectation := by
  cases expectation <;> simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceExpectation : Solcore.Surface.ParseExpectation}
    {expectation : ParseExpectation}
    (projection : ofSurface? surfaceExpectation = some expectation) :
    expectation.toSurface = surfaceExpectation := by
  cases surfaceExpectation with
  | token surfaceKind =>
      cases kindProjection : TokenKind.ofSurface? surfaceKind with
      | none => simp [ofSurface?, kindProjection] at projection
      | some kind =>
          simp [ofSurface?, kindProjection] at projection
          subst expectation
          simp [toSurface,
            TokenKind.toSurface_eq_of_ofSurface?_eq_some kindProjection]
  | identifier | type | expression | argumentOrRightParen |
    commaOrRightParen | bindingOrReturn | endOfFile =>
      simp [ofSurface?] at projection
      subst expectation
      rfl

theorem exists_ofSurface?_eq_some_of_wellFormed
    (surfaceExpectation : Solcore.Surface.ParseExpectation)
    (wellFormed : surfaceExpectation.WellFormed) :
    ∃ expectation, ofSurface? surfaceExpectation = some expectation := by
  cases surfaceExpectation with
  | token surfaceKind =>
      obtain ⟨kind, projection⟩ :=
        TokenKind.exists_ofSurface?_eq_some_of_canonical
          surfaceKind wellFormed
      exact ⟨.token kind, by simp [ofSurface?, projection]⟩
  | identifier => exact ⟨.identifier, rfl⟩
  | type => exact ⟨.type, rfl⟩
  | expression => exact ⟨.expression, rfl⟩
  | argumentOrRightParen => exact ⟨.argumentOrRightParen, rfl⟩
  | commaOrRightParen => exact ⟨.commaOrRightParen, rfl⟩
  | bindingOrReturn => exact ⟨.bindingOrReturn, rfl⟩
  | endOfFile => exact ⟨.endOfFile, rfl⟩

end ParseExpectation

/-!
Only equality and relational operators can be the second operator in an SP0002
diagnostic.  This type prevents other binary operators from being constructed
in the frozen diagnostic language.
-/
inductive NonAssociativeBinaryOp where
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  deriving Repr, BEq, DecidableEq

namespace NonAssociativeBinaryOp

def toBinaryOp : NonAssociativeBinaryOp -> BinaryOp
  | .lt => .lt
  | .gt => .gt
  | .le => .le
  | .ge => .ge
  | .eq => .eq
  | .ne => .ne

def toSurface (operator : NonAssociativeBinaryOp) :
    Solcore.Surface.BinaryOp :=
  operator.toBinaryOp.toSurface

def ofBinaryOp? : BinaryOp -> Option NonAssociativeBinaryOp
  | .lt => some .lt
  | .gt => some .gt
  | .le => some .le
  | .ge => some .ge
  | .eq => some .eq
  | .ne => some .ne
  | _ => none

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.BinaryOp -> Option NonAssociativeBinaryOp
  | .lt => some .lt
  | .gt => some .gt
  | .le => some .le
  | .ge => some .ge
  | .eq => some .eq
  | .ne => some .ne
  | _ => none

@[simp] theorem ofBinaryOp?_toBinaryOp
    (operator : NonAssociativeBinaryOp) :
    ofBinaryOp? operator.toBinaryOp = some operator := by
  cases operator <;> rfl

@[simp] theorem ofSurface?_toSurface
    (operator : NonAssociativeBinaryOp) :
    ofSurface? operator.toSurface = some operator := by
  cases operator <;> rfl

theorem toBinaryOp_eq_of_ofBinaryOp?_eq_some
    {binaryOperator : BinaryOp}
    {operator : NonAssociativeBinaryOp}
    (projection : ofBinaryOp? binaryOperator = some operator) :
    operator.toBinaryOp = binaryOperator := by
  cases binaryOperator <;>
    simp [ofBinaryOp?] at projection
  all_goals subst operator <;> rfl

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceOperator : Solcore.Surface.BinaryOp}
    {operator : NonAssociativeBinaryOp}
    (projection : ofSurface? surfaceOperator = some operator) :
    operator.toSurface = surfaceOperator := by
  cases surfaceOperator <;>
    simp [ofSurface?] at projection
  all_goals subst operator <;> rfl

@[simp] theorem toSurface_associativity
    (operator : NonAssociativeBinaryOp) :
    operator.toSurface.associativity = .nonAssociative := by
  cases operator <;> rfl

end NonAssociativeBinaryOp

inductive DiagnosticPhase where
  | surfaceLexing
  | surfaceParsing
  deriving Repr, BEq, DecidableEq

inductive DiagnosticSeverity where
  | error
  deriving Repr, BEq, DecidableEq

/-!
The argument variants correspond one-to-one with the four frozen diagnostic
codes.  JSON codecs can therefore encode only the exact argument object for a
diagnostic kind.
-/
inductive DiagnosticArguments where
  | invalidCharacter (character : Char)
  | unterminatedBlockComment
  | expected (expectation : ParseExpectation) (found : Option TokenKind)
  | nonAssociative (operator : NonAssociativeBinaryOp)
  deriving Repr, BEq, DecidableEq

inductive DiagnosticKind where
  | invalidCharacter (character : Char)
  | unterminatedBlockComment
  | expected (expectation : ParseExpectation) (found : Option TokenKind)
  | nonAssociative (operator : NonAssociativeBinaryOp)
  deriving Repr, BEq, DecidableEq

namespace DiagnosticKind

def code : DiagnosticKind -> String
  | .invalidCharacter _ => "SL0001"
  | .unterminatedBlockComment => "SL0002"
  | .expected _ _ => "SP0001"
  | .nonAssociative _ => "SP0002"

def phase : DiagnosticKind -> DiagnosticPhase
  | .invalidCharacter _ | .unterminatedBlockComment => .surfaceLexing
  | .expected _ _ | .nonAssociative _ => .surfaceParsing

def arguments : DiagnosticKind -> DiagnosticArguments
  | .invalidCharacter character => .invalidCharacter character
  | .unterminatedBlockComment => .unterminatedBlockComment
  | .expected expectation found => .expected expectation found
  | .nonAssociative operator => .nonAssociative operator

end DiagnosticKind

structure Diagnostic where
  primary : SourceSpan
  kind : DiagnosticKind
  display : Option String := none
  deriving Repr, BEq, DecidableEq

namespace Diagnostic

def code (diagnostic : Diagnostic) : String :=
  diagnostic.kind.code

def severity (_diagnostic : Diagnostic) : DiagnosticSeverity :=
  .error

def phase (diagnostic : Diagnostic) : DiagnosticPhase :=
  diagnostic.kind.phase

def arguments (diagnostic : Diagnostic) : DiagnosticArguments :=
  diagnostic.kind.arguments

def toLexError? (diagnostic : Diagnostic) : Option Solcore.Surface.LexError :=
  match diagnostic.kind with
  | .invalidCharacter character => some {
      code := "SL0001"
      span := diagnostic.primary.toSurface
      kind := .invalidCharacter character
    }
  | .unterminatedBlockComment => some {
      code := "SL0002"
      span := diagnostic.primary.toSurface
      kind := .unterminatedBlockComment
    }
  | _ => none

def toParseError? (diagnostic : Diagnostic) : Option Solcore.Surface.ParseError :=
  match diagnostic.kind with
  | .expected expectation found => some {
      code := "SP0001"
      span := diagnostic.primary.toSurface
      kind := .expected expectation.toSurface (found.map TokenKind.toSurface)
    }
  | .nonAssociative operator => some {
      code := "SP0002"
      span := diagnostic.primary.toSurface
      kind := .nonAssociative operator.toSurface
    }
  | _ => none

def toFrontendError (diagnostic : Diagnostic) : Solcore.Surface.FrontendError :=
  match diagnostic.kind with
  | .invalidCharacter character => .lexical {
      code := "SL0001"
      span := diagnostic.primary.toSurface
      kind := .invalidCharacter character
    }
  | .unterminatedBlockComment => .lexical {
      code := "SL0002"
      span := diagnostic.primary.toSurface
      kind := .unterminatedBlockComment
    }
  | .expected expectation found => .syntactic {
      code := "SP0001"
      span := diagnostic.primary.toSurface
      kind := .expected expectation.toSurface (found.map TokenKind.toSurface)
    }
  | .nonAssociative operator => .syntactic {
      code := "SP0002"
      span := diagnostic.primary.toSurface
      kind := .nonAssociative operator.toSurface
    }

def ValidFor
    (diagnostic : Diagnostic)
    (file : Solcore.Surface.SourceFile) : Prop :=
  match diagnostic.toFrontendError with
  | .lexical error =>
      Solcore.Surface.LexicalGrammar.failureAt
          file error.span.startByte = some error
  | .syntactic error => error.WellFormedFor file
  | .internal _ => False

def CanonicalFor
    (diagnostic : Diagnostic)
    (file : Solcore.Surface.SourceFile) : Prop :=
  diagnostic.display = none ∧ diagnostic.ValidFor file

end Diagnostic

/-!
Project an internal lexer error only when the declarative lexer recognizes the
complete error at the claimed cursor.  This validates the exact code, source
label, UTF-8 range, character payload, comment opener, and end-of-file bound.
-/
set_option match.ignoreUnusedAlts true in
def ofLexError?
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError) : Option Diagnostic :=
  if _recognized :
      Solcore.Surface.LexicalGrammar.failureAt file error.span.startByte =
        some error then
    match error.kind with
    | .invalidCharacter character =>
        if error.code != "SL0001" then none else
        some {
          primary := SourceSpan.ofSurface error.span
          kind := .invalidCharacter character
        }
    | .unterminatedBlockComment =>
        if error.code != "SL0002" then none else
        some {
          primary := SourceSpan.ofSurface error.span
          kind := .unterminatedBlockComment
        }
    | _ => none
  else
    none

private def lexErrorCodeMatches (error : Solcore.Surface.LexError) : Prop :=
  match error.kind with
  | .invalidCharacter _ => error.code = "SL0001"
  | .unterminatedBlockComment => error.code = "SL0002"

private theorem lexErrorCodeMatches_of_failureAt_eq_some
    (file : Solcore.Surface.SourceFile)
    (offset : Nat)
    (error : Solcore.Surface.LexError)
    (recognized :
      Solcore.Surface.LexicalGrammar.failureAt file offset = some error) :
    lexErrorCodeMatches error := by
  have rejection :=
    (Solcore.Surface.LexicalGrammar.failureAt_eq_some_iff
      file offset error).mp recognized
  cases rejection <;> rfl

private def projectFound? : Option Solcore.Surface.TokenKind -> Option (Option TokenKind)
  | none => some none
  | some kind => some <$> TokenKind.ofSurface? kind

private theorem foundToSurface_eq_of_projectFound?_eq_some
    {surfaceFound : Option Solcore.Surface.TokenKind}
    {found : Option TokenKind}
    (projection : projectFound? surfaceFound = some found) :
    found.map TokenKind.toSurface = surfaceFound := by
  cases surfaceFound with
  | none =>
      simp [projectFound?] at projection
      subst found
      rfl
  | some surfaceKind =>
      cases kindProjection : TokenKind.ofSurface? surfaceKind with
      | none => simp [projectFound?, kindProjection] at projection
      | some kind =>
          simp [projectFound?, kindProjection] at projection
          subst found
          simp [TokenKind.toSurface_eq_of_ofSurface?_eq_some kindProjection]

private theorem exists_nonAssociativeBinaryOp_ofSurface?_eq_some
    (surfaceOperator : Solcore.Surface.BinaryOp)
    (nonAssociative :
      surfaceOperator.associativity = .nonAssociative) :
    ∃ operator,
      NonAssociativeBinaryOp.ofSurface? surfaceOperator = some operator := by
  cases surfaceOperator <;>
    simp [Solcore.Surface.BinaryOp.associativity,
      NonAssociativeBinaryOp.ofSurface?] at nonAssociative ⊢

/-!
Project an internal parser error only when its code and primary span agree with
the source file.  A found token must be canonical and must spell the exact
source slice.  A missing token must use the empty end-of-file span.  The second
operator in a non-associative chain is checked against its exact source token.
-/
set_option match.ignoreUnusedAlts true in
def ofParseError?
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.ParseError) : Option Diagnostic :=
  if _wellFormed : error.isWellFormedFor file = true then
    match error.kind with
    | .expected surfaceExpectation surfaceFound => do
        let expectation <- ParseExpectation.ofSurface? surfaceExpectation
        let found <- projectFound? surfaceFound
        some {
          primary := SourceSpan.ofSurface error.span
          kind := .expected expectation found
        }
    | .nonAssociative surfaceOperator => do
        let operator <- NonAssociativeBinaryOp.ofSurface? surfaceOperator
        some {
          primary := SourceSpan.ofSurface error.span
          kind := .nonAssociative operator
        }
    | _ => none
  else
    none

def ofFrontendError?
    (file : Solcore.Surface.SourceFile) :
    Solcore.Surface.FrontendError -> Option Diagnostic
  | .lexical error => ofLexError? file error
  | .syntactic error => ofParseError? file error
  | .internal _ => none

theorem exists_ofParseError?_eq_some_of_wellFormedFor
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.ParseError)
    (wellFormed : error.WellFormedFor file) :
    ∃ diagnostic, ofParseError? file error = some diagnostic := by
  have executable : error.isWellFormedFor file = true :=
    (Solcore.Surface.ParseError.isWellFormedFor_eq_true_iff
      error file).mpr wellFormed
  cases error with
  | mk code span kind =>
      cases kind with
      | expected surfaceExpectation surfaceFound =>
          have expectationWellFormed : surfaceExpectation.WellFormed :=
            wellFormed.2.1
          obtain ⟨expectation, expectationProjection⟩ :=
            ParseExpectation.exists_ofSurface?_eq_some_of_wellFormed
              surfaceExpectation expectationWellFormed
          cases surfaceFound with
          | none =>
              refine ⟨{
                primary := SourceSpan.ofSurface span
                kind := .expected expectation none
              }, ?_⟩
              simp [ofParseError?, executable, expectationProjection,
                projectFound?]
          | some surfaceKind =>
              have kindCanonical : surfaceKind.Canonical :=
                wellFormed.2.2.1
              obtain ⟨found, foundProjection⟩ :=
                TokenKind.exists_ofSurface?_eq_some_of_canonical
                  surfaceKind kindCanonical
              refine ⟨{
                primary := SourceSpan.ofSurface span
                kind := .expected expectation (some found)
              }, ?_⟩
              simp [ofParseError?, executable, expectationProjection,
                projectFound?, foundProjection]
      | nonAssociative surfaceOperator =>
          obtain ⟨operator, operatorProjection⟩ :=
            exists_nonAssociativeBinaryOp_ofSurface?_eq_some
              surfaceOperator wellFormed.2.1
          refine ⟨{
            primary := SourceSpan.ofSurface span
            kind := .nonAssociative operator
          }, ?_⟩
          simp [ofParseError?, executable, operatorProjection]

theorem exists_ofLexError?_eq_some_of_failureAt_eq_some
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (recognized :
      Solcore.Surface.LexicalGrammar.failureAt file error.span.startByte =
        some error) :
    ∃ diagnostic, ofLexError? file error = some diagnostic := by
  have codeMatches :=
    lexErrorCodeMatches_of_failureAt_eq_some
      file error.span.startByte error recognized
  cases error with
  | mk code span kind =>
      cases kind with
      | invalidCharacter character =>
          refine ⟨{
            primary := SourceSpan.ofSurface span
            kind := .invalidCharacter character
          }, ?_⟩
          simp [ofLexError?, recognized, lexErrorCodeMatches]
            at codeMatches ⊢
          exact codeMatches
      | unterminatedBlockComment =>
          refine ⟨{
            primary := SourceSpan.ofSurface span
            kind := .unterminatedBlockComment
          }, ?_⟩
          simp [ofLexError?, recognized, lexErrorCodeMatches]
            at codeMatches ⊢
          exact codeMatches

theorem exists_ofLexError?_eq_some_of_lexer_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (failure :
      Solcore.Surface.Lexer.lex file =
        .error (.source error)) :
    ∃ diagnostic, ofLexError? file error = some diagnostic := by
  exact exists_ofLexError?_eq_some_of_failureAt_eq_some file error
    (Solcore.Surface.Lexer.lex_source_failure_recognized file error failure)

theorem ofFrontendError?_toFrontendError_of_canonicalFor
    (file : Solcore.Surface.SourceFile)
    (diagnostic : Diagnostic)
    (canonical : diagnostic.CanonicalFor file) :
    ofFrontendError? file diagnostic.toFrontendError = some diagnostic := by
  cases diagnostic with
  | mk primary kind display =>
      have displayEquation := canonical.1
      change display = none at displayEquation
      subst display
      cases kind with
      | invalidCharacter character =>
          have recognized := canonical.2
          simp [Diagnostic.ValidFor, Diagnostic.toFrontendError]
            at recognized
          simp [ofFrontendError?, Diagnostic.toFrontendError,
            ofLexError?, recognized]
      | unterminatedBlockComment =>
          have recognized := canonical.2
          simp [Diagnostic.ValidFor, Diagnostic.toFrontendError]
            at recognized
          simp [ofFrontendError?, Diagnostic.toFrontendError,
            ofLexError?, recognized]
      | expected expectation found =>
          have wellFormed := canonical.2
          simp [Diagnostic.ValidFor, Diagnostic.toFrontendError]
            at wellFormed
          have executable :=
            (Solcore.Surface.ParseError.isWellFormedFor_eq_true_iff
              _ file).mpr wellFormed
          cases found with
          | none =>
              have executable' :
                  ({
                    code := "SP0001"
                    span := primary.toSurface
                    kind := .expected expectation.toSurface none
                  } : Solcore.Surface.ParseError).isWellFormedFor file = true := by
                simpa using executable
              simp [ofFrontendError?, Diagnostic.toFrontendError,
                ofParseError?, executable', projectFound?]
          | some found =>
              have executable' :
                  ({
                    code := "SP0001"
                    span := primary.toSurface
                    kind := .expected expectation.toSurface
                      (some found.toSurface)
                  } : Solcore.Surface.ParseError).isWellFormedFor file = true := by
                simpa using executable
              simp [ofFrontendError?, Diagnostic.toFrontendError,
                ofParseError?, executable', projectFound?]
      | nonAssociative operator =>
          have wellFormed := canonical.2
          simp [Diagnostic.ValidFor, Diagnostic.toFrontendError]
            at wellFormed
          have executable :=
            (Solcore.Surface.ParseError.isWellFormedFor_eq_true_iff
              _ file).mpr wellFormed
          simp [ofFrontendError?, Diagnostic.toFrontendError,
            ofParseError?, executable]

theorem toLexError?_eq_some_of_ofLexError?_eq_some
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.LexError}
    {diagnostic : Diagnostic}
    (projection : ofLexError? file error = some diagnostic) :
    diagnostic.toLexError? = some error := by
  cases error with
  | mk code span kind =>
      cases kind <;>
        simp [ofLexError?, Diagnostic.toLexError?] at projection ⊢
      all_goals rcases projection with ⟨_, codeEquation, diagnosticEquation⟩
      all_goals subst code
      all_goals subst diagnostic
      all_goals simp

theorem toParseError?_eq_some_of_ofParseError?_eq_some
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.ParseError}
    {diagnostic : Diagnostic}
    (projection : ofParseError? file error = some diagnostic) :
    diagnostic.toParseError? = some error := by
  unfold ofParseError? at projection
  split at projection
  next wellFormed =>
    cases error with
    | mk code span kind =>
        cases kind with
        | expected surfaceExpectation surfaceFound =>
            simp [Solcore.Surface.ParseError.isWellFormedFor]
              at wellFormed
            cases expectationProjection :
                ParseExpectation.ofSurface? surfaceExpectation with
            | none => simp [expectationProjection] at projection
            | some expectation =>
                cases foundProjection : projectFound? surfaceFound with
                | none =>
                    simp [expectationProjection, foundProjection] at projection
                | some found =>
                    simp [expectationProjection, foundProjection] at projection
                    subst diagnostic
                    have codeEquation := wellFormed.1.1
                    subst code
                    simp [Diagnostic.toParseError?,
                      ParseExpectation.toSurface_eq_of_ofSurface?_eq_some
                        expectationProjection,
                      foundToSurface_eq_of_projectFound?_eq_some
                        foundProjection]
        | nonAssociative surfaceOperator =>
            simp [Solcore.Surface.ParseError.isWellFormedFor]
              at wellFormed
            cases operatorProjection :
                NonAssociativeBinaryOp.ofSurface? surfaceOperator with
            | none => simp [operatorProjection] at projection
            | some operator =>
                simp [operatorProjection] at projection
                subst diagnostic
                have codeEquation := wellFormed.1.1
                subst code
                simp [Diagnostic.toParseError?,
                  NonAssociativeBinaryOp.toSurface_eq_of_ofSurface?_eq_some
                    operatorProjection]
  next _ => simp at projection

theorem toFrontendError_eq_of_ofFrontendError?_eq_some
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.FrontendError}
    {diagnostic : Diagnostic}
    (projection : ofFrontendError? file error = some diagnostic) :
    diagnostic.toFrontendError = error := by
  cases error with
  | lexical lexicalError =>
      have reconstruction :=
        toLexError?_eq_some_of_ofLexError?_eq_some projection
      cases diagnostic with
      | mk primary kind display =>
          cases kind <;>
            simp [Diagnostic.toLexError?, Diagnostic.toFrontendError]
              at reconstruction ⊢
          all_goals subst lexicalError
          all_goals rfl
  | syntactic parseError =>
      have reconstruction :=
        toParseError?_eq_some_of_ofParseError?_eq_some projection
      cases diagnostic with
      | mk primary kind display =>
          cases kind <;>
            simp [Diagnostic.toParseError?, Diagnostic.toFrontendError]
              at reconstruction ⊢
          all_goals subst parseError
          all_goals rfl
  | internal invariant =>
      simp [ofFrontendError?] at projection

end Solcore.Surface.Wire.V1
