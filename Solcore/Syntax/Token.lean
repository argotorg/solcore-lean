import Solcore.Syntax.Source

set_option autoImplicit false

namespace Solcore.Syntax

/-- Words emitted as dedicated tokens by the canonical Rust lexer. -/
inductive HardKeyword where
  | contractKw
  | importKw
  | exportKw
  | asKw
  | letKw
  | dataKw
  | classKw
  | forallKw
  | instanceKw
  | ifKw
  | elseKw
  | forKw
  | switchKw
  | typeKw
  | caseKw
  | defaultKw
  | matchKw
  | publicKw
  | payableKw
  | functionKw
  | constructorKw
  | fallbackKw
  | returnKw
  | leaveKw
  | continueKw
  | breakKw
  | lamKw
  | assemblyKw
  | pragmaKw
  | trueKw
  | falseKw
  deriving Repr, BEq, DecidableEq

namespace HardKeyword

/-- Unique source spelling of a hard keyword. -/
def spelling : HardKeyword → String
  | .contractKw => "contract"
  | .importKw => "import"
  | .exportKw => "export"
  | .asKw => "as"
  | .letKw => "let"
  | .dataKw => "data"
  | .classKw => "class"
  | .forallKw => "forall"
  | .instanceKw => "instance"
  | .ifKw => "if"
  | .elseKw => "else"
  | .forKw => "for"
  | .switchKw => "switch"
  | .typeKw => "type"
  | .caseKw => "case"
  | .defaultKw => "default"
  | .matchKw => "match"
  | .publicKw => "public"
  | .payableKw => "payable"
  | .functionKw => "function"
  | .constructorKw => "constructor"
  | .fallbackKw => "fallback"
  | .returnKw => "return"
  | .leaveKw => "leave"
  | .continueKw => "continue"
  | .breakKw => "break"
  | .lamKw => "lam"
  | .assemblyKw => "assembly"
  | .pragmaKw => "pragma"
  | .trueKw => "true"
  | .falseKw => "false"

/-- Recognize a complete hard-keyword spelling. -/
def ofString? : String → Option HardKeyword
  | "contract" => some .contractKw
  | "import" => some .importKw
  | "export" => some .exportKw
  | "as" => some .asKw
  | "let" => some .letKw
  | "data" => some .dataKw
  | "class" => some .classKw
  | "forall" => some .forallKw
  | "instance" => some .instanceKw
  | "if" => some .ifKw
  | "else" => some .elseKw
  | "for" => some .forKw
  | "switch" => some .switchKw
  | "type" => some .typeKw
  | "case" => some .caseKw
  | "default" => some .defaultKw
  | "match" => some .matchKw
  | "public" => some .publicKw
  | "payable" => some .payableKw
  | "function" => some .functionKw
  | "constructor" => some .constructorKw
  | "fallback" => some .fallbackKw
  | "return" => some .returnKw
  | "leave" => some .leaveKw
  | "continue" => some .continueKw
  | "break" => some .breakKw
  | "lam" => some .lamKw
  | "assembly" => some .assemblyKw
  | "pragma" => some .pragmaKw
  | "true" => some .trueKw
  | "false" => some .falseKw
  | _ => none

@[simp] theorem ofString?_spelling (keyword : HardKeyword) :
    ofString? keyword.spelling = some keyword := by
  cases keyword <;> rfl

theorem spelling_eq_of_ofString?_eq_some (text : String)
    (keyword : HardKeyword) (recognized : ofString? text = some keyword) :
    keyword.spelling = text := by
  fun_cases ofString? text <;> simp [ofString?] at recognized
  all_goals subst keyword <;> rfl

end HardKeyword

/--
Grammar-selected words that remain ordinary identifier tokens. They may still
be used as names outside the production that selects them.
-/
inductive ContextualKeyword where
  | comptime
  | derive
  | enum
  | from
  | hiding
  | impl
  | mapping
  | returns
  | trait
  | where
  | while
  deriving Repr, BEq, DecidableEq

namespace ContextualKeyword

def spelling : ContextualKeyword → String
  | .comptime => "comptime"
  | .derive => "derive"
  | .enum => "enum"
  | .from => "from"
  | .hiding => "hiding"
  | .impl => "impl"
  | .mapping => "mapping"
  | .returns => "returns"
  | .trait => "trait"
  | .where => "where"
  | .while => "while"

def ofString? : String → Option ContextualKeyword
  | "comptime" => some .comptime
  | "derive" => some .derive
  | "enum" => some .enum
  | "from" => some .from
  | "hiding" => some .hiding
  | "impl" => some .impl
  | "mapping" => some .mapping
  | "returns" => some .returns
  | "trait" => some .trait
  | "where" => some .where
  | "while" => some .while
  | _ => none

@[simp] theorem ofString?_spelling (keyword : ContextualKeyword) :
    ofString? keyword.spelling = some keyword := by
  cases keyword <;> rfl

end ContextualKeyword

/-- Complete punctuation and operator catalog of the canonical lexer. -/
inductive Symbol where
  | colonEqual
  | arrow
  | fatArrow
  | equalEqual
  | notEqual
  | greaterEqual
  | lessEqual
  | logicalAnd
  | logicalOr
  | plusEqual
  | minusEqual
  | starEqual
  | slashEqual
  | caretEqual
  | ampEqual
  | pipeEqual
  | percentEqual
  | tildeEqual
  | plus
  | minus
  | star
  | slash
  | percent
  | bang
  | tilde
  | less
  | greater
  | equal
  | pipe
  | amp
  | caret
  | at
  | question
  | hash
  | dot
  | colon
  | semicolon
  | comma
  | leftParen
  | rightParen
  | leftBrace
  | rightBrace
  | leftBracket
  | rightBracket
  | underscore
  deriving Repr, BEq, DecidableEq

namespace Symbol

/-- Unique source spelling of a symbol. -/
def spelling : Symbol → String
  | .colonEqual => ":="
  | .arrow => "->"
  | .fatArrow => "=>"
  | .equalEqual => "=="
  | .notEqual => "!="
  | .greaterEqual => ">="
  | .lessEqual => "<="
  | .logicalAnd => "&&"
  | .logicalOr => "||"
  | .plusEqual => "+="
  | .minusEqual => "-="
  | .starEqual => "*="
  | .slashEqual => "/="
  | .caretEqual => "^="
  | .ampEqual => "&="
  | .pipeEqual => "|="
  | .percentEqual => "%="
  | .tildeEqual => "~="
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .percent => "%"
  | .bang => "!"
  | .tilde => "~"
  | .less => "<"
  | .greater => ">"
  | .equal => "="
  | .pipe => "|"
  | .amp => "&"
  | .caret => "^"
  | .at => "@"
  | .question => "?"
  | .hash => "#"
  | .dot => "."
  | .colon => ":"
  | .semicolon => ";"
  | .comma => ","
  | .leftParen => "("
  | .rightParen => ")"
  | .leftBrace => "{"
  | .rightBrace => "}"
  | .leftBracket => "["
  | .rightBracket => "]"
  | .underscore => "_"

end Symbol

/-- Payload emitted by canonical lexical analysis. -/
inductive TokenKind where
  | keyword (keyword : HardKeyword)
  | symbol (symbol : Symbol)
  | identifier (text : String)
  | yulIdentifier (text : String)
  | decimalLiteral (spelling : String)
  | hexadecimalLiteral (spelling : String)
  | stringLiteral (spelling : String)
  | yulMetaBacktick (spelling : String)
  | yulMetaInterpolation (spelling : String)
  deriving Repr, BEq, DecidableEq

/-- One lexical token with its exact source range. -/
abbrev Token := Located TokenKind

namespace TokenKind

/-- Source spelling when it is carried or uniquely determined by the token. -/
def spelling : TokenKind → String
  | TokenKind.keyword value => HardKeyword.spelling value
  | TokenKind.symbol value => Symbol.spelling value
  | .identifier text
  | .yulIdentifier text
  | .decimalLiteral text
  | .hexadecimalLiteral text
  | .stringLiteral text
  | .yulMetaBacktick text
  | .yulMetaInterpolation text => text

/-- Whether an identifier token is the requested contextual keyword. -/
def isContextual (kind : TokenKind) (keyword : ContextualKeyword) : Bool :=
  match kind with
  | .identifier text => text == keyword.spelling
  | _ => false

end TokenKind

end Solcore.Syntax
