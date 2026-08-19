import Solcore.Surface.Multi.Source

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The exact hard-keyword set of Multi Surface m2c-v1. -/
inductive HardKeyword where
  | contractKw
  | importKw
  | exportKw
  | hidingKw
  | asKw
  | letKw
  | dataKw
  | forallKw
  | classKw
  | instanceKw
  | ifKw
  | elseKw
  | forKw
  | switchKw
  | caseKw
  | defaultKw
  | leaveKw
  | continueKw
  | breakKw
  | assemblyKw
  | matchKw
  | functionKw
  | fallbackKw
  | payableKw
  | publicKw
  | constructorKw
  | returnKw
  | lamKw
  | typeKw
  | pragmaKw
  deriving Repr, BEq, DecidableEq

namespace HardKeyword

/-- The unique ASCII source spelling of a hard keyword. -/
def spelling : HardKeyword → String
  | .contractKw => "contract"
  | .importKw => "import"
  | .exportKw => "export"
  | .hidingKw => "hiding"
  | .asKw => "as"
  | .letKw => "let"
  | .dataKw => "data"
  | .forallKw => "forall"
  | .classKw => "class"
  | .instanceKw => "instance"
  | .ifKw => "if"
  | .elseKw => "else"
  | .forKw => "for"
  | .switchKw => "switch"
  | .caseKw => "case"
  | .defaultKw => "default"
  | .leaveKw => "leave"
  | .continueKw => "continue"
  | .breakKw => "break"
  | .assemblyKw => "assembly"
  | .matchKw => "match"
  | .functionKw => "function"
  | .fallbackKw => "fallback"
  | .payableKw => "payable"
  | .publicKw => "public"
  | .constructorKw => "constructor"
  | .returnKw => "return"
  | .lamKw => "lam"
  | .typeKw => "type"
  | .pragmaKw => "pragma"

/-- Recognize exactly one complete hard-keyword spelling. -/
def ofString? : String → Option HardKeyword
  | "contract" => some .contractKw
  | "import" => some .importKw
  | "export" => some .exportKw
  | "hiding" => some .hidingKw
  | "as" => some .asKw
  | "let" => some .letKw
  | "data" => some .dataKw
  | "forall" => some .forallKw
  | "class" => some .classKw
  | "instance" => some .instanceKw
  | "if" => some .ifKw
  | "else" => some .elseKw
  | "for" => some .forKw
  | "switch" => some .switchKw
  | "case" => some .caseKw
  | "default" => some .defaultKw
  | "leave" => some .leaveKw
  | "continue" => some .continueKw
  | "break" => some .breakKw
  | "assembly" => some .assemblyKw
  | "match" => some .matchKw
  | "function" => some .functionKw
  | "fallback" => some .fallbackKw
  | "payable" => some .payableKw
  | "public" => some .publicKw
  | "constructor" => some .constructorKw
  | "return" => some .returnKw
  | "lam" => some .lamKw
  | "type" => some .typeKw
  | "pragma" => some .pragmaKw
  | _ => none

@[simp] theorem ofString?_spelling (keyword : HardKeyword) :
    ofString? keyword.spelling = some keyword := by
  cases keyword <;> rfl

end HardKeyword

/-- The two spellings that become keywords only at grammar-selected sites. -/
inductive ContextualKeyword where
  | thenKw
  | comptimeKw
  deriving Repr, BEq, DecidableEq

namespace ContextualKeyword

/-- The unique ASCII source spelling of a contextual keyword. -/
def spelling : ContextualKeyword → String
  | .thenKw => "then"
  | .comptimeKw => "comptime"

end ContextualKeyword

/-- The four complete hyphenated pragma names of m2c-v1. -/
inductive PragmaKind where
  | noCoverageCondition
  | noPattersonCondition
  | noBoundedVariableCondition
  | noGenericInstanceFor
  deriving Repr, BEq, DecidableEq

namespace PragmaKind

/-- The unique complete source spelling of a pragma name. -/
def spelling : PragmaKind → String
  | .noCoverageCondition => "no-coverage-condition"
  | .noPattersonCondition => "no-patterson-condition"
  | .noBoundedVariableCondition => "no-bounded-variable-condition"
  | .noGenericInstanceFor => "no-generic-instance-for"

/-- Recognize exactly one complete pragma spelling. -/
def ofString? : String → Option PragmaKind
  | "no-coverage-condition" => some .noCoverageCondition
  | "no-patterson-condition" => some .noPattersonCondition
  | "no-bounded-variable-condition" => some .noBoundedVariableCondition
  | "no-generic-instance-for" => some .noGenericInstanceFor
  | _ => none

@[simp] theorem ofString?_spelling (kind : PragmaKind) :
    ofString? kind.spelling = some kind := by
  cases kind <;> rfl

end PragmaKind

/-- The exact punctuation and operator token set of m2c-v1. -/
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
  | caretEqual
  | ampEqual
  | pipeEqual
  | percentEqual
  | plus
  | minus
  | star
  | slash
  | percent
  | bang
  | less
  | greater
  | equal
  | pipe
  | amp
  | caret
  | at
  | question
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

/-- The unique source spelling of a symbol token. -/
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
  | .caretEqual => "^="
  | .ampEqual => "&="
  | .pipeEqual => "|="
  | .percentEqual => "%="
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .percent => "%"
  | .bang => "!"
  | .less => "<"
  | .greater => ">"
  | .equal => "="
  | .pipe => "|"
  | .amp => "&"
  | .caret => "^"
  | .at => "@"
  | .question => "?"
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

/-- A canonical identifier spelling that is not a hard keyword. -/
def identifierTextValid (text : String) : Bool :=
  pathSegmentTextValid text && (HardKeyword.ofString? text).isNone

/-- A proof-carrying Multi Surface identifier. -/
structure Identifier where
  text : String
  valid : identifierTextValid text = true
  deriving Repr, DecidableEq

namespace Identifier

instance : BEq Identifier :=
  ⟨fun left right => left.text == right.text⟩

/-- Validate one complete identifier spelling without normalization. -/
def parse (text : String) : Option Identifier :=
  if valid : identifierTextValid text = true then
    some { text, valid }
  else
    none

/-- Render an identifier without normalization. -/
def render (identifier : Identifier) : String :=
  identifier.text

@[simp] theorem parse_render (identifier : Identifier) :
    parse identifier.render = some identifier := by
  cases identifier with
  | mk text valid => simp [parse, render, valid]

theorem render_injective : Function.Injective render := by
  intro left right equality
  cases left
  cases right
  simp only [render] at equality
  simp_all

end Identifier

/-- Exact interior and delimiter ranges of one opaque assembly block. -/
structure AssemblySlicePayload where
  openBrace : SourceSpan
  contents : SourceSpan
  closeBrace : SourceSpan
  deriving Repr, BEq, DecidableEq

/-- A located opaque assembly block. -/
abbrev AssemblySlice := Located AssemblySlicePayload

/-- The closed source-preserving token payload. -/
inductive TokenKind where
  | hardKeyword (keyword : HardKeyword)
  | identifier (text : String)
  | pragmaName (kind : PragmaKind)
  | decimalLiteral (spelling : String) (digits : String)
  | hexadecimalLiteral (spelling : String) (digits : String)
  | stringLiteral (spelling : String) (decoded : String)
  | assemblyBlock (slice : AssemblySlice)
  | symbol (symbol : Symbol)
  deriving Repr, BEq, DecidableEq

/-- One token paired with its exact source lexeme. -/
abbrev Token := Located TokenKind

/-- The retained comment category. -/
inductive CommentKind where
  | line
  | block
  deriving Repr, BEq, DecidableEq

/-- One retained comment paired with its exact source range. -/
abbrev Comment := Located CommentKind

end Solcore.Surface.Multi
