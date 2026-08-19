# ADR-0015: M2c Multi Surface parser kernel

- Status: Accepted
- Decision date: 2026-08-18
- Scope: M2c internal multi-module Surface lexer and parser

## Context

ADR-0012 and ADR-0013 define and publish the deliberately small, one-file
Surface v1 grammar. ADR-0014 defines canonical workspace and source identity,
but does not define the language parsed from those sources. Module resolution
cannot be specified over compiler-owned syntax trees, parser recovery nodes, or
an open collection of source forms. It needs one closed, source-preserving AST
whose names, binders, module references, selectors, and lexical bodies can be
addressed independently of either comparison implementation.

The syntax evidence is pinned by `metadata/baselines.json`:

- Haskell Solcore at
  `1d490d8bb5f374356f06e0720655496482eb1fb4`; and
- Rust Solcore at
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`.

The Haskell parser accepts all six canonical ADR-0007 standard-library files,
but it normalizes several written forms while parsing. It turns a one-element
parenthesized expression or type into its child, turns tuples into nested
`pair` applications, converts a body containing one expression into a return,
represents an absent statement `else` as an empty body, parses integer values
instead of retaining digits, and uses character offsets in fields described as
byte offsets. Those transformations erase evidence needed by later judgments.

The Rust parser retains more source shape, but its semantic tree contains error
sentinels and recovery artifacts. It accepts Unicode identifiers through a
host Unicode property, accepts trailing commas inconsistently, classifies some
patterns by capitalization during parsing, rewrites compound assignments, and
parses assembly into an implementation-owned Yul tree. These choices are also
unsuitable as the normative resolver input.

The first draft of the M2c resolution ADR sketched a larger AST without fixing
its lexer, grammar, delimiter policies, or parser diagnostics. In particular,
it could not represent statement `if` without `else`, contract fallbacks with a
generic prefix, contract-local type aliases, value-free returns, or the exact
same-name constructor syntax used by the canonical standard library. It also
had no source-owned replacement for the opaque Surface v1 span label. Resolver
implementation must wait until these prerequisites are closed.

## Decision

### Proposal gate and frozen published boundaries

This ADR is a proposal. It authorizes no implementation while its status is
`Proposed`. Acceptance will authorize only the internal modules, judgments,
executors, proofs, and fixtures listed below. Publication still requires a
separate ADR.

Oracle v1 through v4, draft.1 through draft.4 language versions, existing
profiles, Surface v1, parse-result v1, Semantic Core v1 and v2, existing golden
streams, feature statuses, and capability bytes remain unchanged. In
particular, this decision does not extend Surface v1 and does not make a source
or resolution query available.

The new closed grammar is named
`solcore-multi-surface/m2c-v1`. `Multi` is a separate Lean namespace under
`Solcore.Surface`; it does not reinterpret any existing opaque source label or
span.

### Source ownership, spans, and locations

The parser accepts exactly one ADR-0014 `WorkspaceFile` at a time. It has no
filesystem access and does not parse every file in a workspace eagerly. A
later reachability traversal invokes the module-local parser only when a source
becomes reachable. Consequently an unreachable malformed source remains
unobserved.

Multi Surface defines a distinct span type:

```text
Multi.SourceSpan = {
  source    : SourceId,
  startByte : Nat,
  endByte   : Nat
}

Multi.SourceSpan.ValidFor(file, span) iff
  span.source = file.id and
  span.startByte <= span.endByte and
  span.endByte <= file.content.utf8ByteSize and
  file.content.isUtf8Boundary(span.startByte) and
  file.content.isUtf8Boundary(span.endByte)

Multi.Located alpha = {
  span    : Multi.SourceSpan,
  payload : alpha
}
```

All ranges are half-open UTF-8 byte ranges. `isUtf8Boundary(0)` and
`isUtf8Boundary(utf8ByteSize)` hold; an interior offset is a boundary exactly
when its byte is not a UTF-8 continuation byte. There is no line or column in
the normative identity. A presentation layer may derive them from the exact
source bytes. Empty spans are permitted only at a grammar boundary that
contains no token, such as an empty match-arm body or end of file.

The following conventions are normative.

- A token span is exactly its lexeme.
- An identifier or path-component span is exactly its spelling.
- A qualified-name span begins at its first component and ends at its last.
- A delimited syntax-node span includes both delimiters.
- A declaration or statement span begins at its first keyword, modifier, or
  name and includes its required terminator or closing brace.
- An expression, type, or pattern span includes explicit grouping delimiters.
- A module-root span is `[0, file.content.utf8ByteSize)` and therefore includes
  leading and trailing trivia.
- Leading and trailing trivia is otherwise excluded from syntax-node spans.
- A nonempty match-arm body spans its first through last statement. An empty
  arm body has the empty span at the end of its `=>` token.

Unless one of those rules states otherwise, a located production has the
minimal contiguous span from the first through last token consumed by that
production. Nested wrappers may consequently have equal spans when both are
real source productions; equality does not authorize inserting a wrapper for
an absent production.

Every module, top item, declaration, contract member, signature, generic
prefix, binder, selector, selector entry, constructor selector, type,
predicate, parameter, body, statement, loop item, match arm, pattern,
expression, literal, module reference, qualified name, identifier occurrence,
and semantic marker is `Located`. Semantic markers include module roots
`lib`, `std`, and `@`, wildcard `*`, fallback, contract constructor, modifiers,
and an assembly slice. Whitespace and comments remain located lexer evidence
but are not syntax-address nodes. Ordinary punctuation remains in the retained
token stream and need not be a separate address node.

The parser never invents a located node for an absent source construct. In
particular, absent `else`, absent return value, absent initializer, absent type
annotation, an omitted optional argument list, and absent generic context are
represented by `none`. Explicit grouping, an explicit empty call argument
list, an explicit empty leading-dot expression argument list, an explicit
empty tuple, and an explicitly written semicolon remain distinguishable.
Explicit empty named-type arguments, data-constructor field lists, and pattern
argument lists are outside this grammar rather than normalized to absence.

### Character repertoire and lexical grammar

The source is a Lean `String`, so its encoding is valid UTF-8. Multi Surface
uses Unicode only as source content and for byte accounting. Identifiers are
ASCII and are never normalized.

```text
asciiLetter      ::= "A" ... "Z" | "a" ... "z"
asciiDigit       ::= "0" ... "9"
identifierText   ::= asciiLetter (asciiLetter | asciiDigit | "_")*
decimalText      ::= asciiDigit+
hexText          ::= "0x" (asciiDigit | "a" ... "f" | "A" ... "F")+
whitespace       ::= U+0020 | U+0009 | U+000A | U+000D | U+000C
```

```text
identifierTextValid(text) =
  Workspace.pathSegmentTextValid(text) and
  text is not the spelling of any HardKeyword

Identifier = {
  text  : String,
  valid : identifierTextValid(text) = true
}
```

An `Identifier` is a refined `identifierText` that is not a hard keyword. A
module path component is ADR-0014 `PathSegment`; hard-keyword spellings are
allowed contextually in module-reference components. An external-library
component is ADR-0014 `ExternalLibraryName`. Unicode letters and digits are not
identifier characters. A non-ASCII scalar outside a comment, string, or
assembly slice is an invalid character, and its diagnostic span covers exactly
its UTF-8 bytes. Changing this repertoire requires a new grammar identifier
and an explicitly pinned Unicode version.

The hard keywords are exactly:

```text
contract import export hiding as let data forall class instance
if else for switch case default leave continue break assembly
match function fallback payable public constructor return lam type pragma
```

Their closed token payload is:

```text
HardKeyword =
  | contractKw | importKw | exportKw | hidingKw | asKw | letKw
  | dataKw | forallKw | classKw | instanceKw
  | ifKw | elseKw | forKw | switchKw | caseKw | defaultKw
  | leaveKw | continueKw | breakKw | assemblyKw | matchKw
  | functionKw | fallbackKw | payableKw | publicKw | constructorKw
  | returnKw | lamKw | typeKw | pragmaKw
```

Each constructor's spelling is its constructor name with the `Kw` suffix
removed. This map is bijective over the displayed spelling list.

`then` and `comptime` are contextual keywords. The lexer emits them as
identifiers, and the parser recognizes their exact lowercase spelling only in
the grammar positions below. `true`, `false`, `bool`, `word`, `Proxy`, `lib`,
and `std` are ordinary identifiers outside their explicitly contextual
positions. This keeps constructor, intrinsic, and shadowing decisions out of
the parser.

`then` is contextual only between the condition and then branch of a keyword
conditional. `comptime` is contextual as a leading parameter modifier, the
post-colon let modifier, a type prefix, or a comptime-pattern prefix under the
lookahead rule stated below. Those positions give the contextual spelling
priority over an ordinary identifier. Everywhere else both spellings remain
ordinary identifiers.

```text
ContextualKeyword = thenKw | comptimeKw
```

The four pragma names are dedicated complete lexemes:

```text
no-coverage-condition
no-patterson-condition
no-bounded-variable-condition
no-generic-instance-for
```

They produce a `pragmaName` token only when the following scalar is absent or
is neither an ASCII letter, an ASCII digit, `_`, nor `-`. This is the exact
pragma-name boundary. No other hyphenated identifier exists. For example,
`foo-bar` tokenizes as the identifier `foo`, `-`, and the identifier `bar`,
while `no-coverage-condition-extra` begins with the identifier `no` rather
than a pragma-name prefix.

The closed token payload is:

```text
TokenKind =
  | hardKeyword HardKeyword
  | identifier String
  | pragmaName PragmaKind
  | decimalLiteral (spelling : String) (digits : String)
  | hexadecimalLiteral (spelling : String) (digits : String)
  | stringLiteral (spelling : String) (decoded : String)
  | assemblyBlock AssemblySlice
  | symbol Symbol

Token = Located TokenKind

Symbol =
  | colonEqual | arrow | fatArrow
  | equalEqual | notEqual | greaterEqual | lessEqual
  | logicalAnd | logicalOr
  | plusEqual | minusEqual | caretEqual | ampEqual | pipeEqual
  | percentEqual
  | plus | minus | star | slash | percent | bang
  | less | greater | equal | pipe | amp | caret
  | at | question | dot | colon | semicolon | comma
  | leftParen | rightParen | leftBrace | rightBrace
  | leftBracket | rightBracket | underscore
```

The source spellings of the multi-character symbols, in the order shown, are
`:=`, `->`, `=>`, `==`, `!=`, `>=`, `<=`, `&&`, `||`, `+=`, `-=`, `^=`,
`&=`, `|=`, and `%=`. Single-character spellings are the corresponding
characters in `Symbol`.

Lexing uses maximal munch over these exact languages: at a cursor it chooses
the candidate with the greatest UTF-8 byte length. The four complete
pragma-name candidates therefore outrank their shorter initial identifier,
multi-character symbols outrank their prefixes, a valid hexadecimal literal
outranks its initial decimal zero, and comment openers outrank `/`. Equal-length
ties use this fixed order: comment, string, pragma name, ASCII identifier,
numeric literal, multi-character symbol, then single-character symbol. After
an ASCII identifier wins, its complete spelling is classified as a hard
keyword, contextual identifier, or ordinary identifier. Maximal munch does
not create a malformed-number token. Thus `0x` is decimal `0` followed by
identifier `x`, `0x1g` is hexadecimal `0x1` followed by identifier `g`, and
`123abc` is decimal `123` followed by identifier `abc`. The parser reports any
invalid adjacency.

For a decimal token, `spelling = digits` is the exact nonempty source slice.
For a hexadecimal token, `spelling = "0x" ++ digits`; `digits` is the exact
nonempty suffix and retains the source letter case. Leading zeroes are retained
in both forms. The corresponding `Literal` fields are copied exactly from the
token and are never recomputed from a numeric value.

The lexer retains comments in source order:

```text
CommentKind = line | block
Comment = Located CommentKind
```

`//` consumes through the byte before LF or through end of file. In CRLF, CR
belongs to the comment and LF terminates it. A bare CR does not terminate a
line comment. `/*` and `*/` delimit arbitrarily nested block comments. One
outer block comment yields one retained comment spanning every nested pair.
Whitespace is discarded. Comments inside an assembly block belong to the
opaque assembly slice and are not duplicated in the outer comment list.

A source string begins and ends with `"`. Its unescaped content may contain
any Unicode scalar except `"` and `\`. Raw LF, CR, and other scalar values are
accepted, matching the common behavior of the pinned parsers. The only escapes
are `\n`, `\t`, `\"`, and `\\`, decoded respectively to LF, tab, quote, and
backslash. The literal retains both its complete spelling and decoded value.
An unsupported escape fails at the backslash through the escaped scalar. A
backslash at end of file is `invalidStringEscape` with payload `none` and the
one-byte backslash span. The scanner reports the first invalid escape
immediately; `unterminatedString` applies only when every encountered escape is
valid and no closing quote occurs, and its span runs from the opening quote
through end of file. An unterminated ordinary nested block comment spans from
the outermost still-open `/*` through end of file. No literal is converted to a
number, word, boolean, or Core value.

### Opaque assembly scanning

Multi Surface does not parse Yul. When the normal lexer emits hard keyword
`assembly` and its next nontrivia byte is `{`, it invokes the assembly-block
scanner and emits one `assemblyBlock` token for the balanced block. If the next
nontrivia byte is not `{`, lexing continues normally so the parser can report
the missing block.

```text
AssemblySlicePayload = {
  openBrace  : SourceSpan,
  contents   : SourceSpan,
  closeBrace : SourceSpan
}
AssemblySlice = Located AssemblySlicePayload
```

The outer location covers both braces. `contents` is the exact interior byte
range and can be sliced from the owning `WorkspaceFile`; no normalized Yul text
is stored. The enclosing `assemblyBlock` token has exactly the same span as the
slice, and the assembly statement reuses that exact slice value. The scanner
starts at depth one, increments on `{`, decrements on `}`, and stops at the
first `}` returning depth to zero. Braces are ignored inside these scanner
states:

- a `//` comment through LF or end of file;
- an arbitrarily nested `/* ... */` comment; and
- a double-quoted string, where a backslash consumes the following Unicode
  scalar solely for delimiter scanning.

The assembly scanner does not interpret or validate escapes, identifiers,
operators, literals, or Yul grammar. That work belongs to a later assembly
layer. At end of file it reports an open string first, otherwise the outermost
still-open block-comment state, otherwise the assembly block. Each span runs
from that state's unmatched opening delimiter through end of file. This design
parses the canonical standard library without importing either implementation's Yul AST
and correctly ignores braces in assembly strings and comments.

### Closed source-preserving AST

The following pseudocode is the exact Lean-level algebra modulo namespace
qualification, Lean's `«...»` escaping for a displayed constructor that is a
keyword, and the mechanical use of `Box` where Lean's positivity checker
requires it. Every sum constructor has the direct named fields displayed; no
anonymous variant-payload record is implicit. `NonemptyList alpha` is a
structure with `head : alpha` and `tail : List alpha`; it is data, not a proof
over an otherwise empty list.

```text
IdentifierOccurrence = Located Identifier
PathComponent         = Located PathSegment

QualifiedNamePayload = {
  components : NonemptyList IdentifierOccurrence
}
QualifiedName = Located QualifiedNamePayload

SyntaxMarker =
  | libraryRoot | standardRoot | externalSigil | wildcard
  | fallbackName | contractConstructorName
  | publicModifier | payableModifier | comptimeModifier | defaultModifier

Marker = Located SyntaxMarker
```

Module references retain their written root and every component:

```text
ModuleReferencePayload =
  | relative
      (components : NonemptyList PathComponent)
  | libraryRoot
      (marker : Marker)
      (tail : NonemptyList PathComponent)
  | standard
      (marker : Marker)
      (tail : List PathComponent)
  | external
      (at : Marker)
      (library : Located ExternalLibraryName)
      (tail : NonemptyList PathComponent)

ModuleReference = Located ModuleReferencePayload

ModuleReferenceShape =
  | relative (components : NonemptyList PathSegment)
  | libraryRoot (tail : NonemptyList PathSegment)
  | standard (tail : List PathSegment)
  | external
      (library : ExternalLibraryName)
      (tail : NonemptyList PathSegment)
```

`ModuleReference.eraseLocations` produces `ModuleReferenceShape` by preserving
the payload constructor and ordered component texts while deleting every
`Located` wrapper and the constructor-determined marker. This value exists only
for structural equality such as duplicate local `allFrom` entries. It is not
ADR-0016's occurrence-bearing `Structural.ModuleReferenceSite`.

An empty `standard.tail` is bare `std`; a one-element tail containing `std` is
the distinct spelling `std.std`. Bare `lib` is `relative [lib]`. `lib.a` is
`libraryRoot lib [a]`. External syntax always contains a library name and at
least one module component.

Imports and exports retain raw finite lists until structural validation:

```text
ImportSelectorEntryPayload =
  | wildcard (marker : Marker)
  | named
      (source : IdentifierOccurrence)
      (alias : Option IdentifierOccurrence)
ImportSelectorEntry = Located ImportSelectorEntryPayload

ImportSelectionPayload = {
  entries : List ImportSelectorEntry
}
ImportSelection = Located ImportSelectionPayload

HidingClausePayload = {
  names : List IdentifierOccurrence
}
HidingClause = Located HidingClausePayload

ImportMode =
  | module (alias : Option IdentifierOccurrence)
  | items
      (selection : ImportSelection)
      (hiding : Option HidingClause)

ImportDeclPayload = {
  moduleRef : ModuleReference,
  mode      : ImportMode
}
ImportDecl = Located ImportDeclPayload

ConstructorSelectionPayload =
  | all (marker : Marker)
  | named (constructors : NonemptyList IdentifierOccurrence)
ConstructorSelection = Located ConstructorSelectionPayload

ExportItemPayload = {
  name         : IdentifierOccurrence,
  constructors : Option ConstructorSelection
}
ExportItem = Located ExportItemPayload

ExportEntryPayload =
  | wildcard (marker : Marker)
  | item (item : ExportItem)
  | allFrom (moduleRef : ModuleReference) (marker : Marker)
ExportEntry = Located ExportEntryPayload

LocalExportListPayload = { entries : List ExportEntry }
LocalExportList = Located LocalExportListPayload

RemoteExportEntryPayload =
  | wildcard (marker : Marker)
  | item (item : ExportItem)
RemoteExportEntry = Located RemoteExportEntryPayload

RemoteExportSelectionPayload =
  | dotWildcard (marker : Marker)
  | braced (entries : List RemoteExportEntry)
RemoteExportSelection = Located RemoteExportSelectionPayload

ExportMode =
  | local (selection : LocalExportList)
  | module
      (moduleRef : ModuleReference)
      (alias : Option IdentifierOccurrence)
  | from
      (moduleRef : ModuleReference)
      (selection : RemoteExportSelection)

ExportDecl = Located ExportMode
```

The generic and declaration payloads are:

```text
ForallBinderPayload =
  | bare (binder : IdentifierOccurrence)
  | bounded
      (binder : IdentifierOccurrence)
      (className : QualifiedName)
      (arguments : Option (NonemptyList TypeExpr))
ForallBinder = Located ForallBinderPayload

ForallClausePayload = {
  binders : NonemptyList ForallBinder
}
ForallClause = Located ForallClausePayload

PredicatePayload = {
  main       : TypeExpr,
  className  : QualifiedName,
  parameters : Option (NonemptyList TypeExpr)
}
Predicate = Located PredicatePayload

GenericPrefixPayload = {
  forallClause : ForallClause,
  context      : Option (NonemptyList Predicate)
}
GenericPrefix = Located GenericPrefixPayload

ParameterPayload = {
  comptime : Option Marker,
  name     : IdentifierOccurrence,
  type     : Option TypeExpr
}
Parameter = Located ParameterPayload

FunctionSignaturePayload = {
  genericPrefix : Option GenericPrefix,
  public        : Option Marker,
  payable       : Option Marker,
  name          : IdentifierOccurrence,
  parameters    : List Parameter,
  returnType    : Option TypeExpr
}
FunctionSignature = Located FunctionSignaturePayload

ClassMethodDeclPayload = {
  signature  : FunctionSignature,
  terminator : SourceSpan
}
ClassMethodDecl = Located ClassMethodDeclPayload

FunctionDeclPayload = {
  signature : FunctionSignature,
  body      : Body
}
FunctionDecl = Located FunctionDeclPayload

FallbackDeclPayload = {
  genericPrefix : Option GenericPrefix,
  public        : Option Marker,
  payable       : Option Marker,
  marker        : Marker,
  parameters    : List Parameter,
  returnType    : Option TypeExpr,
  body          : Body
}
FallbackDecl = Located FallbackDeclPayload

ContractConstructorDeclPayload = {
  public     : Option Marker,
  payable    : Option Marker,
  marker     : Marker,
  parameters : List Parameter,
  body       : Body
}
ContractConstructorDecl = Located ContractConstructorDeclPayload

DataConstructorPayload = {
  name   : IdentifierOccurrence,
  fields : Option (NonemptyList TypeExpr)
}
DataConstructor = Located DataConstructorPayload

DataDeclPayload = {
  name         : IdentifierOccurrence,
  parameters   : Option (NonemptyList IdentifierOccurrence),
  constructors : Option (NonemptyList DataConstructor)
}
DataDecl = Located DataDeclPayload

TypeAliasDeclPayload = {
  name       : IdentifierOccurrence,
  parameters : Option (NonemptyList IdentifierOccurrence),
  body       : TypeExpr
}
TypeAliasDecl = Located TypeAliasDeclPayload

ClassDeclPayload = {
  genericPrefix : Option GenericPrefix,
  main          : TypeExpr,
  className     : IdentifierOccurrence,
  parameters    : Option (NonemptyList TypeExpr),
  methods       : List ClassMethodDecl
}
ClassDecl = Located ClassDeclPayload

InstanceDeclPayload = {
  genericPrefix : Option GenericPrefix,
  default       : Option Marker,
  main          : TypeExpr,
  className     : QualifiedName,
  parameters    : Option (NonemptyList TypeExpr),
  methods       : List FunctionDecl
}
InstanceDecl = Located InstanceDeclPayload

PragmaKind =
  | noCoverageCondition
  | noPattersonCondition
  | noBoundedVariableCondition
  | noGenericInstanceFor

PragmaDeclPayload = {
  kind    : Located PragmaKind,
  targets : List IdentifierOccurrence
}
PragmaDecl = Located PragmaDeclPayload
```

`ClassDeclPayload.className` is the declaration's binding occurrence and is
therefore exactly one `IdentifierOccurrence`. It is not a class reference and
cannot be qualified. `ForallBinderPayload.bounded.className`,
`PredicatePayload.className`, and `InstanceDeclPayload.className` are class
references and remain complete `QualifiedName` values.

There is no `enabled` pragma source form or AST constructor. An empty target
list disables the selected check globally for the first three kinds. The
`noGenericInstanceFor` kind requires at least one target during structural
validation. A nonempty list disables the check only for the written names.

Contracts retain all members in one source-ordered list:

```text
FieldDeclPayload = {
  name        : IdentifierOccurrence,
  type        : TypeExpr,
  initializer : Option Expression
}
FieldDecl = Located FieldDeclPayload

ContractMemberPayload =
  | dataDecl (declaration : DataDecl)
  | typeAlias (declaration : TypeAliasDecl)
  | field (declaration : FieldDecl)
  | function (declaration : FunctionDecl)
  | fallback (declaration : FallbackDecl)
  | constructor (declaration : ContractConstructorDecl)
ContractMember = Located ContractMemberPayload

ContractDeclPayload = {
  name       : IdentifierOccurrence,
  parameters : Option (NonemptyList IdentifierOccurrence),
  members    : List ContractMember
}
ContractDecl = Located ContractDeclPayload

TopItemPayload =
  | importDecl (declaration : ImportDecl)
  | exportDecl (declaration : ExportDecl)
  | pragmaDecl (declaration : PragmaDecl)
  | dataDecl (declaration : DataDecl)
  | typeAliasDecl (declaration : TypeAliasDecl)
  | classDecl (declaration : ClassDecl)
  | instanceDecl (declaration : InstanceDecl)
  | contractDecl (declaration : ContractDecl)
  | functionDecl (declaration : FunctionDecl)
TopItem = Located TopItemPayload

ParsedModuleV1Payload = {
  source : SourceId,
  items  : List TopItem
}
ParsedModuleV1 = Located ParsedModuleV1Payload
```

The expression, type, pattern, and statement sums are also closed:

```text
LiteralPayload =
  | decimal (spelling : String) (digits : String)
  | hexadecimal (spelling : String) (digits : String)
  | string (spelling : String) (decoded : String)
Literal = Located LiteralPayload

TypeExprPayload =
  | named
      (name : QualifiedName)
      (arguments : Option (NonemptyList TypeExpr))
  | proxy (marker : Located Unit) (inner : TypeExpr)
  | function (domain : TypeExpr) (codomain : TypeExpr)
  | tuple (elements : List TypeExpr)
  | group (inner : TypeExpr)
  | comptime (marker : Marker) (inner : TypeExpr)
TypeExpr = Located TypeExprPayload

PrefixOperator = logicalNot
InfixOperator =
  | multiply | divide | modulo | add | subtract
  | bitAnd | bitXor | bitOr
  | less | greater | lessEqual | greaterEqual | equal | notEqual
  | logicalAnd | logicalOr
AssignmentOperator =
  | equal | addEqual | subtractEqual | bitXorEqual
  | bitAndEqual | bitOrEqual | moduloEqual

ExpressionPayload =
  | name (name : IdentifierOccurrence)
  | call (callee : Expression) (arguments : List Expression)
  | select (receiver : Expression) (field : IdentifierOccurrence)
  | dotConstructor
      (marker : Located Unit)
      (name : IdentifierOccurrence)
      (arguments : Option (List Expression))
  | proxy (marker : Located Unit) (type : TypeExpr)
  | literal (literal : Literal)
  | lambda
      (parameters : List Parameter)
      (returnType : Option TypeExpr)
      (body : Body)
  | annotation (expression : Expression) (type : TypeExpr)
  | keywordConditional
      (condition : Expression)
      (thenBranch : Expression)
      (elseBranch : Expression)
  | ternaryConditional
      (condition : Expression)
      (thenBranch : Expression)
      (elseBranch : Expression)
  | index (receiver : Expression) (index : Expression)
  | prefix (operator : Located PrefixOperator) (operand : Expression)
  | infix
      (operator : Located InfixOperator)
      (left : Expression)
      (right : Expression)
  | tuple (elements : List Expression)
  | group (inner : Expression)
Expression = Located ExpressionPayload

PatternPayload =
  | named
      (name : QualifiedName)
      (arguments : Option (NonemptyList Pattern))
  | dotConstructor
      (marker : Located Unit)
      (name : IdentifierOccurrence)
      (arguments : Option (NonemptyList Pattern))
  | wildcard (marker : Marker)
  | literal (literal : Literal)
  | comptime (marker : Marker) (expression : Expression)
  | tuple (elements : List Pattern)
  | group (inner : Pattern)
Pattern = Located PatternPayload

BodyOrigin =
  | braced (openBrace : SourceSpan) (closeBrace : SourceSpan)
  | matchArm (fatArrow : SourceSpan)
BodyPayload = {
  origin     : BodyOrigin,
  statements : List Statement
}
Body = Located BodyPayload

LetBindingPayload = {
  comptime   : Option Marker,
  name       : IdentifierOccurrence,
  type       : Option TypeExpr,
  initializer : Option Expression
}
LetBinding = Located LetBindingPayload

ForInitItemPayload =
  | letBinding (binding : LetBinding)
  | assignment
      (operator : Located AssignmentOperator)
      (left : Expression)
      (right : Expression)
  | expression (expression : Expression)
ForInitItem = Located ForInitItemPayload

ForPostItemPayload =
  | assignment
      (operator : Located AssignmentOperator)
      (left : Expression)
      (right : Expression)
  | expression (expression : Expression)
ForPostItem = Located ForPostItemPayload

MatchArmPayload = {
  patterns : NonemptyList Pattern,
  body     : Body
}
MatchArm = Located MatchArmPayload

StatementPayload =
  | assignment
      (operator : Located AssignmentOperator)
      (left : Expression)
      (right : Expression)
  | letBinding (binding : LetBinding)
  | block (body : Body)
  | expression
      (expression : Expression)
      (terminator : Option SourceSpan)
  | return
      (value : Option Expression)
      (terminator : SourceSpan)
  | match
      (scrutinees : NonemptyList Expression)
      (arms : NonemptyList MatchArm)
      (terminator : Option SourceSpan)
  | assembly (slice : AssemblySlice)
  | ifThenElse
      (condition : Expression)
      (thenBody : Body)
      (elseBody : Option Body)
  | forLoop
      (initializers : List ForInitItem)
      (condition : Expression)
      (post : List ForPostItem)
      (body : Body)
  | break (terminator : SourceSpan)
  | continue (terminator : SourceSpan)
Statement = Located StatementPayload
```

`TypeExpr`, `Predicate`, `Parameter`, `Expression`, `Pattern`, `Body`, loop
items, match arms, and `Statement` are one mutually recursive Lean family where
required. Reordering declarations or inserting mechanical `Box` fields does
not introduce an addressable syntax node. There is no generic variant wrapper
between a sum constructor and the direct named fields shown above.

`TypeExpr.function` has one domain and one codomain. A multi-value-looking
domain is one tuple type. Arrow syntax is right-associative. A one-element
parenthesized type, expression, or pattern is `group`; it is not discarded. An
empty parenthesized form is `tuple []`; two or more elements are `tuple` in
source order. No tuple is rewritten to `pair`.

Calls apply to an arbitrary expression. `f(x)`, `x.f(y)`, `(f)(x)`, and
`factory()(x)` are represented uniformly by nested `call` and `select` nodes.
Whether such a callee is callable is not a parser decision. A leading-dot
constructor stays distinct. An ordinary `T` or `T(args)` stays an ordinary
name or call, so same-name constructor shorthand is available to resolution
without the parser classifying it. Patterns likewise retain `named` syntax;
capitalization never decides binder versus constructor.

A statement `if` carries `Option Body` for its source `else`. A value-free
`return;` is accepted and represented by `none`. Compound assignment is not
rewritten into ordinary assignment plus an infix expression. A single final
expression is not rewritten into return. These choices preserve the exact
source tree for later judgments.

### Exact AST carrier and node measure

Resource proofs and ADR-0016 structural addresses use the same concrete AST
universe. The closed carrier-sort enumeration is:

```text
AstCarrierSort =
  | parsedModule | topItem | qualifiedName
  | identifier | pathComponent | externalLibraryName | syntaxMarker
  | unitMarker | moduleReference
  | importSelectorEntry | importSelection | hidingClause | importMode
  | importDecl | constructorSelection | exportItem | exportEntry
  | localExportList | remoteExportEntry | remoteExportSelection | exportMode
  | forallBinder | forallClause | predicate | genericPrefix | parameter
  | functionSignature | classMethodDecl | functionDecl | fallbackDecl
  | contractConstructorDecl | dataConstructor | dataDecl | typeAliasDecl
  | classDecl | instanceDecl | pragmaKind | pragmaDecl | fieldDecl
  | contractMember | contractDecl | literal | typeExpr | prefixOperator
  | infixOperator | assignmentOperator | expression | pattern | body
  | letBinding | forInitItem | forPostItem | matchArm | statement
  | assemblySlice

AstCarrier =
  | located (sort : AstCarrierSort)
  | payload (sort : AstCarrierSort)
```

ADR-0016 names the constructor-for-constructor identical structural sort sum
`Structural.SyntaxSort`; `AstCarrierSort` is the parser-side measure index, not
a second syntax universe or an address-visible wrapper.

An `AstCarrier.located sort` occurrence exists for each actual `Located`
wrapper of that sort in the AST above. An `AstCarrier.payload sort` occurrence
exists for its payload. `ImportMode` is the sole unlocated semantic carrier:
it contributes one `payload importMode` occurrence and no `located importMode`
occurrence. `ExportMode`, by contrast, is the payload of the located
`ExportDecl`. This enumeration includes located `Unit`, `PragmaKind`, operator,
marker, path, external-library-name, identifier, literal, and assembly-slice
leaves; each such leaf contributes its wrapper and its payload.

`astChildren` is the following exact executable relation, rather than an
implementation-selected traversal:

1. the only child of any `Located alpha` wrapper is its payload;
2. the children of a payload are exactly the recursive semantic fields shown
   for that payload in the closed AST blocks above, in displayed field order;
3. a present optional field contributes its value and an absent optional field
   contributes nothing;
4. a `List` or `NonemptyList` contributes its elements in written order, but
   the container, its `head`/`tail` representation, and option/list proofs do
   not contribute nodes;
5. a direct unlocated `ImportMode` field contributes that one mode carrier and
   then the mode's displayed semantic fields; and
6. `SourceSpan`, `SourceId`, `BodyOrigin`, strings, decoded values, digits,
   primitive enum payload data, `Box`, punctuation not represented by a marker,
   token/comment evidence, and list/option structure contribute no child.

Sum constructors have direct named fields, so there is no constructor-variant,
tuple, or other synthetic carrier between a payload and those fields. These
rules cover every displayed recursive field and no implicit field.

```text
astCarrierMeasure(node) =
  1 + sum(astCarrierMeasure(child) for child in astChildren(node))

Multi.astNodeMeasure(module : ParsedModuleV1) =
  astCarrierMeasure(the located parsedModule root of module)
```

This measure counts the located module root itself. It does not count virtual
scopes. ADR-0016 must use the same child relation and establish, without a
conversion traversal:

```text
Structural.nodeMeasure certified =
  Multi.astNodeMeasure certified.module
```

Thus an implementation cannot satisfy parser and structural resource bounds
with two different meanings of “AST node.”

### Complete syntactic grammar

The grammar below is complete. `list0(X)` means either empty or
`X ("," X)*`. `list1(X)` means `X ("," X)*`. No list accepts a trailing
comma. Square brackets in the metalanguage mean optional syntax; literal
brackets are quoted. `identifier` excludes hard keywords. `pathComponent`
accepts the spelling of either an identifier token or a hard-keyword token
when that spelling satisfies ADR-0014 `PathSegment`.

```text
module          ::= topItem* EOF

topItem         ::= importDecl
                  | exportDecl
                  | pragmaDecl
                  | dataDecl
                  | typeAliasDecl
                  | classDecl
                  | instanceDecl
                  | contractDecl
                  | functionDecl

moduleRef       ::= "@" pathComponent "." pathComponent
                      ("." pathComponent)*
                  | pathComponent ("." pathComponent)*

importDecl      ::= "import" moduleRef ";"
                  | "import" moduleRef "as" identifier ";"
                  | "import" moduleRef "." "{" list0(importEntry) "}"
                      [hidingClause] ";"
importEntry     ::= "*" | identifier ["as" identifier]
hidingClause    ::= "hiding" "{" list0(identifier) "}"

exportDecl      ::= "export" "{" list0(localExportEntry) "}" ";"
                  | "export" moduleRef ";"
                  | "export" moduleRef "as" identifier ";"
                  | "export" moduleRef "." "*" ";"
                  | "export" moduleRef "." "{" list0(remoteExportEntry)
                      "}" ";"
localExportEntry
                ::= "*" | exportItem | moduleRef "." "*"
remoteExportEntry
                ::= "*" | exportItem
exportItem      ::= identifier [constructorSelection]
constructorSelection
                ::= "(" "*" ")"
                  | "(" list1(identifier) ")"

pragmaDecl      ::= "pragma" "no-coverage-condition"
                      [list1(identifier)] ";"
                  | "pragma" "no-patterson-condition"
                      [list1(identifier)] ";"
                  | "pragma" "no-bounded-variable-condition"
                      [list1(identifier)] ";"
                  | "pragma" "no-generic-instance-for"
                      [list1(identifier)] ";"

genericPrefix   ::= forallClause [predicateList "=>"]
forallClause    ::= "forall" forallBinder (optionalComma forallBinder)* "."
forallBinder    ::= identifier
                  | identifier ":" qualifiedName
                      ["(" list1(type) ")"]
optionalComma   ::= [","]
predicateList   ::= list1(predicate)
predicate       ::= typeAtom ":" qualifiedName
                      ["(" list1(type) ")"]

functionSignature
                ::= [genericPrefix] ["public"] ["payable"]
                    "function" identifier "(" list0(parameter) ")"
                    ["->" type]
functionDecl    ::= functionSignature body
classMethod     ::= functionSignature ";"

dataDecl       ::= "data" identifier
                    ["(" list1(identifier) ")"]
                    ["=" dataConstructor ("|" dataConstructor)*] ";"
dataConstructor
                ::= identifier ["(" list1(type) ")"]

typeAliasDecl   ::= "type" identifier
                    ["(" list1(identifier) ")"] "=" type ";"

classDecl       ::= [genericPrefix] "class" typeAtom ":" identifier
                    ["(" list1(type) ")"]
                    "{" classMethod* "}"

instanceDecl    ::= [genericPrefix] ["default"] "instance"
                    typeAtom ":" qualifiedName
                    ["(" list1(type) ")"]
                    "{" instanceMethod* "}"
instanceMethod  ::= functionDecl

contractDecl    ::= "contract" identifier
                    ["(" list1(identifier) ")"]
                    "{" contractMember* "}"
contractMember  ::= dataDecl
                  | typeAliasDecl
                  | fieldDecl
                  | functionDecl
                  | fallbackDecl
                  | contractConstructorDecl
fieldDecl       ::= identifier ":" type ["=" expression] ";"
fallbackDecl    ::= [genericPrefix] ["public"] ["payable"]
                    "fallback" "(" list0(parameter) ")"
                    ["->" type] body
contractConstructorDecl
                ::= ["public"] ["payable"] "constructor"
                    "(" list0(parameter) ")" body

parameter       ::= ["comptime"] identifier [":" type]
body            ::= "{" statement* "}"

type            ::= "comptime" type
                  | typeAtom ["->" type]
typeAtom        ::= "@" typeAtom
                  | qualifiedName ["(" list1(type) ")"]
                  | "(" ")"
                  | "(" type ")"
                  | "(" type "," type ("," type)* ")"
qualifiedName   ::= identifier ("." identifier)*

statement       ::= letStatement
                  | returnStatement
                  | matchStatement
                  | ifStatement
                  | forStatement
                  | assemblyStatement
                  | blockStatement
                  | breakStatement
                  | continueStatement
                  | assignmentStatement
                  | expressionStatement

letStatement    ::= letBinding ";"
letBinding      ::= "let" identifier
                    [":" ["comptime"] type]
                    ["=" expression]
returnStatement ::= "return" [expression] ";"
blockStatement  ::= body
breakStatement  ::= "break" ";"
continueStatement
                ::= "continue" ";"
assemblyStatement
                ::= "assembly" assemblyBlock

ifStatement     ::= "if" "(" expression ")" body ["else" body]

forStatement    ::= "for" "(" list0(forInitItem) ";" expression ";"
                    list0(forPostItem) ")" body
forInitItem     ::= letBinding
                  | expression assignmentOperator expression
                  | expression
forPostItem     ::= expression assignmentOperator expression
                  | expression

matchStatement  ::= "match" list1(expression)
                    "{" matchArm+ "}" [";"]
matchArm        ::= "|" list1(pattern) "=>" armStatement*
armStatement    ::= statement

assignmentStatement
                ::= expression assignmentOperator expression ";"
assignmentOperator
                ::= "=" | "+=" | "-=" | "^=" | "&=" | "|=" | "%="

expressionStatement
                ::= expression ";"
                  | terminalExpression
terminalExpression
                ::= expression
```

After parsing the component sequence, the parser constructs the module-reference
variant by this exhaustive rule:

1. a leading `@` constructs `external`; the component immediately after `@`
   is the located external-library name and the remaining nonempty components
   are its module tail;
2. otherwise, first component `std` constructs `standard`, stores that exact
   component as the standard marker, and stores every remaining component as
   the possibly empty tail;
3. otherwise, first component `lib` with at least one following component
   constructs `libraryRoot`, stores `lib` as the marker, and stores the
   nonempty remainder as its tail; and
4. every other sequence, including bare `lib`, constructs `relative` with all
   written components.

Thus `std`, `std.std`, `lib`, and `lib.a` have four distinct exact AST shapes.
This is syntactic classification only; it performs no workspace lookup.

`predicateList` has no outer-parenthesis alternative: the grammar accepts a
bare comma-separated context only. Parentheses may instead group the `main`
type of one predicate. Predicate, class, and instance main heads use
`typeAtom`, so an arrow or comptime full type must be explicitly grouped to
occupy one head. Class references in bounded binders, predicates, and instances
use `qualifiedName`; the class-declaration binder after its colon uses exactly
one `identifier`.

After the colon of a let binding, an immediately following identifier spelled
`comptime` is always the let modifier and is stored in
`LetBindingPayload.comptime`; parsing of the following type begins after it.
This priority removes the otherwise possible parse as a
`TypeExprPayload.comptime` node. A general comptime type can still be written
there with explicit grouping, as in `let x : (comptime T);`.

An unterminated expression statement is accepted only as the final statement
before the closing `}` of a braced body or before the next arm/closing `}` of a
match. This admits the written final-expression form used by the canonical
sources while making statement boundaries deterministic. Assignments always
require `;`. A match may have one optional trailing `;`; other structured
statements do not consume one.

The parser recognizes a statement `if` only for the complete prefix
`if ( expression ) {`. Otherwise `if` begins the keyword conditional
expression below. This finite chart guard does not construct or discard nodes.
Within a match, a `|` followed by a complete `list1(pattern) =>` at a statement
boundary begins the next arm; otherwise it is the bitwise-or operator. The
declarative judgment, `Chart.G`, and the fast executor use the same guard
predicate, and its uniqueness is proved.

Pattern grammar is:

```text
pattern         ::= "_"
                  | literal
                  | "." identifier ["(" list1(pattern) ")"]
                  | "comptime" expression
                  | qualifiedName ["(" list1(pattern) ")"]
                  | "(" ")"
                  | "(" pattern ")"
                  | "(" pattern "," pattern ("," pattern)* ")"
```

`comptime` is treated as the contextual pattern marker only when a following
expression and a pattern boundary can be parsed. Otherwise it is an ordinary
one-segment qualified name. `T()` and `.T()` are not pattern forms; a nullary
constructor pattern is written `T` or `.T` and is classified later.

Expression precedence, from strongest to weakest, is postfix, prefix `!`,
multiplicative, additive, bitwise-and, bitwise-xor, bitwise-or, relational,
equality, logical-and, logical-or, conditional, then annotation.

```text
expression      ::= annotation
annotation      ::= conditional [":" type]

conditional     ::= "if" conditional "then" conditional
                      "else" conditional
                  | logicalOr ["?" conditional ":" conditional]

logicalOr       ::= logicalAnd ("||" logicalAnd)*
logicalAnd      ::= equality ("&&" equality)*
equality        ::= relational [("==" | "!=") relational]
relational      ::= bitOr [("<" | ">" | "<=" | ">=") bitOr]
bitOr           ::= bitXor ("|" bitXor)*
bitXor          ::= bitAnd ("^" bitAnd)*
bitAnd          ::= additive ("&" additive)*
additive        ::= multiplicative (("+" | "-") multiplicative)*
multiplicative  ::= prefix (("*" | "/" | "%") prefix)*
prefix          ::= "!" prefix | postfix
postfix         ::= atom postfixPart*
postfixPart     ::= "(" list0(expression) ")"
                  | "." identifier
                  | "[" expression "]"

atom            ::= literal
                  | identifier
                  | "." identifier ["(" list0(expression) ")"]
                  | "@" typeAtom
                  | lambda
                  | "(" ")"
                  | "(" expression ")"
                  | "(" expression "," expression
                      ("," expression)* ")"

lambda          ::= "lam" "(" list0(parameter) ")"
                    ["->" type] body
literal         ::= decimalLiteral | hexadecimalLiteral | stringLiteral
```

Postfix, multiplicative, additive, bitwise, and logical operators associate to
the left. Conditional forms and arrow types associate to the right. Equality
and relational operators are non-associative; a second operator at the same
non-associative level receives the dedicated diagnostic below rather than a
generic unexpected-token diagnostic. There is no unary `+` or `-`.

The optional argument list immediately following a leading-dot atom belongs
greedily to that `dotConstructor` node. Thus `.T()` has
`arguments = some []`, `.T(x)(y)` is a call whose callee is the argument-bearing
`.T(x)` node, and `.T` has `arguments = none`. This priority removes the only
overlap between that atom production and `postfixPart`.

Annotation is allowed once at the weakest precedence. A conditional operand
therefore needs explicit grouping to contain an annotation. A keyword or
ternary conditional needs grouping before a postfix operation. Explicit
grouping is always retained.

### Normative finite production chart and AST reduction

The EBNF above is serialized as one checked `Multi.Grammar.m2cV1` constant.
Line wrapping is not significant; rule and alternative order is the displayed
order. Its closed source-rule enumeration is:

```text
GrammarRuleId =
  | module | topItem | moduleRef | importDecl | importEntry | hidingClause
  | exportDecl | localExportEntry | remoteExportEntry | exportItem
  | constructorSelection | pragmaDecl | genericPrefix | forallClause
  | forallBinder | optionalComma | predicateList | predicate
  | functionSignature | functionDecl | classMethod | dataDecl
  | dataConstructor | typeAliasDecl | classDecl | instanceDecl
  | instanceMethod | contractDecl | contractMember | fieldDecl
  | fallbackDecl | contractConstructorDecl | parameter | body | type
  | typeAtom | qualifiedName | statement | letStatement | letBinding
  | returnStatement | blockStatement | breakStatement | continueStatement
  | assemblyStatement | ifStatement | forStatement | forInitItem
  | forPostItem | matchStatement | matchArm | armStatement
  | assignmentStatement | assignmentOperator | expressionStatement
  | terminalExpression | pattern | expression | annotation | conditional
  | logicalOr | logicalAnd | equality | relational | bitOr | bitXor
  | bitAnd | additive | multiplicative | prefix | postfix | postfixPart
  | atom | lambda | literal
```

Every rule right-hand side is a finite `EbnfExpr` tree. A `GrammarSite` is a
rule ID plus the finite child-index path to one node of that exact tree. It is
a subtype whose path-validity proof is checked against `m2cV1`, not an open
string or natural-number namespace. At each nesting level, adjacent terms form
one variadic sequence and displayed `|` branches form one variadic choice;
neither is encoded as an implementation-selected binary association. Unquoted
parentheses create one metalanguage-group node, while quoted parentheses are
terminals. The mechanical expansion below is
normative. `Aux(s)` is a fresh auxiliary nonterminal for site `s`, `Tail(s)` is
the one list-tail auxiliary, and `s.i` is the `i`th child site.

| EBNF node at site `s` | Expanded BNF productions and stable `ProductionId` | Stable `ActionId` |
| --- | --- | --- |
| rule root `R ::= e` | `P.root[R] : R -> Aux(R.root)` | `A.root[R]` |
| terminal or nonterminal atom `x` | `P.atom[s] : Aux(s) -> x` | `A.atom[s]` |
| sequence `e0 ... ek` | `P.seq[s] : Aux(s) -> Aux(s.0) ... Aux(s.k)` | `A.seq[s]` |
| metalanguage grouping `(e)` | `P.group[s] : Aux(s) -> Aux(s.0)` | `A.group[s]` |
| choice `e0 \| ... \| ek` | one `P.choice[s,i] : Aux(s) -> Aux(s.i)` for each displayed branch `i` | `A.choice[s,i]` |
| optional `[e]` | `P.opt[s,none] : Aux(s) -> epsilon`; `P.opt[s,some] : Aux(s) -> Aux(s.0)` | `A.opt[s,none]`; `A.opt[s,some]` |
| repetition `e*` | `P.star[s,nil] : Aux(s) -> epsilon`; `P.star[s,cons] : Aux(s) -> Aux(s.0) Aux(s)` | `A.star[s,nil]`; `A.star[s,cons]` |
| repetition `e+` | `P.plus[s,one] : Aux(s) -> Aux(s.0)`; `P.plus[s,cons] : Aux(s) -> Aux(s.0) Aux(s)` | `A.plus[s,one]`; `A.plus[s,cons]` |
| `list0(e)` | `P.list0[s,nil] : Aux(s) -> epsilon`; `P.list0[s,cons] : Aux(s) -> Aux(s.0) Tail(s)` | `A.list0[s,nil]`; `A.list0[s,cons]` |
| `list1(e)` | `P.list1[s] : Aux(s) -> Aux(s.0) Tail(s)` | `A.list1[s]` |
| list tail | `P.tail[s,nil] : Tail(s) -> epsilon`; `P.tail[s,cons] : Tail(s) -> "," Aux(s.0) Tail(s)` | `A.tail[s,nil]`; `A.tail[s,cons]` |

The Lean-level identifier algebra is exactly:

```text
OptionalBranch = none | some
NilConsBranch = nil | cons
OneConsBranch = one | cons

ProductionId =
  | root   GrammarRuleId
  | atom   AtomSite
  | seq    SequenceSite
  | group  GroupSite
  | choice (site : ChoiceSite) (branch : Fin site.branchCount)
  | opt    OptionalSite OptionalBranch
  | star   StarSite NilConsBranch
  | plus   PlusSite OneConsBranch
  | list0  List0Site NilConsBranch
  | list1  List1Site
  | tail   ListSite NilConsBranch

ActionId = actionFor (production : ProductionId)
```

Each `...Site` is the finite subtype of `GrammarSite` having that exact EBNF
node kind; `ListSite` is the disjoint finite union of `List0Site` and
`List1Site`. The table's `P.*` and `A.*` spellings are the pretty names of these
constructors. Therefore there is neither an unbounded numeric ID nor an action
without one unique production. Ordering uses the displayed `ProductionId`
constructor order, then displayed `GrammarRuleId` order, then lexicographic
child-index path and displayed branch order. `ActionId` inherits that order.

`epsilon` is the empty right-hand side, not a token. The quoted `EOF` in the
module rule is an ordinary terminal class in this expansion. Expansion rejects
a star, plus, or list whose repeated element is nullable. All repetitions in
`m2cV1` pass that executable check, including
`(optionalComma forallBinder)*` because the complete repeated sequence always
consumes a binder. Therefore this table generates a finite `ExpandedGrammar`,
and equality and ordering of every `ProductionId`, dotted position, and
`ActionId` are decidable by their finite indices. No implementation may hand
translate the EBNF or renumber productions.

Each expanded production has exactly the action with the same table cell and
ID. Atom actions retain the terminal value and exact span or forward the
nonterminal value. Sequence and choice actions construct temporary typed
semantic tuples and tags; optional and repetition actions construct temporary
options and source-ordered lists. These temporary values are not AST carriers.
`A.root[R]` eliminates them. Its reduction is fixed as follows:

- pass-through precedence and dispatch rules return their one AST child
  unchanged and do not add a location wrapper;
- each displayed declaration, body, pattern, type, expression, statement,
  selector, binder, name, and module alternative constructs the same-named
  direct-field payload in the closed AST, with the exact span conventions
  stated above rather than an action-selected range;
- `moduleRef` applies the four-way `external`/`standard`/`libraryRoot`/
  `relative` classification rule already stated, after retaining all written
  components;
- `type` folds `->` to the right; the multiplicative through logical-or rules
  fold their repeated pairs to the left; equality and relational build at most
  one node; `postfix` folds parts to the left into `call`, `select`, and `index`;
- annotation and both conditional forms construct a node only when their
  explicit operator syntax is present; otherwise their pass-through action
  returns the child unchanged;
- parenthesized singleton alternatives construct `group`, empty parentheses
  construct `tuple []`, and comma alternatives construct one flat `tuple`;
- optional argument syntax maps absent delimiters to `none` and written
  delimiters to `some`, including `some []` only where the AST permits it;
- a braced body records both brace spans, a match-arm body records its fat-arrow
  span, and an absent production never causes a located AST node; and
- punctuation spans are retained only in the exact `SourceSpan`, located
  operator, located unit marker, semantic marker, body-origin, or terminator
  fields displayed in the AST.

The finite root-action chart is:

| Source rules | `A.root` reduction |
| --- | --- |
| `module`, `topItem` | Construct the module root at exact span `[0, file.content.utf8ByteSize)` and its source-ordered items; tag each top-item alternative with the identically ordered `TopItemPayload` constructor. |
| `qualifiedName`, `moduleRef` | Construct all located name/path components; fold qualified components without loss; then apply the exhaustive module-reference shape classifier. |
| `importEntry`, `hidingClause`, `importDecl` | Construct wildcard or named selector entries and their alias options; construct the raw hiding list; map the three import alternatives to `ImportMode.module none`, `ImportMode.module (some alias)`, or `ImportMode.items`. |
| `constructorSelection`, `exportItem`, `localExportEntry`, `remoteExportEntry`, `exportDecl` | Construct the displayed raw selector sums; map export alternatives in order to local, module-without-alias, module-with-alias, from-dot-wildcard, and from-braced `ExportMode` payloads. |
| `pragmaDecl` | Construct the corresponding located `PragmaKind` in displayed alternative order and retain the exact target list. |
| `forallBinder`, `forallClause`, `predicate`, `genericPrefix` | Construct bare/bounded binders, the nonempty binder list, predicate, and optional nonempty context without expanding a bounded binder into a predicate. |
| `parameter`, `functionSignature`, `functionDecl`, `classMethod`, `fallbackDecl`, `contractConstructorDecl` | Construct the exact callable payloads; retain every modifier marker and option; retain the class-method or statement terminator span. |
| `dataConstructor`, `dataDecl`, `typeAliasDecl`, `classDecl`, `instanceDecl`, `instanceMethod`, `fieldDecl`, `contractMember`, `contractDecl` | Construct the corresponding declaration payload; `classDecl` stores its one identifier binder, while `instanceDecl` stores its qualified class reference; `instanceMethod` forwards its `FunctionDecl`. |
| `typeAtom`, `type` | Construct proxy, named, tuple, group, comptime, and right-associated function types; pass through only when no source constructor is present. |
| `pattern` | Construct wildcard, literal, named/dot-constructor, comptime, tuple, or group in displayed alternative order, preserving absent versus nonempty argument lists. |
| `literal`, `atom`, `lambda` | Construct exact literal spelling/decoded data and atomic expression payloads; construct leading-dot argument presence, explicit tuple/group shapes, and lambda fields. |
| `postfixPart`, `postfix`, `prefix` | Represent a postfix part temporarily as call/select/index action data, fold it left over the callee, and construct each written prefix node. |
| `multiplicative` through `logicalOr`, `relational`, `equality` | Construct one located operator and infix node per written operator with the stated associativity; relational/equality accept at most one. |
| `conditional`, `annotation`, `expression` | Construct keyword or ternary conditional and annotation nodes when written; otherwise forward the exact child. |
| `letBinding`, `forInitItem`, `forPostItem`, `matchArm` | Construct the exact displayed payload, preserving item kind, operator, source order, and the match-arm body origin. |
| `letStatement`, `returnStatement`, `blockStatement`, `breakStatement`, `continueStatement`, `assemblyStatement`, `ifStatement`, `forStatement`, `matchStatement`, `assignmentStatement`, `expressionStatement` | Construct the corresponding `StatementPayload`, including all terminator, absent-value, absent-else, opaque-slice, and ordered-list fields. |
| `statement`, `armStatement`, `terminalExpression` | Forward the already constructed semantic child without adding a wrapper. |
| `body` | Construct a braced body with both brace spans; match-arm bodies are constructed by the `matchArm` action with an empty span at the fat-arrow end when they contain no statements. |
| `optionalComma`, `predicateList`, `assignmentOperator` | Forward the temporary optional separator, nonempty predicate list, or construct the exact located assignment-operator payload; separator punctuation is not an AST node. |

Every source rule occurs in exactly one row. Where a row says “in displayed
alternative order,” the finite choice tag produced by `A.choice[s,i]` selects
the same zero-based AST constructor or listed special case. This is a total
mapping, not a naming convention left for implementers.

Those clauses, the alternative order, and the direct-field AST are the complete
root-action table. In particular, there is no pretty-print/reparse action,
capitalization action, implicit return, synthetic empty body, or tuple-to-pair
action.

Some successful prefixes overlap before their delimiters are known. The
following closed guard table resolves them. A guard fact is computed from the
same expanded productions by span recognition; it does not invoke
`parseTokens`, resolution, or semantic typing. Lower numeric priority wins,
and an explicitly disabled alternative cannot enter the chart.

```text
PriorityGuardId =
  | G01_statementIf | G02_matchArmBoundary | G03_parameterComptime
  | G04_letComptime | G05_typeComptime | G06_patternComptime
  | G07_leadingDotArguments | G08_terminalExpression
  | G09_genericContext

ParseOverrideId = G10_repeatedNonAssociative
```

| `GuardId` | Enabled alternative and exact priority condition |
| --- | --- |
| `G01_statementIf` | At a statement boundary beginning with `if`, enable `ifStatement` and disable the expression-statement branch exactly when an `expression` can end at the matching `)` and the next token is `{`; otherwise disable `ifStatement`. |
| `G02_matchArmBoundary` | In a match-arm body at a statement boundary, stop the body before `\|` exactly when a nonempty pattern list followed by `=>` is span-recognizable there; otherwise the `\|` remains available to expression parsing. |
| `G03_parameterComptime` | At the beginning of a parameter, `comptime` is the located parameter modifier; the competing interpretation as the parameter name is disabled, even if the required following identifier is absent. |
| `G04_letComptime` | Immediately after the colon of a let binding, a token spelled `comptime` is the located let marker; the competing type-level contextual interpretation is disabled. |
| `G05_typeComptime` | At a type start, `comptime` is the located type-prefix marker; the competing one-component named type is disabled, even if the required following type is absent. |
| `G06_patternComptime` | At a pattern start, `comptime` is the pattern marker exactly when an expression can end at the next comma, `)`, or `=>` pattern boundary; otherwise it is reinterpreted as an ordinary identifier component. |
| `G07_leadingDotArguments` | Parentheses immediately following a leading-dot name are consumed by `dotConstructor.arguments`; the same parentheses are disabled as the first postfix call part. |
| `G08_terminalExpression` | The unterminated expression-statement alternative is enabled only when its greatest complete end cursor is immediately before the enclosing body `}`, the next match arm recognized by `G02_matchArmBoundary`, or the enclosing match `}`. |
| `G09_genericContext` | After a `forallClause`, take the context option exactly when a nonempty `predicateList` is followed by `=>`; otherwise take the absent option without consuming predicates. |

`guardOf : ProductionId -> List (PriorityGuardId × Polarity)` is total and is
nonempty exactly on these expanded choices: `G01_statementIf` guards the
`statement` paths to `ifStatement` and `expressionStatement`;
`G02_matchArmBoundary` guards the cons/nil choice of the match arm's
`armStatement*`; `G03_parameterComptime` guards the parameter's leading option;
`G04_letComptime` guards the post-colon let option; `G05_typeComptime` guards
the two `type` alternatives; `G06_patternComptime` guards the comptime and
qualified-name pattern alternatives; `G07_leadingDotArguments` guards
the leading-dot argument option and the competing first call `postfixPart`;
`G08_terminalExpression` guards the `terminalExpression`
expression-statement alternative; and `G09_genericContext` guards the
generic-prefix context option. `Polarity` selects the enabled or disabled side
stated in the table. Every other production has `guardOf = []`.

For `G01_statementIf`, “matching `)`” means the delimiter reached after a
complete grouped condition from that `(`; braces inside strings, comments, and
assembly tokens are never candidates. For `G02_matchArmBoundary`,
`G06_patternComptime`, `G08_terminalExpression`, and `G09_genericContext`, the
greatest complete end cursor is selected before applying the condition. These
facts are the least fixed point of the unguarded predict/scan/complete relation
restricted to the named subgrammar and delimiter boundary. The universe is
finite, so the guard computation is executable and cannot appeal recursively
to a parse answer. The table is exhaustive; no parser-combinator commit order
is part of m2c-v1.

The normative reference parser is `Multi.Chart.G`. For an input containing
`n` retained tokens, let `terminalStream` append one logical `EOF`, let
`T = n + 1`, and number its `T + 1` boundaries from zero through `T`.

```text
DottedItem = {
  production : ProductionId,
  dot        : Fin (production.rhs.length + 1),
  origin     : Fin (T + 1),
  current    : Fin (T + 1)
}

PackedEdgeKey =
  | scanned  (before after : DottedItem) (terminalCursor : Fin T)
  | completed
      (waiting finished after : DottedItem)
      (sharedCursor : Fin (T + 1))

Predict(item) =
  if item.next is nonterminal X, add every guarded-on X production
  with dot zero and origin = current = item.current

Scan(item) =
  if item.next is terminal k and terminalStream[item.current] matches k,
  add the same item with its dot advanced and current advanced by one

Complete(waiting, finished) =
  if waiting.next is finished.lhs and
     waiting.current = finished.origin and finished is complete,
  add waiting with its dot advanced and current = finished.current
```

`G` starts with `P.root[module]` at origin/current zero and computes the least
set closed under `Predict`, `Scan`, and `Complete`, retaining packed action
edges by stable `ActionId`. A packed-edge key exists only when its displayed
items satisfy the corresponding `Scan` or `Complete` equation, so it is a
finite subtype rather than an open trace object. The executable uses an
ordered finite worklist:
each item key is dequeued once, each compatible prediction, scan, and completion
key is attempted once, and duplicate insertion is ignored. It accepts exactly
when the completed module-root item spans boundary zero through `T`. Thus EOF
is consumed and successful prefix parses do not exist.

On acceptance, the packed root is reduced by the action table. The guard table,
non-null repetition check, precedence construction, and delimiter rules imply:

```text
uniqueRootReduction :
  completedRoot G tokens root1 ->
  completedRoot G tokens root2 ->
  root1 = root2
```

The statement quantifies over all packed derivations, not only the first
worklist path. `G` therefore never selects an AST by map iteration order. Its
result is the unique `ParsedModuleV1`, or the closed parse diagnostic specified
below.

### Structural acceptance

Parsing constructs the raw closed AST without recovery nodes. A separate pure
structural pass accepts it exactly when all cross-node source-shape invariants
hold. This separation gives invalid but fully parsed selectors and signatures
specific diagnostics without admitting them to resolution.

`Multi.StructurallyAccepts module` holds exactly when:

1. every import selection is nonempty;
2. a wildcard import entry is the only entry in its selection;
3. import source names and resulting local names are each unique within the
   declaration;
4. every written hiding clause is nonempty and contains unique names;
5. every local and braced remote export list is nonempty;
6. a wildcard export entry is the only entry in its list;
7. export item names are unique within each local or braced remote list, and
   span-erased `allFrom` `ModuleReferenceShape` values are unique within each
   local list;
8. named constructor selections contain unique constructor names;
9. each match arm has exactly as many patterns as its enclosing match has
   scrutinees;
10. `noGenericInstanceFor` has a nonempty target list and every pragma target
    list is duplicate-free;
11. `public` and `payable` are absent from top-level functions, class methods,
    and instance methods;
12. contract functions may use `public` and `payable` in that order;
13. fallback and contract-constructor declarations have no written `public`;
14. fallback has no parameters and its written return type is absent or the
    explicit unit tuple `()` after removal only of explicit `group` wrappers;
15. contract-constructor parameters and every parameter of an ordinary
    top-level, contract, class-method, or instance-method function are typed;
    and
16. `break` and `continue` occur under at least one enclosing `for` body.

Lambda parameters may omit types. Let bindings may omit both annotation and
initializer, as required by canonical opcode wrappers. Sequential let-binding
shadowing, declaration duplication, name classification, constructor arity,
callability, assignment-target validity, and type admissibility are not parser
structural properties; later phases decide them.

Loop depth starts at zero for every ordinary function, fallback, contract
constructor, and lambda body. It increases only while checking a `forLoop`
body. A lambda nested inside a loop therefore cannot use `break` or `continue`
to target the enclosing function's loop.

Removing explicit `group` wrappers in rule 14 is a predicate over the parsed
tree, not an AST rewrite. No accepted AST is normalized by the structural pass.

### Closed diagnostics

Diagnostics are structured values. English text is presentation only. There
is no unstructured message constructor.

```text
LexicalDiagnostic =
  | invalidCharacter SourceSpan Char
  | unterminatedBlockComment SourceSpan
  | unterminatedString SourceSpan
  | invalidStringEscape SourceSpan (Option Char)
  | unterminatedAssemblyString SourceSpan
  | unterminatedAssemblyComment SourceSpan
  | unterminatedAssemblyBlock SourceSpan

Expected =
  | hardKeyword HardKeyword
  | contextualKeyword ContextualKeyword
  | pragmaName PragmaKind
  | symbol Symbol
  | identifier
  | pathComponent
  | literal
  | assemblyBlock
  | endOfFile

Found = token TokenKind | endOfFile

ParseDiagnostic =
  | unexpected SourceSpan Found (NonemptyList Expected)
  | repeatedNonAssociative
      SourceSpan
      NonAssociativeLevel
      (Located InfixOperator)

NonAssociativeLevel = relational | equality
ControlKind = breakControl | continueControl

ModifierContext =
  | topLevelFunction | classMethod | instanceMethod
  | fallback | contractConstructor

ParameterContext =
  | topLevelFunction | contractFunction
  | classMethod | instanceMethod | contractConstructor

StructuralDiagnostic =
  | emptyImportSelection SourceSpan
  | mixedImportWildcard SourceSpan
  | duplicateImportSourceName SourceSpan Identifier
  | duplicateImportLocalName SourceSpan Identifier
  | emptyHidingClause SourceSpan
  | duplicateHiddenName SourceSpan Identifier
  | emptyLocalExportList SourceSpan
  | emptyRemoteExportList SourceSpan
  | mixedExportWildcard SourceSpan
  | duplicateExportName SourceSpan Identifier
  | duplicateExportModuleReference SourceSpan ModuleReferenceShape
  | duplicateExportConstructor SourceSpan Identifier
  | matchPatternArityMismatch SourceSpan Nat Nat
  | emptyGenericPragmaTargets SourceSpan
  | duplicatePragmaTarget SourceSpan Identifier
  | modifierNotAllowed SourceSpan ModifierContext SyntaxMarker
  | fallbackHasParameters SourceSpan Nat
  | fallbackHasNonUnitReturn SourceSpan
  | requiredParameterTypeMissing SourceSpan ParameterContext
  | controlOutsideLoop SourceSpan ControlKind

SurfaceDiagnostic =
  | lexical LexicalDiagnostic
  | parse ParseDiagnostic
  | structural StructuralDiagnostic
```

`ModifierContext` and `ParameterContext` are closed enumerations of the
declaration positions mentioned by the structural rules. Every constructor has
total `diagnosticSource`, `diagnosticSpan`, and `diagnosticCode` projections.
Codes are assigned in constructor order in three disjoint ranges: `MSL0001`
through `MSL0007`, `MSP0001` through `MSP0002`, and `MSS0001` through
`MSS0020`.

Lexing is fail-fast at the least byte cursor at which no lexical rule can
continue. A parse diagnostic instead comes from the complete finite chart, so
an earlier dead alternative cannot hide a later, more informative failure.
Let `Reach` be `G`'s guarded predict/scan/complete closure and define:

```text
greatestReachableCursor =
  max { item.current | item is in Reach }

frontier =
  predict/complete closure of all Reach items whose current equals
  greatestReachableCursor

ExpectedAtFrontier =
  union { expectedClass(terminal) |
          item is in frontier and item.next = terminal and
          the item's production remains enabled by every priority guard }
```

`greatestReachableCursor` exists because the start item is reachable. On parse
failure it is no later than the logical EOF cursor, and `ExpectedAtFrontier` is
nonempty; both facts are required theorems of the expanded grammar. The union
is set union over every reachable item, not the expectation of a preferred
derivation. It is sorted first by `Expected` constructor order and then by the
displayed order of any `HardKeyword`, `ContextualKeyword`, `PragmaKind`, or
`Symbol` payload, and is deduplicated.

Quoted hard and contextual words, pragma names, and symbols map to their
corresponding singleton `Expected` constructors; grammar terminals
`identifier`, `pathComponent`, `literal`, and `assemblyBlock` map to the four
category constructors; `EOF` maps to `endOfFile`. No nonterminal label,
disabled branch, recovery alternative, or presentation-only name is added.
This list is used identically by `ParseDiagnostic.Applies`, `Chart.G`, and the
proved-equal fast executor.

If the greatest cursor denotes a retained token, `unexpected` uses that token's
exact span and `Found.token`; at the logical EOF cursor it uses the empty span
at `file.content.utf8ByteSize` and `Found.endOfFile`. There is one override. If
the frontier contains a completed first relational or equality operation, the
found token is another operator from that same level, and no explicit group
boundary intervenes, `G10_repeatedNonAssociative` replaces `unexpected`. It
uses the exact span of that second operator and retains that operator as
payload. The override applies across different operators at the same level,
such as `<` followed by `>=`; grouping starts a new level. At such a cursor,
`repeatedNonAssociative` is the only applicable parse diagnostic and the union
`ExpectedAtFrontier` is not emitted.

Structural validation reports every applicable structural diagnostic. It
sorts and deduplicates by diagnostic code, source identity, primary start and
end byte, and remaining payload fields. Duplicate diagnostics identify the
later conflicting occurrence as the primary span and include the repeated
spelling as payload. These rules make the result independent of map or set
iteration order.

Primary spans and multiplicity are exact:

- an empty-list diagnostic uses its located selection, clause, or export-list
  span and occurs once for that container;
- a mixed-wildcard diagnostic uses the least wildcard-marker span in the
  offending list and occurs once for that list;
- a duplicate name, constructor, target, or module-reference diagnostic occurs
  once for every occurrence after the first equal span-erased key and uses that
  later occurrence's span;
- a match-arity diagnostic occurs once per mismatching arm and uses the arm
  span;
- an empty generic-pragma diagnostic uses the located pragma-kind span;
- a modifier diagnostic occurs once per invalid modifier and uses the marker
  span;
- a fallback-parameter diagnostic occurs once and uses the fallback marker
  span, while carrying the written parameter count;
- a fallback-return diagnostic uses the written return-type span;
- a missing-parameter-type diagnostic occurs once per parameter and uses its
  name span; and
- an out-of-loop control diagnostic occurs once per statement and uses the
  complete statement span.

For the duplicate-import constructors, the source-name diagnostic uses the
later `source` name span, while the local-name diagnostic uses the later alias
span when an alias is written and otherwise that entry's source-name span.
Duplicate hiding, export-item, constructor-selection, pragma-target, and
`allFrom` diagnostics respectively use the later hidden-name, export-item name,
constructor name, pragma target, and complete module-reference span. Wildcard
entries do not contribute a name key.

The public module parser uses first-failing-phase precedence:

1. one lexical diagnostic;
2. otherwise one parse diagnostic;
3. otherwise the canonical nonempty list of structural diagnostics; or
4. one certified parsed module.

For every diagnostic constructor, an independent `Applies` relation is an
if-and-only-if characterization of the exact condition above. No executor
failure, recursion budget, host exception, or recovery sentinel is exposed as
a source diagnostic.

### Independent judgments and pure executors

The specification separates syntax relations from execution.

```text
Multi.Lexes : WorkspaceFile -> List Token -> List Comment -> Prop
Multi.Parses : WorkspaceFile -> List Token -> ParsedModuleV1 -> Prop
Multi.StructurallyAccepts : ParsedModuleV1 -> Prop
Multi.LexicalDiagnostic.Applies : WorkspaceFile -> LexicalDiagnostic -> Prop
Multi.ParseDiagnostic.Applies : WorkspaceFile -> List Token ->
  ParseDiagnostic -> Prop
Multi.StructuralDiagnostic.Applies : ParsedModuleV1 ->
  StructuralDiagnostic -> Prop
```

`Lexes` is an inductive byte-partition judgment. It specifies maximal token
lexemes, retained trivia, UTF-8 cursor movement, nested comments, string
decoding, and the assembly scanner without mentioning the lexer function.
`Parses` is a declarative, full-token grammar judgment generated from the
stable production and action tables. Its derivations record production IDs,
guard premises, action IDs, and associativity, but do not contain an equation
to `Chart.G` or `parseTokens`. `StructurallyAccepts` is the conjunction of the
sixteen rules above and does not invoke the validator.

The raw executors import syntax and diagnostics but do not import their sibling
judgments:

```text
LexedModule = {
  source   : SourceId,
  tokens   : List Token,
  comments : List Comment
}

Multi.lexModule :
  WorkspaceFile -> Except LexicalDiagnostic LexedModule

Multi.Chart.G :
  WorkspaceFile -> LexedModule -> Except ParseDiagnostic ParsedModuleV1

Multi.parseTokens :
  WorkspaceFile -> LexedModule -> Except ParseDiagnostic ParsedModuleV1

Multi.validateStructure :
  ParsedModuleV1 -> Except (NonemptyList StructuralDiagnostic) Unit
```

`LexedModule.tokens` contains no EOF token. The parser uses one logical EOF
terminal at the boundary after the last token; this terminal is counted in `T`
below and scanning it reaches the final chart boundary.
Successful `lexModule file` sets `source = file.id`, orders tokens and comments
independently by increasing span, and every span is valid for `file`.

`Chart.G` is the executable finite-chart reference just specified.
`parseTokens` is a separate memoized deterministic executor. Neither imports
`Parses`; the property layer proves both correspondence and exact result
equality. This preserves an independently readable declarative judgment while
preventing the optimized executor from changing diagnostics or AST reduction.

Only the property layer imports both judgments and executors. It defines the
public certified result and facade:

```text
Multi.CertifiedParsedModule = {
  file       : WorkspaceFile,
  tokens     : List Token,
  comments   : List Comment,
  module     : ParsedModuleV1,
  lexes      : Multi.Lexes file tokens comments,
  parses     : Multi.Parses file tokens module,
  accepted   : Multi.StructurallyAccepts module,
  locations  : EveryLocationValid file module,
  corresponds : ExactTokenCorrespondence file tokens comments module
}

Multi.parseModule :
  WorkspaceFile ->
  Except (NonemptyList SurfaceDiagnostic) CertifiedParsedModule
```

There is intentionally no eager `ParsedClosedWorkspace` in this ADR.
ADR-0016 defines module-root structural keys over `CertifiedParsedModule`.
ADR-0017 may collect certified modules in a resolver-owned
`ParsedReachableWorkspace` after reachability discovers them.

`ExactTokenCorrespondence` is executable. It checks every located leaf against
the exact source slice, every container span against its grammar children and
delimiters, source ownership, token order, absence versus presence fields,
and complete token consumption. It does not compare only pretty-printed text.

### Termination and resource bounds

The public parser has no caller-selected fuel. Lexer loops advance a UTF-8 byte
cursor or pop a finite delimiter stack. Structural traversal decreases the
closed AST. Parser termination is not justified by a strict-token-suffix claim:
prediction and completion can revisit one cursor. Instead, `Chart.G` consumes
the finite set of previously unprocessed item and packed-edge keys, and the
fast executor consumes a finite memo/worklist key set. Duplicate keys never
re-enter either worklist.

The following executable bounds are fixed for m2c-v1:

```text
B = file.content.utf8ByteSize
T = LexedModule.tokens.length + 1              -- includes logical EOF
Q = T + 1                                      -- chart boundaries
P = Multi.Grammar.expanded.productionCount
D = sum (p.rhs.length + 1 for p in Multi.Grammar.expanded.productions)
FastMemoKeyKind =
  | rule GrammarRuleId | site GrammarSite
  | guard PriorityGuardId | action ActionId
F = card FastMemoKeyKind
  = card GrammarRuleId + card GrammarSite
    + card PriorityGuardId + card ActionId
N = Multi.astNodeMeasure parsedModule

lexBound(B) =
  16 * (B + 1)

chartGBound(T) =
  1 + (2 * D * P + 4 * D) * Q * Q
    + 4 * D * D * Q * Q * Q

parseBound(T) =
  1 + 32 * F * Q
    + 256 * F * Q * Q

structureBound(N) =
  32 * (N + 1) * (N + 1)
```

A lexer unit is one cursor-state transition or one delimiter-stack transition.
One `G` unit is one ordered-worklist dequeue, candidate prediction, candidate
scan, candidate completion pair, packed-edge insertion, action application, or
frontier-diagnostic candidate. The exact cubic polynomial covers the unguarded
guard-fact chart and guarded parse chart: their dequeues, predictions, and scans
use at most `(2 * D * P + 4 * D) * Q^2` units; completion pairs, packed edges,
reduction, and diagnostic collection use at most `4 * D^2 * Q^3` units; the
leading one covers initialization. These are bounds on the specified semantic
counter, not asymptotic placeholders.

`F` is exactly the displayed sum of the four finite enumerations; it is not a
tunable numeral. The optimized
`parseTokens` fills memo cells in lexicographic `(fast key kind, start boundary,
end boundary)` order, uses precedence climbing for expressions, and visits
each successful reduction edge once. Each kind/boundary pair has 32 fixed
initialization/finalization work slots and each memo cell has 256 fixed
recognition/guard/action slots; an inapplicable slot is a no-op and a slot is
never revisited. A non-no-op slot is one memo lookup or insertion, token
comparison, guard comparison, or AST action. This schedule is the executor's
termination argument and gives the displayed exact quadratic bound. Acceptance
requires both its own bound and extensional equality with `Chart.G` for success
ASTs and complete diagnostics:

```text
parseTokens_eq_chartG :
  Multi.parseTokens file lexed = Multi.Chart.G file lexed
```

A structural unit is one `astChildren` node visit, list comparison, or
diagnostic insertion. Thus `structureBound` uses exactly the AST node meaning
shared with ADR-0016, including leaf wrappers/payloads and the unlocated
`ImportMode`, while excluding lists, options, spans, and virtual scopes.

The implementation proves actual units at or below each bound and proves that
its internal exhausted state is unreachable at the public boundary. A later
publication profile may compare an independently specified demand metric with
a limit; it must not reinterpret internal exhaustion as language rejection.

### Required correspondence theorems

Acceptance of an implementation requires at least these public theorems, with
the final names adjusted only for Lean namespace syntax:

```text
sourceSpan_valid_iff
located_source_unique

decodeUtf8Strict_accepts_iff_valid
decodeUtf8Strict_roundTrip
canonicalStandard_utf8Strict
canonicalStandard_byteRoundTrip

lexer_progress
lexer_maximal_munch
lexer_sound
lexer_complete
Lexes.functional
lexical_diagnostic_sound
lexical_diagnostic_complete
lexBound_sufficient

assembly_slice_balanced
assembly_slice_ignores_string_braces
assembly_slice_ignores_comment_braces

ebnf_expansion_finite
ebnf_expansion_nonnullable_repetitions
production_action_id_bijective
chart_predict_scan_complete_closed
chart_guard_facts_functional
chart_greatest_cursor_exists
chart_expected_nonempty_on_failure
chart_expected_is_frontier_union
chart_repeated_nonassoc_overrides
chart_unique_root_reduction
chartG_sound
chartG_complete
chartG_diagnostic_sound
chartG_diagnostic_complete
chartGBound_sufficient

parser_consumes_all
parser_sound
parser_complete
Parses.functional
parse_diagnostic_sound
parse_diagnostic_complete
parseTokens_eq_chartG
parseBound_sufficient

structure_sound
structure_complete
structural_diagnostics_canonical
structureBound_sufficient
astNodeMeasure_eq_astCarrier_cardinality

all_locations_valid
all_locations_nested
module_source_exact
qualified_components_exact
module_reference_shape_exact
grouping_preserved
literal_spelling_exact
no_parser_normalization

parseModule_success_iff
parseModule_failure_iff
parseModule_deterministic
accepted_or_diagnosed
success_not_diagnosed
```

Completeness ranges over the entire grammar and every diagnostic constructor,
not only the canonical fixtures. Public theorem assumptions are limited to the
repository's accepted Lean foundations and are audited in the same way as the
existing semantic kernel.

### Canonical standard-library parse certificate

The six ADR-0007 files are a mandatory kernel-checked gate:

```text
std/ABIGeneric.solc
std/Generic.solc
std/StorageGeneric.solc
std/dispatch.solc
std/opcodes.solc
std/std.solc
```

Their exact ADR-0007 metadata is:

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `ABIGeneric.solc` | 5,540 | `b14f31abd374d65e194c7706183086082558ab2a60d230ec5b9e6f1b9c9b9ae2` |
| `Generic.solc` | 445 | `913a02e32829e0230e31db6512151c36e019f5630e3dbd0be9d033a9019194d7` |
| `StorageGeneric.solc` | 10,546 | `8d68601447f40a6e662de8b6cff06031998628339ca23ec917a970157c301a6a` |
| `dispatch.solc` | 11,249 | `b723ec9a0a76a6abf091d49a12467c6a4628b634c48d8c34e82e2c45d6e939f5` |
| `opcodes.solc` | 10,377 | `a6a08beed16ccdf722f65c60af835dcfd0eaec61f34f041082bbc0fca1e69bab` |
| `std.solc` | 72,958 | `e8ec755232347bbf4a130dcc05c7c5a3230c4d0cb0223445a2d82260d4474fec` |

There is one neutral owner for these bytes:

```text
Solcore/Standard/CanonicalData.lean

CanonicalFileId =
  | abiGeneric | generic | storageGeneric | dispatch | opcodes | std

CanonicalRawFile = {
  id                  : CanonicalFileId,
  logicalPathUtf8     : ByteArray,
  contentUtf8         : ByteArray,
  expectedByteCount   : Nat,
  expectedSha256Bytes : Vector UInt8 32
}

Solcore.Standard.canonicalRawFiles : Vector CanonicalRawFile 6
```

The vector is in the table order and contains literal raw bytes from the
Haskell pin, not host paths, escaped `String` approximations, or generated
premises. `expectedByteCount` and `expectedSha256Bytes` are metadata values;
their presence is not a theorem that the content has either value. This module
imports neither Surface nor resolution code. Both the parser fixture layer and
ADR-0017's verified standard-bundle layer must import these same constants;
neither may keep a second content copy. The repository's kernel-policy audit
treats `Solcore/Standard/CanonicalData.lean` as a root in its own right.

The upstream `std/` directory is the bundle root, not a logical path segment.
The six `logicalPathUtf8` values strictly decode to `ABIGeneric.solc`,
`Generic.solc`, `StorageGeneric.solc`, `dispatch.solc`, `opcodes.solc`, and
`std.solc` inside `LibraryId.standard`.

`Solcore/Surface/Multi/StandardFixtures.lean` supplies an independent strict
UTF-8 decoder and constructs `WorkspaceFile` values only after proving all of:

```text
decodeUtf8Strict(raw) = Except.ok text
String.toUTF8(text) = raw
raw.size = expectedByteCount
Workspace.pathValid(strictly decoded logicalPathUtf8)
```

All two-digit byte values and ranges in this subsection are hexadecimal with
the `0x` prefix omitted. Strict validity means the entire byte array has the
unique partition into exactly these sequences, where every unqualified
continuation range is `80` through `BF` inclusive:

```text
00..7F
C2..DF 80..BF
E0 A0..BF 80..BF
E1..EC 80..BF 80..BF
ED 80..9F 80..BF
EE..EF 80..BF 80..BF
F0 90..BF 80..BF 80..BF
F1..F3 80..BF 80..BF 80..BF
F4 80..8F 80..BF 80..BF
```

The decoder accepts if and only if that partition consumes every byte. It
decodes each sequence to its Unicode scalar and has no BOM, noncharacter,
normalization, or text-content exception.

The decoder rejects a stray continuation byte `[80]`, overlong slash
`[C0, AF]`, truncated three-byte input `[E2, 82]`, UTF-16 surrogate encoding
`[ED, A0, 80]`, and a scalar above U+10FFFF `[F4, 90, 80, 80]`. It accepts and
round-trips exact one-, two-, three-, and four-byte boundary fixtures, including
`[00]`, `[C2, 80]`, `[E0, A0, 80]`, and `[F4, 8F, BF, BF]`. No replacement
scalar, lossy host decoding, locale, or filesystem API is permitted.

The kernel proves a general successful-decode byte round trip and specializes
it to every canonical path and content constant:

```text
decodeUtf8Strict_roundTrip :
  decodeUtf8Strict raw = Except.ok text -> String.toUTF8 text = raw

canonicalStandard_utf8Strict :
  for every raw in Solcore.Standard.canonicalRawFiles,
  exists pathText contentText,
    decodeUtf8Strict raw.logicalPathUtf8 = Except.ok pathText and
    decodeUtf8Strict raw.contentUtf8 = Except.ok contentText

canonicalStandard_byteRoundTrip :
  every decoded canonical path and content re-encodes byte-for-byte
  to its corresponding raw constant

canonicalStandardFixtures : Vector WorkspaceFile 6 =
  the strictly decoded files, with LibraryId.standard source identities
```

This is parser evidence, not a digest proof. ADR-0017 verifies byte counts and
SHA-256 over `Solcore.Standard.canonicalRawFiles` and compares any supplied
standard bundle to those same raw constants before reusing a parse result.

The parser implementation must prove in the ordinary Lean kernel:

```text
canonicalStandard_parses :
  for every file in canonicalStandardFixtures,
  exists certified,
    Multi.parseModule file = Except.ok certified

canonicalStandard_structurally_accepts :
  for every certified result above,
  Multi.StructurallyAccepts certified.module
```

These are theorems, not only tests. `native_decide`, a host parser, generated
success booleans treated as premises, and trusted digest constants are not
permitted.

To keep roughly 110 KiB of source practical for kernel checking, the
implementation uses checked certificates split at lexer partitions and
top-item boundaries. A certificate contains tokens, source spans, grammar
`ProductionId`/`ActionId` tags, and subtree boundaries. A pure checker
recomputes every source slice and produces `Lexes` and `Parses` derivations.
Certificates may be
generated offline, but malformed certificates cannot prove a theorem. Ordinary
kernel reduction checks each chunk; file-level theorems compose the chunks,
and parser completeness plus functionality connects the checked derivation to
`parseModule`. This is a proof-performance technique, not a second parser or a
semantic oracle.

The fixture gate specifically covers:

- statement `if` with and without `else`;
- same-name constructor calls and patterns such as `Error`, `ABIDecoder`,
  `Method`, `Fallback`, `Proxy`, `storage`, and their argument forms;
- generic fallbacks and predicates where present in compatibility fixtures;
- sequential untyped and typed lets;
- match statements with one and multiple scrutinees;
- final unterminated expression statements;
- strings and all operator precedence levels used by the standard sources;
- C-style loops with empty initializer or post lists; and
- every canonical opaque assembly block.

### Compatibility fixture ledger

The implementation includes small exact-string fixtures attributed to the two
pinned revisions. They establish that each deliberate divergence is observable
and stable; they do not make either parser authoritative.

| Topic | Pinned Haskell evidence | Pinned Rust evidence | m2c-v1 decision |
| --- | --- | --- | --- |
| identifiers | host `letterChar`, Unicode accepted | host `\p{L}`/`\p{N}`, Unicode accepted | ASCII only; Unicode outside strings/comments/assembly rejected |
| whitespace | host `space1`, including Unicode space characters | exactly space, tab, LF, CR, and form feed | exactly the Rust five; every other scalar outside strings/comments/assembly is invalid |
| comments | discarded by the parser space consumer | outer comment kind and byte range retained as lexer extras | outer kind and source-owned span retained as lexer evidence; nested block contents are not duplicated |
| `true` and `false` | ordinary identifiers | dedicated tokens converted back to identifiers in name positions | ordinary identifiers; meaning deferred |
| `fallback` as an ordinary name | hard reserved | converted back to an identifier in several name positions | hard reserved; only the fallback declaration marker uses it |
| hard words in module paths | rejected by ordinary identifier parser | token-dependent and editor-path behavior | every ADR-0014-valid keyword spelling accepted contextually |
| module-reference roots | `lib.a` is classified as library-rooted; `std` remains relative | optional external sigil and raw component vector retained | exact `relative`/`libraryRoot`/`standard`/`external` source-shape classification above |
| external references in exports | accepted anywhere an export takes a module path | external sigil accepted by imports but not exports | the same external `moduleRef` form is accepted in every import and export module-reference position |
| top-item order | imports are partitioned from the declaration list | one source-order parsed-item list retained | one source-order `TopItem` list retains imports, exports, pragmas, and declarations together |
| hyphenated names | only four pragma parsers consume them as keywords | lexer admits general hyphenated text, parser diagnoses it later | only four exact pragma-name tokens |
| pragma enabled/status syntax | no enabled marker; absence of targets is the global form | no enabled marker in parsed source shape | no enabled field or source form; exact target presence is retained |
| trailing commas | generally rejected | accepted by many delimited lists | rejected in every comma list |
| empty selectors | accepted by `sepBy` paths | accepted or recovered in some paths | parsed raw, then structural rejection |
| wildcard mixed with names | retained | collapsed to wildcard, losing names | retained raw, then structural rejection |
| operator import/export names | rejected | accepted in parentheses | rejected in m2c-v1 |
| import constructor selectors | rejected | parsed in intermediate forms | rejected in m2c-v1 |
| high-level `:=` | rejected | accepted for let initialization | tokenized but rejected outside opaque assembly; high-level initialization uses `=` |
| integer literals | converted to an integer value | original token slice retained | exact decimal or hexadecimal spelling and digits retained; no numeric conversion |
| parenthesized singleton | child returned, delimiters lost | child returned, delimiters lost | explicit `group` node |
| tuples | normalized to nested `pair` calls/types | tuple node, singleton grouping lost | exact flat source tuple node; no `pair` rewrite |
| final expression | one-expression body rewritten to return | retained as expression statement | retained, with optional semicolon span |
| omitted expression semicolon before another statement | accepted where expression parsing can stop | accepted | rejected; omission is terminal-only |
| value-free return | rejected | accepted as `Return none` | accepted and retained as `none` |
| statement `if` condition | parentheses required | parentheses optional | parentheses required |
| statement `if` without `else` | absent else normalized to empty body | absence retained | absence retained as `none` |
| arbitrary postfix call | initial or receiver names only | arbitrary callee accepted | arbitrary callee accepted |
| postfix on ungrouped conditional | rejected | accepted because conditional is an atom | rejected; explicit grouping required |
| contract-local type alias | rejected | accepted | accepted as a contract member |
| bounded `forall` binder | rejected | accepted then expanded into a predicate | accepted as a distinct source node; never expanded by parser |
| context without `forall` | rejected | accepted in several declaration parsers | rejected; a predicate context is part of `genericPrefix` |
| parenthesized predicate context | rejected; `predListP` is bare | accepted; `pred_list_parser` accepts bare or parenthesized lists | rejected; grouping a type inside one predicate is distinct from grouping the context list |
| ungrouped full-type predicate/class/instance head | rejected; each main head uses `atomTypeP` | accepted; `pred_parser` uses the full `type_parser` | rejected; each main head is `typeAtom`, while grouping permits a full type such as `(a -> b)` |
| qualified class reference | accepted by `qualifiedName` in predicates and instance heads; bounded binders are unavailable | rejected by `ident_parser` | accepted in bounded binders, predicates, and instance references as `QualifiedName` |
| class declaration name binder | accepted as a qualified name | accepted only as one identifier through `pred_parser` | exactly one `IdentifierOccurrence`; qualification is rejected at the first dot |
| predicate placement after `instance` | rejected | accepted as a compatibility alternative | rejected; context precedes `instance` |
| data/type/contract parameters | arbitrary type syntax in several Haskell paths | identifier binders | identifier binders |
| explicit empty named-type or data-constructor field list | rejected | accepted for some forms | rejected; absence and nonempty lists only |
| nullary constructor pattern `T()` | rejected | rejected | rejected; use `T` or `.T` |
| pattern classification | resolver classifies names | parser uses capitalization for some forms | parser retains named syntax; resolution classifies it |
| match with no arms | accepted | rejected | rejected syntactically |
| match-arm arity | accepted unchecked | accepted unchecked | parsed, then exact structural rejection on mismatch |
| match trailing semicolon | rejected | accepted | one optional semicolon accepted and retained |
| let without type and initializer | accepted | accepted | accepted |
| untyped non-lambda parameter | parsed and rejected later | parsed and rejected later | parsed raw, then structural rejection |
| context-invalid modifiers in the fixed `public payable` order | parser failure | parser diagnostic with recovered intermediate tree | parsed raw, then structural rejection |
| invalid fallback parameters/return | parser failure | parser diagnostic with recovered intermediate tree | parsed raw, then structural rejection |
| `break`/`continue` outside a loop | parsed | parsed | parsed raw, then structural rejection |
| let in for-post list | rejected | accepted | rejected; post items are assignment or expression |
| compound assignment | retained as distinct statement | rewritten to ordinary assignment plus infix expression | retained with exact assignment operator |
| string escapes | exactly `n`, `t`, quote, backslash | same four | same four, with exact spelling and decoded value |
| string representation | decoded value retained; exact lexeme lost | original token slice retained | both exact spelling and decoded value retained |
| raw newline in string | accepted | lexer expression accepts it | accepted |
| assembly | parsed by the Haskell Yul parser | parsed into Rust Yul recovery AST | exact balanced opaque slice; Yul deferred |
| parser recovery | no semantic recovery tree | error nodes can enter intermediate trees | no recovery constructor in the AST |
| source offsets | character-oriented Megaparsec offsets | UTF-8 byte ranges | UTF-8 byte ranges tied to `SourceId` |

The conformance fixture set includes the Rust-pinned
`same_name_nullary_ctor_pattern` and
`import_same_name_ctor_unqualified` cases as accepted syntax, while making no
claim about their later target. It also includes accepted minimal fixtures for
`return;`, bounded `forall`, a contract-local type alias, `(f)(x)`, and both
ordinary and leading-dot empty calls, plus rejection fixtures for Unicode
identifiers, every trailing-comma position, explicit empty named-type,
data-constructor, and pattern argument lists, high-level `:=`, empty match arms,
a pattern-arity mismatch, a let in the for-post list, a parenthesized predicate
context, an ungrouped full-type head, and a qualified class-declaration binder.
Accepted fixtures cover grouped full-type heads and qualified class references
in all three reference positions, and distinguish a grouped predicate main
from a forbidden outer grouping of the predicate context. Fixture outcomes are
checked through `parseModule`, including their exact diagnostic constructor and
span.

The minimum boundary fixtures are these exact source strings; formatting is
part of each fixture value:

```text
accepted-value-free-return:
function f() -> () { return; }

accepted-bounded-forall:
forall a:Eq. function id(x:a) -> a { return x; }

accepted-grouped-full-type-heads:
class (a -> b) :C {}
instance (a -> b):pkg.C {}

accepted-parenthesized-predicate-main:
forall a. (a):pkg.Eq => function p(x:a) -> a { return x; }

accepted-qualified-class-references:
forall a:pkg.Eq. function f(x:a) -> a { return x; }
forall a. a:pkg.Show => function g(x:a) -> a { return x; }
instance word:pkg.Render {}

accepted-contract-local-alias:
contract C { type T = word; }

accepted-generic-fallback:
contract C { forall a. a:Eq => payable fallback() -> () { return; } }

accepted-arbitrary-postfix-call:
function apply(f:word -> word, x:word) -> word { return (f)(x); }

accepted-empty-call-shapes:
function call0(f:() -> word) -> word { .T(); return f(); }

accepted-no-else:
function f(x:bool) -> () { if (x) { return; } }

accepted-same-name-nullary-syntax:
data T = T; function f(x:T) -> T { match x { | T => return T; } }

rejected-unicode-identifier:
function λ() -> () { return; }

rejected-trailing-parameter-comma:
function f(x:word,) -> word { return x; }

rejected-empty-named-type-arguments:
function f(x:T()) -> T { return x; }

rejected-empty-data-constructor-fields:
data T = C();

rejected-empty-pattern-arguments:
function f(x:T) -> T { match x { | C() => return x; } }

rejected-high-level-colon-equal:
function f() -> word { let x := 0; return x; }

rejected-empty-match:
function f(x:word) -> word { match x { } }

structurally-rejected-match-arity:
function f(x:word, y:word) -> word { match x, y { | _ => return x; } }

rejected-let-in-for-post:
function f() -> () { for (; true; let x = 0) { } }

rejected-parenthesized-predicate-context:
forall a. (a:Eq) => function f(x:a) -> a { return x; }

rejected-ungrouped-class-head:
class a -> b :C {}

rejected-ungrouped-instance-head:
instance a -> b:pkg.C {}

rejected-ungrouped-predicate-head:
forall a b. a -> b:pkg.C => function f(x:a) -> b { return x; }

rejected-qualified-class-declaration-binder:
forall a. class a:C.D {}
```

The same-name import fixture is a two-file parser fixture:

```text
lib.solc:
export { T(*) }; data T = T;

main.solc:
import lib.{T}; function f(x:T) -> T { match x { | T => return T; } }
```

The Unicode case fails with `invalidCharacter` on the two UTF-8 bytes of `λ`.
The arity case parses and then fails with
`matchPatternArityMismatch` carrying expected arity two and actual arity one.
The qualified class-declaration binder case fails with `unexpected` on the dot
at exact half-open UTF-8 byte span `[19, 20)`, with found symbol `.` and the
frontier union containing exactly `(` and `{`. This proves that
`ClassDeclPayload.className` is an `IdentifierOccurrence`, while the accepted
qualified-reference fixture proves that reference positions remain
`QualifiedName`.
The other rejected fixtures fail at the first token that cannot continue their
named production. Tests add one exact fixture for every other comma-list
position and every diagnostic constructor.

### Module boundaries and implementation order

The implementation is split so judgments and executors remain independently
auditable:

```text
Solcore/Standard/CanonicalData.lean

Solcore/Surface/Multi/Source.lean
Solcore/Surface/Multi/Token.lean
Solcore/Surface/Multi/Syntax.lean
Solcore/Surface/Multi/Diagnostic.lean
Solcore/Surface/Multi/Measure.lean
Solcore/Surface/Multi/Grammar.lean

Solcore/Surface/Multi/LexicalJudgment.lean
Solcore/Surface/Multi/Lexer.lean
Solcore/Surface/Multi/ParserJudgment.lean
Solcore/Surface/Multi/Chart.lean
Solcore/Surface/Multi/Parser.lean
Solcore/Surface/Multi/StructureJudgment.lean
Solcore/Surface/Multi/Structure.lean

Solcore/Surface/Multi/Properties.lean
Solcore/Surface/Multi/StandardFixtures.lean
Solcore/Surface/Multi.lean
```

`LexicalJudgment.lean` does not import `Lexer.lean`.
`ParserJudgment.lean` does not import `Chart.lean` or `Parser.lean`.
`StructureJudgment.lean` does not import `Structure.lean`.
`Lexer.lean`, `Chart.lean`, `Parser.lean`, and `Structure.lean` do not import
their sibling judgments. `Parser.lean` does not import `Chart.lean`; only
`Properties.lean` connects either executor to the declarative judgment and
proves their equality. `CanonicalData.lean` imports no Surface or resolver
module. The public internal umbrella is added only after all correspondence,
certificate, fixture, and kernel audits pass.

Implementation proceeds in this order:

1. neutral canonical raw bytes, strict UTF-8 decoding, source spans, located
   values, tokens, closed diagnostics, and the exact measures;
2. the independent lexical judgment and assembly-slice relation;
3. the pure maximal-munch lexer and its correspondence proofs;
4. the complete AST, checked EBNF expansion, stable production/action tables,
   and independent parser judgment;
5. finite-chart `G`, then the separate fast full-token parser, their bounds,
   correspondence, and exact result-equality proof;
6. independent structural acceptance and the structural validator;
7. location, token-correspondence, diagnostic, and resource theorems;
8. checked compatibility, strict UTF-8, byte-round-trip, and six-file standard
   certificates; and
9. the internal `Solcore.Surface.Multi` umbrella.

No resolver module may be implemented against an intermediate parser slice.
No later slice may bypass `CertifiedParsedModule` by importing compiler HIR,
constructing unchecked AST values, or assuming a parse equation.

## Consequences

- Resolution receives a closed, location-complete, recovery-free AST tied to
  exact ADR-0014 source identity.
- Reachability remains lazy, so malformed unreachable files do not create
  diagnostics.
- All six canonical standard files have kernel-checked parse evidence before
  standard resolution is attempted.
- Missing `else`, missing return values, grouping, tuple shape, bounded
  binders, constructor spelling, and terminators remain observable.
- Assembly can participate in source identity and statement order without
  importing unpinned Yul semantics.
- ASCII identifiers avoid host Unicode-version drift at the cost of an
  explicit compatibility divergence.
- The larger grammar and certificate proof add a substantial prerequisite
  before the resolver, but remove parser behavior from the resolver's trusted
  assumptions.

## Rejected alternatives

### Extend Surface v1 in place

Rejected because Surface v1 is published and intentionally small. Reusing its
opaque source label or changing its AST would mutate an existing protocol
boundary.

### Use either compiler's parsed tree

Rejected because the Haskell tree erases source shape and the Rust tree admits
recovery nodes and implementation-owned classification. Compiler allocation,
host parser behavior, and recovery policy are not specification inputs.

### Parse every workspace file before reachability

Rejected because it would diagnose malformed sources that neither an entry
module nor any import/export frontier can observe. The parser is module-local;
the resolver owns reachable collection.

### Normalize convenient syntax during parsing

Rejected because implicit return, pair construction, compound-assignment
expansion, bounded-binder expansion, and absent-else normalization destroy the
source identities needed by later judgments.

### Parse and resolve same-name constructors together

Rejected because a one-segment pattern or call has a context-dependent target.
The parser retains its written shape; ADR-0017 decides visibility and target
classification.

### Parse Yul in M2c

Rejected because Yul grammar and semantics require their own pinned decision.
Balanced opaque slices are sufficient for Solcore scope and source identity.

### Accept Unicode through Lean or host character predicates

Rejected because such predicates would silently import a Unicode version and
normalization policy. A future Unicode grammar can be added under a new
identifier with explicit tables.

### Permit parser recovery nodes in certified modules

Rejected because a recovery placeholder has no unique language meaning.
Lexical or parse failure produces a closed diagnostic and no AST.

## Conformance requirements

- Implement exactly the token, AST, grammar, structural, and diagnostic sums
  above; do not add an unknown/string escape constructor.
- Keep every source-semantic node and marker located with a valid
  `Multi.SourceSpan` tied to the exact `WorkspaceFile`.
- Retain the complete token and comment streams as certificate evidence.
- Prove maximal munch, complete token consumption, relation functionality,
  executor soundness and completeness, diagnostic correspondence, and the
  fixed resource bounds.
- Test every token and hard/contextual keyword boundary, including keyword
  spellings as module path components.
- Test nested comments, CRLF line comments, non-ASCII scalars in normal
  syntax, raw Unicode in strings/comments, every string escape, and every
  unterminated scanner state.
- Test assembly braces nested normally and ignored inside line comments, nested
  block comments, and strings.
- Test every grammar production, precedence boundary, associativity rule,
  non-associative repetition, optional construct, empty permitted list, and
  forbidden trailing comma.
- Check mechanical EBNF expansion, stable production/action IDs, all nine
  priority guards, greatest-cursor frontier unions, the repeated-nonassociative
  override, and unique reduction across every packed derivation.
- Test all structural diagnostic constructors, their exact primary spans,
  canonical ordering, and duplicate removal.
- Check the compatibility ledger fixtures and prove both canonical-standard
  theorems, every strict UTF-8 rejection fixture, and every canonical byte
  round trip in the ordinary Lean kernel.
- Use no host I/O, filesystem API, parser library, regex engine, Unicode
  property lookup, mutable global cache, recovery sentinel, undeclared trust
  assumption, or `native_decide` in the semantic kernel.
- Extend the repository kernel-policy roots to include both
  `Solcore/Standard` and `Solcore/Surface/Multi` before any canonical-data or
  internal Surface umbrella is consumed by resolution.
- Pass full build, test, metadata, semantic-kernel, English-text, formatting,
  forbidden-trust, and public-theorem assumption audits for every slice.
- Do not modify any existing schema, profile, capability, or golden manifest.

## Remaining decisions

No lexer, parser, AST, EBNF-expansion, production/action-ID, priority-guard,
AST-reduction, parse-frontier diagnostic, structural-diagnostic, span,
separator, precedence, termination, resource-bound, strict-UTF-8, canonical
raw-data, or canonical-fixture decision required to implement this ADR remains
open. Proposed-to-Accepted review may replace a decision, but code must not
precede acceptance or fill a gap from either comparison implementation.

ADR-0016 must define structural syntax identity over
`Multi.CertifiedParsedModule`. ADR-0017 must define module/interface/scope
resolution, including same-name constructor classification and module-binding
validity. M2d must separately define type checking, overload and instance
selection, literal conversion, receiver selection, callability, assignment
targets, implicit final-expression meaning, Yul semantics, and elaboration to
Semantic Core. A publication ADR must separately define wire schemas, limits,
profiles, Oracle behavior, and comparison verdicts.
