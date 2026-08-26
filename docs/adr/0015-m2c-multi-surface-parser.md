# ADR-0015: M2c Multi Surface parser kernel

- Status: Accepted
- Decision date: 2026-08-18
- Scope: M2c internal multi-module Surface lexer and parser

## Reader summary / Current implementation

- **Decision:** Define the closed, source-preserving
  `solcore-multi-surface/m2c-v1` language, its independent lexer/parser
  judgments and executors, structural acceptance, diagnostics, and the
  `CertifiedParsedModule` boundary. This is an internal specification, not a
  published Oracle feature.
- **Current implementation:** Source, token, syntax, diagnostics, measures,
  grammar tables, `ParserCore`, the lexical judgment and lexer, the parser
  judgment, the finite contextual chart, parser-totality certificates, a total
  file-only lexer/parser frontend, and their current soundness proofs are
  present. The structural judgment and validator are also present, with
  two-way diagnostic correspondence, sufficient traversal fuel, canonical
  reports, and executable acceptance equivalence. Strict UTF-8 and
  canonical-byte facts are present. Parser-wide source-location validity and
  nesting are proved by `Parses.everyLocationValid`. `CertifiedParsedModule`,
  its phase-composition core, executable resource-bound functions, and the
  concrete AST-carrier cardinality theorem are also present. Exact-token
  dispatch is exhaustive; module-reference and let-binding callbacks are
  closed, leaving match-arm, postfix-expression, and statement-body callbacks.
  All six structural unit families now have executable traces and exact
  projections, and a public ledger exposes their combined total. The two
  canonical-list passes also have insertion-square comparison bounds, and the
  complete ledger satisfies the ADR-fixed quadratic structural bound.
  The quadratic fast-parser schedule is also exposed as a public
  three-component capacity ledger whose total is exactly `parseBound`, with
  reduction theorems that make the remaining executor correspondence and
  component-bound obligations explicit.
- **Not yet implemented:** The separate fast `Parser`, final exact-token root
  closure and proof-argument-free frontend wrapper, the counted parser
  execution and its correspondence to the schedule ledger, the schedule's
  component bounds and resulting parser-bound sufficiency,
  the six complete canonical-standard parse certificates, and the public
  `Solcore.Surface.Multi` umbrella are absent.
  Consequently ADR-0015 is Accepted as a decision but is not yet a completed
  implementation or publication boundary.
- **Suggested reading:** Read “Acceptance scope and frozen published
  boundaries”, “Closed source-preserving AST”, and “Complete syntactic grammar”
  for the language; then “Independent judgments and pure executors”,
  “Termination and resource bounds”, and “Module boundaries and implementation
  order” for the proof and delivery plan. Use the compatibility ledger as a
  decision index rather than reading every grammar table first.

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

### Acceptance scope and frozen published boundaries

This ADR was originally reviewed behind a proposal gate and is now Accepted.
Acceptance authorizes only the internal modules, judgments, executors, proofs,
and fixtures listed below; it does not claim that every implementation slice is
complete. Publication still requires a separate ADR.

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
                ::= expression [";"]
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
declarative judgment, `Chart.G`, and the fast executor use the same anchored
three-way guard decision, and its functionality is proved.

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

Dependent action carriers must not unfold a private grammar helper or perform
one unchecked cast per expanded production. `Grammar.lean` therefore owns this
public bridge API in addition to `ProductionId.rhs`:

```text
EbnfAtom.grammarSymbol     : EbnfAtom -> GrammarSymbol
  | terminal terminal => GrammarSymbol.terminal terminal
  | nonterminal rule   => GrammarSymbol.nonterminal (.rule rule)
AtomSite.symbol            : AtomSite -> GrammarSymbol
SequenceSite.children      : SequenceSite -> List GrammarSite
GroupSite.child            : GroupSite -> GrammarSite
ChoiceSite.branchExpressions :
  (site : ChoiceSite) -> Vector EbnfExpr site.branchCount
ChoiceSite.branch          : (site : ChoiceSite) ->
                             Fin site.branchCount -> GrammarSite
ChoiceSite.branches        :
  (site : ChoiceSite) -> Vector GrammarSite site.branchCount :=
    Vector.ofFn site.branch
ChoiceSite.branchListIndex : (site : ChoiceSite) ->
  Fin site.branchCount -> Fin site.branchExpressions.toList.length
OptionalSite.child         : OptionalSite -> GrammarSite
StarSite.child             : StarSite -> GrammarSite
PlusSite.child             : PlusSite -> GrammarSite
List0Site.element          : List0Site -> GrammarSite
List1Site.element          : List1Site -> GrammarSite

SequenceSite.children_expression (site : SequenceSite) :
  (site.children.map GrammarSite.expression) =
    site.site.expression.children

GrammarSite.root_expression (rule : GrammarRuleId) :
  (GrammarSite.root rule).expression = m2cV1.rhs rule
AtomSite.expression_eq_atom (site : AtomSite) :
  site.site.expression = EbnfExpr.atom site.atom
AtomSite.symbol_eq (site : AtomSite) :
  site.symbol = site.atom.grammarSymbol
SequenceSite.expression_eq_sequence (site : SequenceSite) :
  site.site.expression =
    EbnfExpr.sequence (site.children.map GrammarSite.expression)
GroupSite.expression_eq_group (site : GroupSite) :
  site.site.expression = EbnfExpr.group site.child.expression
ChoiceSite.expression_eq_choice (site : ChoiceSite) :
  site.site.expression =
    EbnfExpr.choice site.branchExpressions.toList
ChoiceSite.branch_expression
    (site : ChoiceSite) (branch : Fin site.branchCount) :
  (site.branch branch).expression = site.branchExpressions.get branch
ChoiceSite.branchListIndex_val
    (site : ChoiceSite) (branch : Fin site.branchCount) :
  (site.branchListIndex branch).val = branch.val
ChoiceSite.branch_get_toList
    (site : ChoiceSite) (branch : Fin site.branchCount) :
  site.branchExpressions.toList.get (site.branchListIndex branch) =
    site.branchExpressions.get branch
OptionalSite.expression_eq_optional (site : OptionalSite) :
  site.site.expression = EbnfExpr.optional site.child.expression
StarSite.expression_eq_star (site : StarSite) :
  site.site.expression = EbnfExpr.star site.child.expression
PlusSite.expression_eq_plus (site : PlusSite) :
  site.site.expression = EbnfExpr.plus site.child.expression
List0Site.expression_eq_list0 (site : List0Site) :
  site.site.expression = EbnfExpr.list0 site.element.expression
List1Site.expression_eq_list1 (site : List1Site) :
  site.site.expression = EbnfExpr.list1 site.element.expression

ListSite.element : ListSite -> GrammarSite
  | .list0 site => site.element
  | .list1 site => site.element

ListSite.element_list0 (site : List0Site) :
  (ListSite.list0 site).element = site.element := rfl
ListSite.element_list1 (site : List1Site) :
  (ListSite.list1 site).element = site.element := rfl

matchArmPatternListSite : List1Site
matchArmPatternListSite_key :
  matchArmPatternListSite.site.val =
    { rule := GrammarRuleId.matchArm, path := [1] }
matchArmPatternListSite_expression :
  matchArmPatternListSite.site.expression =
    EbnfExpr.list1
      (EbnfExpr.atom (EbnfAtom.nonterminal GrammarRuleId.pattern))
```

Every selector is total because its site subtype certifies the corresponding
node shape. `ChoiceSite.branchExpressions` and `ChoiceSite.branch` are defined
by dependent elimination on `site.hasKind`; the impossible eight outer
constructors are discharged from that equality. Thus the same
`Fin site.branchCount` indexes both vectors. The only conversion to the
`Fin site.branchExpressions.toList.length` stored by a choice `EbnfValue` is
the checked `branchListIndex`; its value and lookup equations are public, so
no implementation manufactures or assumes a `Fin` equality.
`ListSite.element` is the displayed case split,
not an attempted projection such as `owner.expression.child[0]` (there is no
such total singular projection on `EbnfExpr`). The two computation theorems
make the tail-element index reduce without a cast.
`matchArmPatternListSite` is constructed by `GrammarSite.ofKey?` at the one
displayed key and then refined by `GrammarSiteOfKind.ofSite? .list1`; the two
`some` equations and the displayed key/expression equations are proved in
`Grammar.lean`. It is not selected by searching for a `list1(pattern)` shape:
that shape also occurs at two pattern-argument sites. The module also exports one
`[simp]` RHS-layout theorem for each of the eleven production constructors:

```text
ProductionId.rhs_root (R : GrammarRuleId) :
  rhs(root R)       = [nonterminal (aux (GrammarSite.root R))]
ProductionId.rhs_atom (s : AtomSite) :
  rhs(atom s)       = [s.symbol]
ProductionId.rhs_seq (s : SequenceSite) :
  rhs(seq s)        = s.children.map (nonterminal . aux)
ProductionId.rhs_group (s : GroupSite) :
  rhs(group s)      = [nonterminal (aux s.child)]
ProductionId.rhs_choice
    (s : ChoiceSite) (i : Fin s.branchCount) :
  rhs(choice s i)   = [nonterminal (aux (s.branch i))]
ProductionId.rhs_opt_none (s : OptionalSite) : rhs(opt s none) = []
ProductionId.rhs_opt_some (s : OptionalSite) :
  rhs(opt s some)   = [nonterminal (aux s.child)]
ProductionId.rhs_star_nil (s : StarSite) : rhs(star s nil) = []
ProductionId.rhs_star_cons (s : StarSite) :
  rhs(star s cons)  = [nonterminal (aux s.child),
                       nonterminal (aux s.site)]
ProductionId.rhs_plus_one (s : PlusSite) :
  rhs(plus s one)   = [nonterminal (aux s.child)]
ProductionId.rhs_plus_cons (s : PlusSite) :
  rhs(plus s cons)  = [nonterminal (aux s.child),
                       nonterminal (aux s.site)]
ProductionId.rhs_list0_nil (s : List0Site) : rhs(list0 s nil) = []
ProductionId.rhs_list0_cons (s : List0Site) :
  rhs(list0 s cons) = [nonterminal (aux s.element),
                       nonterminal (tail (.list0 s))]
ProductionId.rhs_list1 (s : List1Site) :
  rhs(list1 s)      = [nonterminal (aux s.element),
                       nonterminal (tail (.list1 s))]
ProductionId.rhs_tail_nil (s : ListSite) : rhs(tail s nil) = []
ProductionId.rhs_tail_cons (s : ListSite) :
  rhs(tail s cons)  = [terminal (symbol comma),
                       nonterminal (aux s.element),
                       nonterminal (tail s)]
```

The “eleven” count is by outer `ProductionId` constructor; branch equations
are the displayed exhaustive subcases. `ParserCore` implements exactly eleven
typed HList transport functions using these public outer-constructor equality
theorems, branch/element equalities, and `SequenceSite.children_expression`.
The bridges are the total eliminators of each site subtype's `hasKind` proof;
`ParserCore` does not repeat dependent elimination on `EbnfExpr.kind`.
Their equality arguments are checked
proofs and erase at runtime; unchecked representation conversion, conversion
from an assumed equation,
reflection into private definitions, and 1,039 hand-written conversions are
forbidden. Adding this API changes neither `ProductionId`, `ActionId`, their
ordering, nor `P`, `D`, or `F`.

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
following closed guard algebra resolves them. A guard decision is computed
from the same expanded productions by span recognition; it does not invoke
`parseTokens`, resolution, or semantic typing. Lower numeric priority wins,
and an explicitly disabled alternative cannot enter the chart.

```text
PriorityGuardId =
  | G01_statementIf | G02_matchArmBoundary | G03_parameterComptime
  | G04_letComptime | G05_typeComptime | G06_patternComptime
  | G07_leadingDotArguments | G08_terminalExpression
  | G09_genericContext

ParseOverrideId = G10_repeatedNonAssociative

Boundary(tokens : List Token) = Fin (tokens.length + 2)

TerminalCursor(tokens : List Token) = Fin (tokens.length + 1)

TerminalCursor.beforeBoundary {tokens : List Token} :
  TerminalCursor tokens -> Boundary tokens
  | cursor => Fin.castLE (Nat.le_succ _) cursor

TerminalCursor.afterBoundary {tokens : List Token} :
  TerminalCursor tokens -> Boundary tokens
  | cursor =>
      { val := cursor.val + 1,
        isLt := Nat.succ_lt_succ cursor.isLt }

Boundary.start(tokens : List Token) : Boundary tokens =
  { val := 0, isLt := Nat.zero_lt_succ _ }

Boundary.afterLogicalEOF(tokens : List Token) : Boundary tokens =
  { val := tokens.length + 1,
    isLt := Nat.lt_succ_self (tokens.length + 1) }

Multi.Grammar.GuardDecision = positive | negative | neutral

Multi.Grammar.Polarity = positive | negative

Multi.Grammar.Polarity.accepts :
  Polarity -> GuardDecision -> Bool
  | positive, positive => true
  | positive, negative => false
  | positive, neutral  => true
  | negative, positive => false
  | negative, negative => true
  | negative, neutral  => true

Multi.Grammar.GuardDecision.allows :
  GuardDecision -> Polarity -> Bool
  | decision, polarity => Polarity.accepts polarity decision

GuardContext(tokens : List Token) =
  | plain
  | bracedBody       (bodyStart : Boundary tokens)
  | armBody          (armBodyStart : Boundary tokens)
  | postfixInvocation (postfixStart : Boundary tokens)

ProductionInstanceKey(tokens : List Token) = {
  production : ProductionId,
  origin     : Boundary tokens,
  context    : GuardContext tokens
}

GuardInstanceKey(tokens : List Token) = {
  guard        : PriorityGuardId,
  contextStart : Boundary tokens,
  siteCursor   : Boundary tokens,
  ordered      : contextStart.val <= siteCursor.val
}

DottedItem(tokens : List Token) = {
  production : ProductionId,
  dot        : Fin (production.rhs.length + 1),
  origin     : Boundary tokens,
  current    : Boundary tokens
}

PackedEdgeKey(tokens : List Token) =
  | scanned
      (before after : DottedItem tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : DottedItem tokens)
      (sharedCursor : Boundary tokens)

ContextualItemKey(tokens : List Token) = {
  raw     : DottedItem tokens,
  context : GuardContext tokens
}

ContextualPackedEdgeKey(tokens : List Token) =
  | scanned
      (before after : ContextualItemKey tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : ContextualItemKey tokens)
      (sharedCursor : Boundary tokens)

CanonicalCompleteRootItem(tokens : List Token,
                          rule : GrammarRuleId,
                          origin finish : Boundary tokens,
                          context : GuardContext tokens) :
    ContextualItemKey tokens = {
  raw := {
    production := ProductionId.root rule,
    dot := {
      val := (ProductionId.root rule).rhs.length,
      isLt := Nat.lt_succ_self _
    },
    origin := origin,
    current := finish
  },
  context := context
}
```

`Boundary` ranges over all chart boundaries, including the boundary after the
logical `EOF`. A `bracedBody` start is the boundary immediately after that
body's `{`; an `armBody` start is the boundary immediately after that arm's
`=>`; and a `postfixInvocation` start is the origin of the enclosing source
rule `postfix`, before its `atom`. These are source-token boundaries, not byte
cursors. `plain` is used outside all three locally relevant contexts.

These token-indexed data types, `descendContext`, the terminal-stream lookup
below, and the proof-free validity predicates on packed edges are owned by
`Solcore.Surface.Multi.ParserCore`. `ParserCore` imports `Grammar` and is
imported independently by `ParserJudgment`, `Chart`, and `Parser`; none of
those three imports either sibling. This shared ownership is required:
duplicating a `GuardContext`, boundary, or packed-edge type in the judgment and
executor would make context identity an unproved conversion instead of the
same key. `Grammar` continues to own only the grammar table and its finite IDs,
including `GuardDecision`, `Polarity`, and `guardOf`.

`TerminalCursor` selects one member of `tokens` followed by the one logical
`EOF`; it never denotes the boundary after `EOF`. `DottedItem` keeps its four
displayed fields rather than storing an implementation-selected opaque chart
node. `CanonicalCompleteRootItem` is the only rule-indexed root refinement:
its production is definitionally `.root rule`, its dot is definitionally the
complete dot, its left-hand side reduces definitionally to `.rule rule`, and
its semantic output index therefore reduces to `RuleValue rule`. It contains
no equality field or cast. All structures and sums in this block have `Repr`, `BEq`, and
`DecidableEq`; proof fields introduced by the valid-edge subtypes below are
proof-irrelevant.

`GuardDecision` is owned by `Solcore.Surface.Multi.Grammar`, beside
`PriorityGuardId`, `Polarity`, and `guardOf`; judgment and executor modules
import that one type. `GuardDecision.neutral` is not a third priority side. It
means that the two polarities do not overlap at this cursor and therefore both
remain enabled. `GuardDecision.allows decision polarity` is definitionally
`Polarity.accepts polarity decision`, as shown above. The previous
`Polarity -> Bool -> Bool` signature is replaced; it is not a compatible
overload or a second API, and a guard decision is never represented by a
globally cached Boolean.

The context attached to a predicted production is fixed by the following
total transition. `waiting.raw.current` becomes the origin of the resulting
`ProductionInstanceKey` in every case. The two sequence positions below are
the positions before child `1` of
`body ::= "{" statement* "}"` and before child `3` of
`matchArm ::= "|" list1(pattern) "=>" armStatement*` respectively.

```text
descendContext {tokens : List Token}
    (waiting : ContextualItemKey tokens)
    (predicted : ProductionId) : GuardContext tokens =
  | predicted = P.root[postfix] =>
      postfixInvocation waiting.raw.current
  | waiting.raw is P.seq[body.root] at dot 1 and
      predicted.lhs = Aux(body.root.1) =>
      bracedBody waiting.raw.current
  | waiting.raw is P.seq[matchArm.root] at dot 3 and
      predicted.lhs = Aux(matchArm.root.3) =>
      armBody waiting.raw.current
  | _ => waiting.context
```

The second and third cases apply only on initial entry from the displayed
sequence production. Prediction of `P.star[body.root.1,*]` or
`P.star[matchArm.root.3,*]` from its own cons production inherits the existing
context and therefore does not move the region start. A nested `postfix`,
braced body, or match arm temporarily replaces the outer context; completion
restores the waiting item's context. Consequently one context value, rather
than an unbounded ancestry stack, is sufficient.

For a cell `cell = (guard, polarity)` in
`guardOf productionInstance.production`, the closed relation

```text
GuardAnchor {tokens : List Token} : ProductionInstanceKey tokens ->
  (PriorityGuardId × Polarity) -> GuardInstanceKey tokens -> Prop
```

holds exactly when the cell belongs to `guardOf`, the instance guard is
`guard`, its `siteCursor` is `productionInstance.origin`, and the remaining
anchor equation in this table holds:

| Guard | Required production context | `contextStart` / `siteCursor` |
| --- | --- | --- |
| `G01_statementIf` | any | statement start / the same statement start |
| `G02_matchArmBoundary` | `armBody armBodyStart` | that `armBodyStart` / the current `armStatement*` iteration |
| `G03_parameterComptime` | any | parameter start / the same parameter start |
| `G04_letComptime` | any | cursor immediately after the let-binding colon / that same cursor |
| `G05_typeComptime` | any | type start / the same type start |
| `G06_patternComptime` | any | pattern start / the same pattern start |
| `G07_leadingDotArguments` | `postfixInvocation postfixStart` | that canonical enclosing postfix invocation origin / the guarded argument-or-call site (the current token is `(` only for positive evidence) |
| `G08_terminalExpression` | `bracedBody bodyStart` or `armBody armBodyStart` | that nearest enclosing region start / the selected expression's end, immediately before the optional terminator |
| `G09_genericContext` | any | context-option start after `forallClause` / that same cursor |

“Any” means that the surrounding context is retained in the
`ProductionInstanceKey`; it does not mean that it may be erased when items are
deduplicated. For `G07`, both the leading-dot atom option and every competing
call `postfixPart` use the origin of the same enclosing `postfix`. An
implementation-selected atom origin, postfix-part origin, or immediately
preceding dot is not a legal anchor.

`GuardAnchor.functional` is required:

```text
GuardAnchor.functional
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {left right : GuardInstanceKey tokens} :
  GuardAnchor productionInstance cell left ->
  GuardAnchor productionInstance cell right ->
  left = right

GuardAnchor.decide :
  {tokens : List Token} ->
  (productionInstance : ProductionInstanceKey tokens) ->
  (cell : PriorityGuardId × Polarity) ->
  Option (GuardInstanceKey tokens)

GuardAnchor.decide_eq_some_iff
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {guardInstance : GuardInstanceKey tokens} :
  GuardAnchor.decide productionInstance cell = some guardInstance iff
    GuardAnchor productionInstance cell guardInstance
```

This theorem follows from the displayed equations and the canonical context
transition; it must not be obtained by choosing the first of several anchors.
`ParserCore` owns the table relation, the total executable `decide`, and this
characterization. They inspect only Grammar-owned guard cells and Core-owned
keys/contexts; they do not inspect unguarded recognition or `GuardEvidence`.
Consequently both executors may construct the same structural anchor without
importing `ParserJudgment`.

Guard evidence uses one auxiliary, wholly unguarded recognition relation. The
terminal stream and terminal match are first fixed completely:

```text
TerminalStreamValue = retained Token | endOfFile

TokensOwnedBy (file : WorkspaceFile) (tokens : List Token) : Prop =
  forall token, token in tokens -> token.span.ValidFor file

TerminalAt
    (file : WorkspaceFile) (tokens : List Token)
    (cursor : TerminalCursor tokens)
    (value : TerminalStreamValue) (span : SourceSpan) : Prop =
  | cursor.val < tokens.length,
    tokens[cursor.val]? = some token,
    value = retained token,
    span = token.span,
    token.span.ValidFor file
  | cursor.val = tokens.length,
    value = endOfFile,
    span = { source := file.id,
             startByte := file.content.utf8ByteSize,
             endByte := file.content.utf8ByteSize }

TerminalMatches : TerminalSymbol -> TerminalStreamValue -> Prop
  | hardKeyword keyword, retained token =>
      token.payload = hardKeyword keyword
  | contextualKeyword keyword, retained token =>
      token.payload = identifier keyword.spelling
  | pragmaName kind, retained token => token.payload = pragmaName kind
  | symbol symbol, retained token => token.payload = symbol symbol
  | category identifier, retained token =>
      exists text parsed,
        token.payload = identifier text and
        Identifier.parse text = some parsed
  | category pathComponent, retained token =>
      (exists text parsed,
         token.payload = identifier text and
         PathSegment.parse text = some parsed) or
      (exists keyword parsed,
         token.payload = hardKeyword keyword and
         PathSegment.parse keyword.spelling = some parsed)
  | category decimalLiteral, retained token =>
      exists spelling digits,
        token.payload = decimalLiteral spelling digits
  | category hexadecimalLiteral, retained token =>
      exists spelling digits,
        token.payload = hexadecimalLiteral spelling digits
  | category stringLiteral, retained token =>
      exists spelling decoded,
        token.payload = stringLiteral spelling decoded
  | category assemblyBlock, retained token =>
      exists slice, token.payload = assemblyBlock slice
  | endOfFile, endOfFile => True
  | _, _ => False

MatchedTerminal
    (file : WorkspaceFile) (tokens : List Token)
    (terminal : TerminalSymbol) = {
  cursor  : TerminalCursor tokens,
  value   : TerminalStreamValue,
  span    : SourceSpan,
  at      : TerminalAt file tokens cursor value span,
  matches : TerminalMatches terminal value
}

BoundaryByte : WorkspaceFile -> (tokens : List Token) ->
  Boundary tokens -> Nat -> Prop

ConsumedSpan : WorkspaceFile -> (tokens : List Token) ->
  Boundary tokens -> Boundary tokens -> SourceSpan -> Prop

ConsumedSpanWitness
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens) = {
  span     : SourceSpan,
  consumed : ConsumedSpan file tokens origin finish span
}

sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {alpha : Type}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (payload : alpha) : Located alpha =
  { span := witness.span, payload := payload }

SourceLocates
    {alpha : Type}
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens) (payload : alpha)
    (located : Located alpha) : Prop =
  exists witness : ConsumedSpanWitness file tokens origin finish,
    located = sourceLoc witness payload

ConsumedSpanWitness.compute
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val <= finish.val) :
  ConsumedSpanWitness file tokens origin finish
```

Thus contextual words are identifier tokens with the exact contextual
spelling; they are never a second lexer token kind. The identifier category
cannot match a hard-keyword token. A path component may match either an
identifier token or the exact spelling retained by a hard-keyword token, but
only when that spelling constructs a `PathSegment`. The three literal token
kinds are the complete `literal` category. The logical `EOF` has the unique
empty source span at the file's UTF-8 byte size; it is not a synthetic `Token`.

`BoundaryByte file tokens boundary byte` first requires
`TokensOwnedBy file tokens`; it is functional and otherwise holds exactly as
follows. If `boundary.val < tokens.length`, `byte` is the indexed token's
`span.startByte`. At either of the final two chart
boundaries (`boundary.val >= tokens.length`), `byte` is
`file.content.utf8ByteSize`. Thus trivia belongs to no token value. Leading
trivia before the first consumed token and trailing trivia after the last
consumed token are excluded from an ordinary nonempty syntax span; trivia
between two consumed tokens necessarily lies inside their minimal contiguous
byte interval. The logical-EOF and post-EOF boundaries share the physical end
byte while remaining distinct grammar boundaries.

`ConsumedSpan file tokens start finish span` first requires
`TokensOwnedBy file tokens` and `start.val <= finish.val`. If the half-open cursor interval
`[start.val, finish.val)` contains retained tokens, let `first` and `last` be
its least and greatest retained-token cursors; it holds exactly for
`{ source := file.id, startByte := first.span.startByte,
endByte := last.span.endByte }`. Logical `EOF` is not retained and does not
extend that range. If the interval contains no retained token, it holds exactly
for the empty span at the functional `BoundaryByte file tokens start`.
`ConsumedSpan` is therefore functional. The module root deliberately overrides
it with `[0, file.content.utf8ByteSize)`, and an empty match-arm body deliberately
uses the empty span at its retained `fatArrow.span.endByte`; these are the only
two root-action span overrides. Every other located value constructed by a
root action takes the `ConsumedSpan` of that source production's exact origin
and finish, while a pass-through action preserves the child's already fixed
span.

`ConsumedSpanWitness` is an explicit checked Type input to a locating root
constructor. `sourceLoc` projects its span and constructs the `Located` value;
it never searches for or selects a span from a proposition. Every
`RuleReduction` constructor below that uses `sourceLoc` takes such a witness as
an explicit argument. `SourceLocates` is the proposition exposed to proofs.
`ConsumedSpan.functional` gives `SourceLocates.functional`, but functionality
is used only to compare two already-constructed outputs and never to obtain
one. The witness, relation, and constructor are owned by `ParserCore` beside
`BoundaryByte` and `ConsumedSpan`.
`ConsumedSpanWitness.compute` is the total constructive implementation: it
decides whether the finite interval contains a retained token and computes the
first/last or empty-boundary case directly. Completed coherent items provide
`ordered`; the public parse premise provides `owned`. Its proof field is then
established from those inputs. Thus ordinary locating actions have an
executable witness whenever their completed interval is ordered; the module
and empty-arm overrides do not call this constructor.

The unguarded chart and its named projections have these complete signatures:

```text
UnguardedReach :
  WorkspaceFile -> (tokens : List Token) -> DottedItem tokens -> Prop

UnguardedRecognizes :
  WorkspaceFile -> (tokens : List Token) -> NonterminalSymbol ->
  Boundary tokens -> Boundary tokens -> Prop

GreatestUnguardedEnd :
  WorkspaceFile -> (tokens : List Token) -> NonterminalSymbol ->
  (start upperBound finish : Boundary tokens) -> Prop

ExactSlice :
  WorkspaceFile -> (tokens : List Token) ->
  (start finish : Boundary tokens) -> List TerminalSymbol -> Prop

ArmHeaderAt :
  WorkspaceFile -> (tokens : List Token) ->
  (regionStart cursor : Boundary tokens) -> Prop

NearestStatementRegion :
  WorkspaceFile -> (tokens : List Token) ->
  (regionStart regionEnd : Boundary tokens) -> Prop
```

`UnguardedReach file tokens` is the least relation generated by these four
rules, with every `guardOf` entry ignored:

1. `seed` inserts every production at dot zero, with equal origin/current, at
   every `Boundary tokens`;
2. `predict` inserts every dot-zero production whose `lhs` is the
   nonterminal after a reached item's dot, at that item's current boundary;
3. `scan` advances dot and current by one exactly when the current boundary is
   a `TerminalCursor`, `TerminalAt` supplies its retained token or logical
   `EOF`, and `TerminalMatches` holds for the terminal after the dot; and
4. `complete` advances a reached waiting item exactly when its next symbol is
   the `lhs` of a reached complete item and the waiting current equals the
   finished origin, retaining the waiting origin and using the finished
   current.

`UnguardedRecognizes file tokens symbol start finish` holds exactly when a
complete reached item has `production.lhs = symbol`, `origin = start`, and
`current = finish`. It takes `NonterminalSymbol`, not only `GrammarRuleId`, so
the mechanically generated `Aux` for `list1(pattern)` can be named without a
second recognition relation. `GreatestUnguardedEnd file tokens symbol start
upperBound finish` is `UnguardedRecognizes ... start finish`,
`finish.val <= upperBound.val`, and the assertion that every other recognized
end at or below that same upper bound has value at most `finish.val`. The upper
bound is part of the key; there is no open predicate argument or unnamed
delimiter restriction.

`ExactSlice file tokens start finish classes` holds exactly when
`finish.val = start.val + classes.length`, every cursor in that half-open range
is the `beforeBoundary` of a `TerminalCursor` for which `TerminalAt file tokens`
returns a retained token and `TerminalMatches` holds for the corresponding
class, and there is no
logical `EOF` member. In particular, the G07 query uses exactly
`[symbol dot, category identifier]`.

Delimiter evidence is closed over these types:

```text
DelimiterCloser = rightParen | rightBracket | rightBrace

DelimiterStack = List DelimiterCloser

DelimiterStep :
  DelimiterStack -> TokenKind -> DelimiterStack -> Prop

DelimiterRun :
  (tokens : List Token) -> DelimiterStack -> Boundary tokens ->
  Boundary tokens -> DelimiterStack -> Prop

ProtectedDelimiterRun :
  (tokens : List Token) -> NonemptyList DelimiterCloser -> Boundary tokens ->
  Boundary tokens -> NonemptyList DelimiterCloser -> Prop

MatchingDelimiter :
  (tokens : List Token) -> (open close : Boundary tokens) ->
  (opening closing : Symbol) -> Prop

SameDelimiterDepth :
  (tokens : List Token) -> Boundary tokens -> Boundary tokens -> Prop

NextSameDepthDelimiter :
  (tokens : List Token) -> Boundary tokens -> Boundary tokens ->
  NonemptyList Symbol -> Prop

SymbolAtBoundary :
  WorkspaceFile -> (tokens : List Token) ->
  Boundary tokens -> Symbol -> Prop

ImmediatelyAfterSymbol :
  WorkspaceFile -> (tokens : List Token) -> Symbol ->
  (symbolCursor after : Boundary tokens) -> Prop

ContainingBraceFrame :
  (tokens : List Token) -> (cursor open close : Boundary tokens) -> Prop

InnermostContainingBraceFrame :
  (tokens : List Token) -> (cursor open close : Boundary tokens) -> Prop

NextArmOrClose :
  WorkspaceFile -> (tokens : List Token) ->
  (regionStart close regionEnd : Boundary tokens) -> Prop
```

The only opening/closing pairs are `(`/`)`, `[`/`]`, and `{`/`}`.
`DelimiterStep` pushes the corresponding closer for an opening-symbol token,
pops only an equal closer, leaves the stack unchanged for every other token,
and has no rule for a mismatched or unmatched closer. `DelimiterRun` is the
least exact one-token-at-a-time composition of those steps. A token whose kind
is string, literal, comment-free assembly block, identifier, keyword, pragma,
or non-delimiter symbol is one unchanged-stack step. Comments are absent from
`tokens`; strings and opaque assembly tokens are never opened and inspected.

`ProtectedDelimiterRun` is the same composition with a nonempty stack before
and after every step, so it cannot consume the closer belonging to its bottom
stack entry. `MatchingDelimiter tokens open close opening closing` requires
the stated pair at `open`/`close` and a protected run from the successor of
`open` through the half-open interior to `close`, beginning and ending with
the singleton expected closer. `SameDelimiterDepth tokens start finish` is a
run from the empty stack to the empty stack. `NextSameDepthDelimiter tokens
start cursor allowed` requires `SameDelimiterDepth start cursor`, an allowed
symbol token at `cursor`, and no smaller cursor after `start` satisfying both
conditions. These clauses make every delimiter query deterministic without a
guard or parser answer.

`SymbolAtBoundary file tokens cursor symbol` holds exactly when there is a
`TerminalCursor` whose `beforeBoundary` is `cursor`, `TerminalAt` returns a
retained token there, and that token has payload `.symbol symbol`.
`ImmediatelyAfterSymbol file tokens symbol symbolCursor after` adds
`after = terminalCursor.afterBoundary` for that same cursor. It is false at
logical `EOF` and at the post-EOF boundary.

The remaining region relations are the following least closed relations; the
displayed quantifiers are part of their definitions, not implementation
guidance:

```text
ArmHeaderAt file tokens regionStart cursor iff
  regionStart.val <= cursor.val and
  SameDelimiterDepth tokens regionStart cursor and
  SymbolAtBoundary file tokens cursor pipe and
  exists patternStart arrowCursor,
    ImmediatelyAfterSymbol file tokens pipe cursor patternStart and
    NextSameDepthDelimiter
      tokens patternStart arrowCursor [fatArrow] and
    GreatestUnguardedEnd file tokens
      (NonterminalSymbol.aux matchArmPatternListSite.site)
      patternStart arrowCursor arrowCursor

ContainingBraceFrame tokens cursor open close iff
  open.val < cursor.val and cursor.val < close.val and
  MatchingDelimiter tokens open close openBrace closeBrace

InnermostContainingBraceFrame tokens cursor open close iff
  ContainingBraceFrame tokens cursor open close and
  forall otherOpen otherClose,
    ContainingBraceFrame tokens cursor otherOpen otherClose ->
      otherOpen.val <= open.val

NextArmOrClose file tokens regionStart close regionEnd iff
  regionStart.val <= regionEnd.val and regionEnd.val <= close.val and
  SameDelimiterDepth tokens regionStart regionEnd and
  (regionEnd = close or
    ArmHeaderAt file tokens regionStart regionEnd) and
  forall earlier,
    regionStart.val <= earlier.val -> earlier.val < regionEnd.val ->
    SameDelimiterDepth tokens regionStart earlier ->
    not (earlier = close or
      ArmHeaderAt file tokens regionStart earlier)

NearestStatementRegion file tokens regionStart regionEnd iff
  (exists open,
    ImmediatelyAfterSymbol file tokens openBrace open regionStart and
    MatchingDelimiter tokens open regionEnd openBrace closeBrace) or
  (exists arrow open close,
    ImmediatelyAfterSymbol file tokens fatArrow arrow regionStart and
    InnermostContainingBraceFrame tokens arrow open close and
    NextArmOrClose file tokens regionStart close regionEnd)
```

The `SameDelimiterDepth tokens regionStart cursor` premise in `ArmHeaderAt` is
essential: a pipe belonging to an inner match cannot satisfy an outer arm-body
query. The recognized nonterminal is the fixed Grammar-owned site whose exact
key is `[rule = matchArm, path = [1]]`; it cannot accidentally select either
of the other two `list1(pattern)` shapes. The innermost condition chooses the greatest containing opening-brace
cursor; `MatchingDelimiter` then fixes its close. The final universal clause
chooses the least same-depth next-arm header or that close. Nested bodies and
matches are therefore skipped. A valid `GuardAnchor` ensures that the
preceding `{` or `=>` created the retained context, but
`NearestStatementRegion` itself mentions only `file`, `tokens`, delimiter
relations, and `ArmHeaderAt`. Implementations must prove:

```text
nearest_statement_region_functional :
  NearestStatementRegion file tokens regionStart left ->
  NearestStatementRegion file tokens regionStart right ->
  left = right
```

The relation does not consult `G02`; it uses the common unguarded
`ArmHeaderAt` predicate directly. This is necessary to keep `G08` from being
circular through a guarded parse answer.

The final evidence relation is:

```text
GuardEvidence : (file : WorkspaceFile) -> (tokens : List Token) ->
  GuardInstanceKey tokens -> GuardDecision -> Prop
```

It first requires `TokensOwnedBy file tokens`. It then holds exactly for the
one row below. For the eight guards other than `G02`,
“otherwise negative” includes a missing token or incomplete named recognition.
For `G02`, a missing retained token, including the logical-EOF position, is
“not `|`” and therefore `neutral`.

| Guard | Exact `positive`, `negative`, and `neutral` evidence |
| --- | --- |
| `G01_statementIf` | `positive` exactly when `siteCursor` starts `if (` and an unguarded complete `expression` ends at the delimiter-matching `)`, immediately followed by `{`; otherwise `negative`. |
| `G02_matchArmBoundary` | `positive` exactly when `ArmHeaderAt(contextStart, siteCursor)`; `negative` exactly when the retained token at `siteCursor` is `|` but that predicate is false; `neutral` exactly when the retained token is absent or is not `|`. |
| `G03_parameterComptime` | `positive` exactly when the identifier at `siteCursor` has contextual spelling `comptime`, even if no following identifier exists; otherwise `negative`. |
| `G04_letComptime` | `positive` exactly when the identifier immediately after the colon, at `siteCursor`, has contextual spelling `comptime`; otherwise `negative`. |
| `G05_typeComptime` | `positive` exactly when the identifier at `siteCursor` has contextual spelling `comptime`, even if no following type exists; otherwise `negative`. |
| `G06_patternComptime` | `positive` exactly when `siteCursor` spells contextual `comptime` and, from its successor, the greatest unguarded complete `expression` ends at the next same-pattern-depth `,`, `)`, or `=>`; otherwise `negative`. |
| `G07_leadingDotArguments` | `positive` exactly when `ExactSlice(contextStart, siteCursor, [dot, identifier])` and the token at `siteCursor` is `(`; otherwise `negative`. |
| `G08_terminalExpression` | `positive` exactly when `NearestStatementRegion(contextStart, siteCursor)`, so the expression chosen by the expression-statement reduction ends at the nearest enclosing statement-region boundary; otherwise `negative`. |
| `G09_genericContext` | `positive` exactly when, from `siteCursor` after `forallClause`, the greatest unguarded complete nonempty `predicateList` ends immediately before `=>`; otherwise `negative`. |

Only `G02` can yield `neutral`. Thus a recognized next-arm header enables the
positive `star.nil` cell and disables the negative `star.cons` cell; a
non-header `|` does the reverse; and an ordinary non-`|` statement boundary
enables both. The last case is essential: forcing a Boolean complement there
would either prevent an arm body from ending at `}`/EOF or prevent it from
continuing with an ordinary statement.

For `G07`, the exact slice makes `.T(` positive. It makes `f(`, `f.T(`,
the second call in `.T(x)(y)`, and `.T.x(` negative. In particular, the dot
nearest the `(` in `f.T(` cannot be substituted for the enclosing-postfix
origin.

`GuardEvidence.functional` and totality on every `GuardInstanceKey` of a
well-owned `LexedModule` are required; only anchored keys can later be consumed
by a production instance.
Evidence is the least fixed point of only the unguarded finite relations named
above. It may not mention `GuardAnchor`, contextual chart reachability,
`Chart.G`, `parseTokens`, another `GuardEvidence`, resolution, or semantic
typing.

`guardOf : ProductionId -> List (PriorityGuardId × Polarity)` is total and is
nonempty exactly on these expanded choices: `G01_statementIf` guards the
`statement` paths to `ifStatement` and `expressionStatement`;
`G02_matchArmBoundary` guards the cons/nil choice of the match arm's
`armStatement*`; `G03_parameterComptime` guards the parameter's leading option;
`G04_letComptime` guards the post-colon let option; `G05_typeComptime` guards
the two `type` alternatives; `G06_patternComptime` guards the comptime and
qualified-name pattern alternatives; `G07_leadingDotArguments` guards
the leading-dot argument option and the competing first call `postfixPart`;
`G08_terminalExpression` guards the absent-semicolon branch after the selected
expression; and `G09_genericContext` guards the
generic-prefix context option. `Polarity` selects the enabled or disabled side
through `GuardDecision.allows`. Every other production has `guardOf = []`.

The exact cells, using the `GrammarSite` rule plus child-index path, are:

| Guard | Positive production cells | Negative production cells |
| --- | --- | --- |
| `G01` | `P.choice[statement, [], 3]` | `P.choice[statement, [], 10]` |
| `G02` | `P.star[matchArm, [3], nil]` | `P.star[matchArm, [3], cons]` |
| `G03` | `P.opt[parameter, [0], some]` | `P.opt[parameter, [0], none]` |
| `G04` | `P.opt[letBinding, [2,0,1], some]` | `P.opt[letBinding, [2,0,1], none]` |
| `G05` | `P.choice[type, [], 0]` | `P.choice[type, [], 1]` |
| `G06` | `P.choice[pattern, [], 3]` | `P.choice[pattern, [], 4]` |
| `G07` | `P.opt[atom, [2,2], some]` | `P.opt[atom, [2,2], none]`; `P.choice[postfixPart, [], 0]` |
| `G08` | `P.opt[expressionStatement, [1], none]` | none |
| `G09` | `P.opt[genericPrefix, [1], some]` | `P.opt[genericPrefix, [1], none]` |

This table has `H = 18` cells. It is the same executable `guardOf` table used
for coverage validation; the short `G01` through `G09` labels in this display
stand for the correspondingly numbered `PriorityGuardId` constructors.

The Phase-B state and its two independent correctness properties are defined
before any witness that refers to them:

```text
GuardMemoState = undecided | final GuardDecision

GuardMemo(tokens : List Token) =
  GuardInstanceKey tokens -> GuardMemoState

PhaseBCorrect
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens) : Prop =
  forall key decision,
    memo key = GuardMemoState.final decision iff
      GuardEvidence file tokens key decision

AllGuardsFinal {tokens : List Token} (memo : GuardMemo tokens) : Prop =
  forall key, exists decision,
    memo key = GuardMemoState.final decision
```

`ParserCore` owns `GuardMemoState`, `GuardMemo`, and the structural
`AllGuardsFinal` barrier. `ParserJudgment` owns `GuardEvidence` and
`PhaseBCorrect`, because only that relation connects a table to declarative
unguarded recognition. An executor may expose its Core memo and prove
`AllGuardsFinal`; the theorem that the executor's sealed table also satisfies
`PhaseBCorrect` belongs to `Properties.lean`, the only layer that imports both
the executor and `ParserJudgment`.

The finite witness retained by the guarded chart is not a Boolean on a raw
item. Its key is:

```text
GuardWitnessKey.Raw(tokens : List Token) = {
  productionInstance : ProductionInstanceKey tokens,
  guardInstance      : GuardInstanceKey tokens,
  polarity           : Polarity
}

GuardWitnessKey.Valid {tokens : List Token}
    (raw : GuardWitnessKey.Raw tokens) : Prop =
  (raw.guardInstance.guard, raw.polarity) in
    guardOf raw.productionInstance.production and
    GuardAnchor raw.productionInstance
      (raw.guardInstance.guard, raw.polarity) raw.guardInstance

GuardWitnessKey (tokens : List Token) =
  { raw : GuardWitnessKey.Raw tokens // GuardWitnessKey.Valid raw }
```

`GuardWitnessKey.productionInstance`, `.guardInstance`, and `.polarity` are
the transparent projections through `.val`. `ParserCore` owns the raw key,
validity predicate, checked subtype, and its `Repr`, `BEq`, and
`DecidableEq`; the proof field is proof-irrelevant. `Chart.G` and
`parseTokens` store only this Core-owned checked key. They do not store a
`GuardEvidence` or judgment-owned `GuardWitness` value.

A witness value and production enablement have these complete signatures:

```text
GuardWitness
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (allFinal : AllGuardsFinal memo)
    (key : GuardWitnessKey tokens) : Prop =
  exists decision : GuardDecision,
    memo key.guardInstance = GuardMemoState.final decision and
    GuardEvidence file tokens key.guardInstance decision and
    decision.allows key.polarity = true

EnabledProductionInstance
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (allFinal : AllGuardsFinal memo)
    (instance : ProductionInstanceKey tokens) : Prop =
  forall guard polarity,
    (guard, polarity) in guardOf instance.production ->
    exists witnessKey : GuardWitnessKey tokens,
      witnessKey.productionInstance = instance and
      witnessKey.guardInstance.guard = guard and
      witnessKey.polarity = polarity and
      GuardWitness file tokens memo correct allFinal witnessKey
```

Here `correct` and `allFinal` are explicit parameters; the key's proof
field is the exact membership-and-anchor validity premise just displayed. A
`ProductionInstanceKey` is enabled
exactly when such a witness exists for every cell in its `guardOf` list.
Unguarded production instances are enabled vacuously. Witness keys are
inserted and looked up by their complete production/context/guard identity;
erasing either context boundary before the lookup is nonconforming.
`GuardWitness` is deliberately a proposition, not a Type-valued record used as
a proposition. Its existential decision remains inside `Prop`; neither
`EnabledProductionInstance` nor contextual reach eliminates it to construct a
semantic value. The executable constructs its stored `GuardWitnessKey` and
final decision directly from the sealed Phase-B table, and correspondence
proves the displayed proposition afterward.

The public guard schedule is a strict three-phase algorithm. Its Phase-C reach
signature is:

```text
ContextualReach
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
  ContextualItemKey tokens -> Prop
```

`PhaseBCorrect` states that every finalized cell has exactly its declarative
evidence and that every declaratively evidenced decision is the stored one.
`AllGuardsFinal` states only the scheduling barrier. These propositions are
deliberately separate: a table filled with `final neutral` satisfies the
second and generally violates the first. Both derivations are explicit
parameters of the Phase C reach relation and of every contextual packed-edge
constructor. Neither may be recovered from an existential lookup for one key,
and Phase C may not replace `PhaseBCorrect` by functionality or totality of
`GuardEvidence` alone.

1. **Phase A — universal unguarded saturation.** Initialize the raw dot-zero
   production at every boundary for every expanded nonterminal and compute one
   least raw predict/scan/complete fixed point with `guardOf` ignored. This
   single universal span chart defines every `UnguardedRecognizes`, greatest
   end, delimiter, and `ArmHeaderAt` lookup used by guard evidence. It is fully
   saturated before Phase B begins and is never recomputed for a guard ID,
   guard instance, production instance, or context.
2. **Phase B — decision finalization.** Allocate one `undecided` cell for every
   finite `GuardInstanceKey`, in its displayed lexicographic order. Reading
   only Phase A's saturated tables and retained tokens, replace each cell
   exactly once by its unique final decision. Extensionally that decision is
   the one specified by `GuardEvidence`; executors compute it from their
   Phase-A indexes without importing that judgment, and `Properties.lean`
   proves the equivalence. The completed table must separately satisfy
   `PhaseBCorrect` and `AllGuardsFinal` at the declarative interface. Finish
   the entire table, including
   every anchored key, before Phase C begins. This phase creates no `ProductionInstanceKey`,
   `GuardWitnessKey`, contextual item, contextual edge, AST value, or parse
   diagnostic.
3. **Phase C — guarded contextual saturation and reduction.** In the
   declarative relation, given explicit proofs of both `PhaseBCorrect` and
   `AllGuardsFinal`, start the one contextual
   module chart in `plain`. Prediction forms a production instance,
   obtains its unique anchor, reads only a `final` Phase B cell, applies
   `Polarity.accepts`, and creates the corresponding guard witness only when
   the polarity is accepted. Compute the contextual fixed point once, then
   compute its contextual diagnostic frontier or reduce its unique root.

Phase order is part of `Chart.G`, not an implementation optimization. No
declarative Phase C reachability, edge-validity, reduction, frontier, or
diagnostic fact may exist without both Phase B proofs. Executable Chart/Fast
Phase C is blocked by its Core-owned sealed-final state; it never imports or
constructs `PhaseBCorrect`. `Properties.lean` proves that the sealed executor
memo satisfies `PhaseBCorrect` and maps that run into the declarative Phase C
relation. Neither form of Phase C may begin while any Phase B cell is
`undecided`.
`undecided` is an internal scheduler state, never `negative`, `neutral`, a
source diagnostic, or evidence for either polarity. A missing or provisional
decision cannot enable a production and cannot enter `ContextualReach`.
Likewise, Phase C may only look up Phase A/B results; it may not start another
unguarded subchart or revise a finalized decision.

The table is exhaustive; no parser-combinator commit order is part of m2c-v1.

The normative reference parser is `Multi.Chart.G`. For an input containing
`n` retained tokens, let `terminalStream` append one logical `EOF`, let
`T = n + 1`, and number its `T + 1` boundaries from zero through `T`. The
chart uses the `ParserCore` carriers already defined above; it does not
redeclare private executor variants of them.

```text
NextSymbol {tokens : List Token}
    (item : DottedItem tokens) (symbol : GrammarSymbol) : Prop =
  item.dot.val < item.production.rhs.length and
  item.production.rhs[item.dot.val]? = some symbol

CompleteItem {tokens : List Token} (item : DottedItem tokens) : Prop =
  item.dot.val = item.production.rhs.length

AdvanceItem {tokens : List Token}
    (before : DottedItem tokens) (next : Boundary tokens)
    (after : DottedItem tokens) : Prop =
  after.production = before.production and
  after.dot.val = before.dot.val + 1 and
  after.origin = before.origin and
  after.current = next

prefix_zero_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (zero : item.dot.val = 0) :
  [] = item.production.rhs.take item.dot.val

prefix_scan_layout
    {tokens : List Token}
    (before after : DottedItem tokens)
    (terminal : TerminalSymbol)
    (nextBoundary : Boundary tokens)
    (next : NextSymbol before (GrammarSymbol.terminal terminal))
    (advance : AdvanceItem before nextBoundary after) :
  before.production.rhs.take before.dot.val ++
      [GrammarSymbol.terminal terminal] =
    after.production.rhs.take after.dot.val

prefix_complete_layout
    {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (next : NextSymbol waiting
      (GrammarSymbol.nonterminal finished.production.lhs))
    (advance : AdvanceItem waiting finished.current after) :
  waiting.production.rhs.take waiting.dot.val ++
      [GrammarSymbol.nonterminal finished.production.lhs] =
    after.production.rhs.take after.dot.val

prefix_full_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (complete : CompleteItem item) :
  item.production.rhs.take item.dot.val = item.production.rhs

canonicalCompleteRootItem_complete
    {tokens : List Token} (rule : GrammarRuleId)
    (origin finish : Boundary tokens) (context : GuardContext tokens) :
  CompleteItem
    (CanonicalCompleteRootItem
      tokens rule origin finish context).raw

PackedEdgeKey.Valid
    (file : WorkspaceFile) (tokens : List Token)
    (key : PackedEdgeKey tokens) : Prop =
  | scanned before after terminalCursor =>
      exists terminal value span,
        NextSymbol before (terminal terminal) and
        terminalCursor.beforeBoundary = before.current and
        TerminalAt file tokens terminalCursor value span and
        TerminalMatches terminal value and
        AdvanceItem before terminalCursor.afterBoundary after
  | completed waiting finished after sharedCursor =>
      exists symbol,
        NextSymbol waiting (nonterminal symbol) and
        CompleteItem finished and
        finished.production.lhs = symbol and
        waiting.current = sharedCursor and
        finished.origin = sharedCursor and
        AdvanceItem waiting finished.current after

ScannedEdgeWitness
    (file : WorkspaceFile) (tokens : List Token)
    (before after : DottedItem tokens)
    (cursor : TerminalCursor tokens) = {
  terminal : TerminalSymbol,
  matched  : MatchedTerminal file tokens terminal,
  sameCursor : matched.cursor = cursor,
  next     : NextSymbol before (GrammarSymbol.terminal terminal),
  atCurrent : cursor.beforeBoundary = before.current,
  advance  : AdvanceItem before matched.cursor.afterBoundary after
}

CompletedEdgeWitness
    (tokens : List Token)
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) = {
  next : NextSymbol waiting
    (GrammarSymbol.nonterminal finished.production.lhs),
  complete : CompleteItem finished,
  waitingAtShared : waiting.current = shared,
  finishedAtShared : finished.origin = shared,
  advance : AdvanceItem waiting finished.current after
}

packedEdge_scanned_valid_iff
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens} {cursor : TerminalCursor tokens} :
  PackedEdgeKey.Valid file tokens (.scanned before after cursor) iff
    Nonempty (ScannedEdgeWitness file tokens before after cursor)

packedEdge_completed_valid_iff
    {file : WorkspaceFile} {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens} :
  PackedEdgeKey.Valid file tokens
    (.completed waiting finished after shared) iff
      Nonempty
        (CompletedEdgeWitness tokens waiting finished after shared)

PackedEdge (file : WorkspaceFile) (tokens : List Token) =
  { key : PackedEdgeKey tokens // PackedEdgeKey.Valid file tokens key }

ContextualPackedEdgeKey.rawProjection :
  {tokens : List Token} ->
  ContextualPackedEdgeKey tokens -> PackedEdgeKey tokens
  | scanned before after cursor =>
      PackedEdgeKey.scanned before.raw after.raw cursor
  | completed waiting finished after shared =>
      PackedEdgeKey.completed waiting.raw finished.raw after.raw shared

ContextualPackedEdgeKey.StructurallyValid
    (file : WorkspaceFile) (tokens : List Token)
    (key : ContextualPackedEdgeKey tokens) : Prop =
  PackedEdgeKey.Valid file tokens key.rawProjection and
  match key with
  | scanned before after _ =>
      before.context = after.context
  | completed waiting finished after _ =>
      finished.context =
        descendContext waiting finished.raw.production and
      after.context = waiting.context

StructurallyValidContextualPackedEdge
    (file : WorkspaceFile) (tokens : List Token) =
  { key : ContextualPackedEdgeKey tokens //
      ContextualPackedEdgeKey.StructurallyValid file tokens key }

ContextualEdgeReach
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
  ContextualPackedEdgeKey tokens -> Prop

Predict(item) =
  if item.raw.next is nonterminal X, form each production instance for X
  with origin = item.raw.current and context = descendContext(item, production),
  and add its dot-zero contextual item exactly when that complete production
  instance is enabled

Scan(item) =
  if item.raw.next is terminal k and
     terminalStream[item.raw.current] matches k,
  add the same contextual item with its raw dot and current advanced by one

Complete(waiting, finished) =
  if waiting.raw.next is finished.raw.lhs and
     waiting.raw.current = finished.raw.origin and finished.raw is complete and
     finished.context =
       descendContext(waiting, finished.raw.production),
  add waiting with its raw dot advanced and
    current = finished.raw.current and context = waiting.context
```

`TerminalCursor.afterBoundary` is the unique successor boundary, including
when the scanned terminal is logical `EOF`. The terminal cursor is therefore the exact
pre-scan boundary and scanning `EOF` reaches the final boundary. These
relations are proof-free predicates owned by `ParserCore`; the two structural
subtype aliases retain their proofs only as erased validity certificates.
`ContextualEdgeReach` is instead owned by `ParserJudgment`, so `ParserCore`
never imports a judgment relation.

The four `prefix_*_layout` results and
`canonicalCompleteRootItem_complete` are public checked theorems in
`ParserCore`. They are proved only from `List.take_zero`, `List.take_succ`,
`List.take_eq_self`, `NextSymbol`, and `AdvanceItem`, with equality
substitution for production/dot fields. They are not axioms stored in an edge,
and their proofs contain no `Classical.choice` or unchecked cast.

The raw `DottedItem` and `PackedEdgeKey` algebras above are unchanged and remain
the grammar-audit projections. They are not sufficient semantic deduplication
keys. The contextual scanned constructor requires equal before/after contexts.
The contextual completed constructor requires exactly the `Complete` context
equations above. Its raw projection is the displayed raw `PackedEdgeKey`, but
two contextual edges with the same raw projection remain distinct.

After Phase A is saturated and Phase B proves both `PhaseBCorrect` and
`AllGuardsFinal`, Phase C of `G`
starts with `P.root[GrammarRuleId.module]` at origin/current zero in context
`plain`. It
computes the least set closed under contextual `Predict`, `Scan`, and
`Complete`, retaining `ContextualPackedEdgeKey` action edges by stable
`ActionId` and retaining the separate `GuardWitnessKey` set. A scanned
`ContextualEdgeReach` constructor requires reached `before`, structural
validity, and then derives reached `after`; a completed constructor requires
reached `waiting` and `finished`, structural validity, and then derives reached
`after`. Thus every retained edge is structurally valid and all endpoint items
belong to the same least Phase C closure; an unreached `after` cannot be
admitted by constructing a structural subtype. The Phase C executable
uses an ordered finite worklist: each contextual item and contextual edge is
dequeued once; each production instance and guard-witness key is activated or
inserted once; each compatible prediction, scan, and completion key is
attempted once; and duplicate insertion is ignored.

Prediction is the only operation that creates a child context. Scan preserves
it. Complete may consume only a finished item carrying the context produced by
that exact waiting item and then restores the waiting context. In particular,
the implementation must not define a raw predicate such as
`ViableReach item := exists context, ContextualReach { raw := item, context }`
and then use two independent witnesses from it in prediction, completion,
reduction, or diagnostics. A raw item reached once under `.postfixInvocation`
for `.T(` and once under another postfix origin is two keys, as are their
completed edges. Raw projection may be used only after a complete coherent
contextual derivation has been selected.

The semantic carrier is indexed by the finite grammar rather than erased to
`Any`, `Dynamic`, or an executor callback. `ParserCore` owns the following
carrier types. `OptionalCommaValue` and `PostfixPartValue` are the only
non-AST root values:

```text
OptionalCommaValue = absent | present SourceSpan

PostfixPartValue =
  | call   (openParen : SourceSpan) (arguments : List Expression)
           (closeParen : SourceSpan)
  | select (dot : SourceSpan) (field : IdentifierOccurrence)
  | index  (openBracket : SourceSpan) (index : Expression)
           (closeBracket : SourceSpan)

RuleValue : GrammarRuleId -> Type
  | module                  => ParsedModuleV1
  | topItem                 => TopItem
  | moduleRef               => ModuleReference
  | importDecl              => ImportDecl
  | importEntry             => ImportSelectorEntry
  | hidingClause            => HidingClause
  | exportDecl              => ExportDecl
  | localExportEntry        => ExportEntry
  | remoteExportEntry       => RemoteExportEntry
  | exportItem              => ExportItem
  | constructorSelection    => ConstructorSelection
  | pragmaDecl              => PragmaDecl
  | genericPrefix           => GenericPrefix
  | forallClause            => ForallClause
  | forallBinder            => ForallBinder
  | optionalComma           => OptionalCommaValue
  | predicateList           => NonemptyList Predicate
  | predicate               => Predicate
  | functionSignature       => FunctionSignature
  | functionDecl            => FunctionDecl
  | classMethod             => ClassMethodDecl
  | dataDecl                => DataDecl
  | dataConstructor         => DataConstructor
  | typeAliasDecl           => TypeAliasDecl
  | classDecl               => ClassDecl
  | instanceDecl            => InstanceDecl
  | instanceMethod          => FunctionDecl
  | contractDecl            => ContractDecl
  | contractMember          => ContractMember
  | fieldDecl               => FieldDecl
  | fallbackDecl            => FallbackDecl
  | contractConstructorDecl => ContractConstructorDecl
  | parameter               => Parameter
  | body                    => Body
  | type                    => TypeExpr
  | typeAtom                => TypeExpr
  | qualifiedName           => QualifiedName
  | statement               => Statement
  | letStatement            => Statement
  | letBinding              => LetBinding
  | returnStatement         => Statement
  | blockStatement          => Statement
  | breakStatement          => Statement
  | continueStatement       => Statement
  | assemblyStatement       => Statement
  | ifStatement             => Statement
  | forStatement            => Statement
  | forInitItem             => ForInitItem
  | forPostItem             => ForPostItem
  | matchStatement          => Statement
  | matchArm                => MatchArm
  | armStatement            => Statement
  | assignmentStatement     => Statement
  | assignmentOperator      => Located AssignmentOperator
  | expressionStatement     => Statement
  | terminalExpression      => Expression
  | pattern                 => Pattern
  | expression              => Expression
  | annotation              => Expression
  | conditional             => Expression
  | logicalOr               => Expression
  | logicalAnd              => Expression
  | equality                => Expression
  | relational              => Expression
  | bitOr                   => Expression
  | bitXor                  => Expression
  | bitAnd                  => Expression
  | additive                => Expression
  | multiplicative          => Expression
  | prefix                  => Expression
  | postfix                 => Expression
  | postfixPart             => PostfixPartValue
  | atom                    => Expression
  | lambda                  => Expression
  | literal                 => Literal
```

This definition has exactly one equation for each of the 75 constructors of
`GrammarRuleId`, in their displayed order. An exhaustiveness theorem compares
its equation tags with `allGrammarRuleIds`; a wildcard equation is forbidden.

The EBNF value family preserves the raw products, options, and lists displayed
below. It is **not** a naive structural mutual definition: Lean 4.32 does not
accept the recursive occurrence at `branches.get branch` as a structural
subterm, and a nested indexed inductive is rejected when a `List` parameter
contains the local expression index. `ParserCore` therefore uses this one
explicit well-founded family:

```text
ebnfSize : EbnfExpr -> Nat
  | atom _            => 1
  | sequence children => 1 + (children.map ebnfSize).sum
  | group child       => 1 + ebnfSize child
  | choice branches   => 1 + (branches.map ebnfSize).sum
  | optional child    => 1 + ebnfSize child
  | star child        => 1 + ebnfSize child
  | plus child        => 1 + ebnfSize child
  | list0 element     => 1 + ebnfSize element
  | list1 element     => 1 + ebnfSize element

UnaryEbnfKind = group | optional | star | plus | list0 | list1

UnaryEbnfKind.apply : UnaryEbnfKind -> EbnfExpr -> EbnfExpr
  | group, child    => EbnfExpr.group child
  | optional, child => EbnfExpr.optional child
  | star, child     => EbnfExpr.star child
  | plus, child     => EbnfExpr.plus child
  | list0, child    => EbnfExpr.list0 child
  | list1, child    => EbnfExpr.list1 child

EbnfValueIndex =
  | expression  EbnfExpr
  | expressions (List EbnfExpr)

EbnfValueIndex.measure : EbnfValueIndex -> Nat
  | expression expression => 2 * ebnfSize expression
  | expressions values    => 2 * (values.map ebnfSize).sum + 1

EbnfFamily (file : WorkspaceFile) (tokens : List Token) :
    (index : EbnfValueIndex) -> Type
  | expression (atom (terminal terminal)) =>
      MatchedTerminal file tokens terminal
  | expression (atom (nonterminal rule)) => RuleValue rule
  | expression (sequence children) =>
      EbnfFamily file tokens (expressions children)
  | expression (group child) =>
      EbnfFamily file tokens (expression child)
  | expression (choice branches) =>
      (branch : Fin branches.length) ×
        EbnfFamily file tokens (expression (branches.get branch))
  | expression (optional child) =>
      Option (EbnfFamily file tokens (expression child))
  | expression (star child) =>
      List (EbnfFamily file tokens (expression child))
  | expression (plus child) =>
      NonemptyList (EbnfFamily file tokens (expression child))
  | expression (list0 element) =>
      List (EbnfFamily file tokens (expression element))
  | expression (list1 element) =>
      NonemptyList (EbnfFamily file tokens (expression element))
  | expressions [] => Unit
  | expressions (child :: rest) =>
      EbnfFamily file tokens (expression child) ×
        EbnfFamily file tokens (expressions rest)
termination_by index => EbnfValueIndex.measure index

EbnfValue (file : WorkspaceFile) (tokens : List Token)
          (expression : EbnfExpr) : Type =
  EbnfFamily file tokens (EbnfValueIndex.expression expression)

EbnfValues (file : WorkspaceFile) (tokens : List Token)
           (expressions : List EbnfExpr) : Type =
  EbnfFamily file tokens (EbnfValueIndex.expressions expressions)
```

The termination proof is part of this definition. `ParserCore` proves
`ebnfSize_positive` and the following strict-decrease lemmas from it,
`List.get_mem`, and the mapped-sum membership bound:

```text
measure_sequence_lt (children : List EbnfExpr) :
  measure (.expressions children) < measure (.expression (.sequence children))
measure_choice_get_lt (branches : List EbnfExpr)
                      (branch : Fin branches.length) :
  measure (.expression (branches.get branch)) <
    measure (.expression (.choice branches))
measure_unary_child_lt (kind : UnaryEbnfKind) (child : EbnfExpr) :
  measure (.expression child) < measure (.expression (kind.apply child))
measure_cons_head_lt (child : EbnfExpr) (rest : List EbnfExpr) :
  measure (.expression child) < measure (.expressions (child :: rest))
measure_cons_tail_lt (child : EbnfExpr) (rest : List EbnfExpr) :
  measure (.expressions rest) < measure (.expressions (child :: rest))
```

Here `kind` in `measure_unary_child_lt` has the closed constructors
`group | optional | star | plus | list0 | list1`; `kind.apply` is their total
case split, not an arbitrary function. The `decreasing_by` block uses exactly
these lemmas in the corresponding equations. No opaque recursion escape,
unchecked code-generation escape, assumed theorem, or compiler acceptance of
a hidden structural recursion is permitted.
`ParserCore` also exports `[simp]` equation theorems for both atom cases,
sequence, group, choice, optional, star, plus, list0, list1,
`EbnfValues []`, and `EbnfValues (child :: rest)`. Those twelve theorems have
exactly the right-hand-side types displayed above and are proved from the
well-founded equation theorem. They are the only reductions used by the
action constructors, so the choice index always retains its
`Fin branches.length` proof.

The remaining indexed value carriers are:

```text

NonterminalValue (file : WorkspaceFile) (tokens : List Token) :
    NonterminalSymbol -> Type
  | rule rule => RuleValue rule
  | aux site  => EbnfValue file tokens site.expression
  | tail site =>
      List (EbnfValue file tokens site.element.expression)

GrammarSymbolValue (file : WorkspaceFile) (tokens : List Token) :
    GrammarSymbol -> Type
  | terminal terminal       => MatchedTerminal file tokens terminal
  | nonterminal nonterminal => NonterminalValue file tokens nonterminal

GrammarSymbolValues (file : WorkspaceFile) (tokens : List Token) :
    List GrammarSymbol -> Type
  | []             => Unit
  | symbol :: rest =>
      GrammarSymbolValue file tokens symbol ×
        GrammarSymbolValues file tokens rest

GrammarSymbolValues.append
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol} :
  GrammarSymbolValues file tokens left ->
  GrammarSymbolValues file tokens right ->
  GrammarSymbolValues file tokens (left ++ right)

GrammarSymbolValues.transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol}
    (equality : left = right) :
  GrammarSymbolValues file tokens left ->
  GrammarSymbolValues file tokens right :=
  Eq.mp
    (congrArg (GrammarSymbolValues file tokens) equality)

PrefixValues
    (file : WorkspaceFile) (tokens : List Token)
    (item : ContextualItemKey tokens) =
  GrammarSymbolValues file tokens
    (item.raw.production.rhs.take item.raw.dot.val)

PrefixValues.zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
  PrefixValues file tokens item :=
  GrammarSymbolValues.transport
    (prefix_zero_layout item.raw zero) ()

PrefixValues.scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (GrammarSymbol.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw
      matched.cursor.afterBoundary after.raw)
    (prior : PrefixValues file tokens before) :
  PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_scan_layout before.raw after.raw terminal
      matched.cursor.afterBoundary next advance)
    (GrammarSymbolValues.append prior (matched, ()))

PrefixValues.completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (GrammarSymbol.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (prior : PrefixValues file tokens waiting)
    (value : NonterminalValue file tokens
      finished.raw.production.lhs) :
  PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_complete_layout waiting.raw finished.raw after.raw next advance)
    (GrammarSymbolValues.append prior (value, ()))

PrefixValues.fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (prior : PrefixValues file tokens item) :
  GrammarSymbolValues file tokens item.raw.production.rhs :=
  GrammarSymbolValues.transport
    (prefix_full_layout item.raw complete) prior
```

`site.element` is the public total element projection certified by the
`ListSite` subtype; its proof is part of the index, not a fallible lookup.
Terminal values always retain `MatchedTerminal`, including logical `EOF`; the
EOF value has exactly the empty file-end span defined above.

`GrammarSymbolValues.transport` is exactly `Eq.mp` on a checked list-index
equality. The four `PrefixValues` helpers invoke it only with the named
theorem-derived layouts above. `zeroValue` transports the unique empty HList;
`scanValue` appends the exact matched terminal; `completeValue` appends the
finished nonterminal value; and `fullValue` transports a complete prefix to
the full production RHS. None relies on proof irrelevance, an assumed
equation, choice from a proposition, or an unchecked representation cast.

The same checked-transport discipline closes every expanded action.
`ParserCore` owns these total operations; every index that is not an ordinary
argument is still bound explicitly so the signatures remain valid under
`set_option autoImplicit false`:

```text
EbnfValue.transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (equality : left = right) :
  EbnfValue file tokens left -> EbnfValue file tokens right :=
  Eq.mp (congrArg (EbnfValue file tokens) equality)

EbnfValue.atShape
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression) :
  EbnfValue file tokens site.expression ->
  EbnfValue file tokens expression :=
  EbnfValue.transport shape

EbnfValue.ofShape
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression) :
  EbnfValue file tokens expression ->
  EbnfValue file tokens site.expression :=
  EbnfValue.transport shape.symm

EbnfValue.terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) :
  MatchedTerminal file tokens terminal ->
  EbnfValue file tokens (EbnfExpr.atom (.terminal terminal))

EbnfValue.ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) :
  RuleValue rule ->
  EbnfValue file tokens (EbnfExpr.atom (.nonterminal rule))

EbnfValue.sequence
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr) :
  EbnfValues file tokens children ->
  EbnfValue file tokens (EbnfExpr.sequence children)

EbnfValue.group
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
  EbnfValue file tokens child ->
  EbnfValue file tokens (EbnfExpr.group child)

EbnfValue.choice
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr) :
  ((branch : Fin branches.length) ×
    EbnfValue file tokens (branches.get branch)) ->
  EbnfValue file tokens (EbnfExpr.choice branches)

EbnfValue.optional
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
  Option (EbnfValue file tokens child) ->
  EbnfValue file tokens (EbnfExpr.optional child)

EbnfValue.star
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
  List (EbnfValue file tokens child) ->
  EbnfValue file tokens (EbnfExpr.star child)

EbnfValue.plus
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
  NonemptyList (EbnfValue file tokens child) ->
  EbnfValue file tokens (EbnfExpr.plus child)

EbnfValue.list0
    {file : WorkspaceFile} {tokens : List Token}
    (element : EbnfExpr) :
  List (EbnfValue file tokens element) ->
  EbnfValue file tokens (EbnfExpr.list0 element)

EbnfValue.list1
    {file : WorkspaceFile} {tokens : List Token}
    (element : EbnfExpr) :
  NonemptyList (EbnfValue file tokens element) ->
  EbnfValue file tokens (EbnfExpr.list1 element)

GrammarSymbolValues.view
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs) :
  GrammarSymbolValues file tokens production.rhs ->
  GrammarSymbolValues file tokens canonicalRhs :=
  GrammarSymbolValues.transport layout

EbnfValues.ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (sites : List GrammarSite) :
  GrammarSymbolValues file tokens
    (sites.map (fun site =>
      GrammarSymbol.nonterminal (.aux site))) ->
  EbnfValues file tokens
    (sites.map GrammarSite.expression)

RootAction.unpack
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) :
  GrammarSymbolValues file tokens (ProductionId.root rule).rhs ->
  EbnfValue file tokens (m2cV1.rhs rule)

AtomSite.pack
    {file : WorkspaceFile} {tokens : List Token} (site : AtomSite) :
  GrammarSymbolValues file tokens (ProductionId.atom site).rhs ->
  NonterminalValue file tokens (ProductionId.atom site).lhs

SequenceSite.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : SequenceSite) :
  GrammarSymbolValues file tokens (ProductionId.seq site).rhs ->
  NonterminalValue file tokens (ProductionId.seq site).lhs

GroupSite.pack
    {file : WorkspaceFile} {tokens : List Token} (site : GroupSite) :
  GrammarSymbolValues file tokens (ProductionId.group site).rhs ->
  NonterminalValue file tokens (ProductionId.group site).lhs

ChoiceSite.pack
                {file : WorkspaceFile} {tokens : List Token}
                (site : ChoiceSite)
                (branch : Fin site.branchCount) :
  GrammarSymbolValues file tokens
    (ProductionId.choice site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.choice site branch).lhs

OptionalSite.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite) (branch : OptionalBranch) :
  GrammarSymbolValues file tokens
    (ProductionId.opt site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.opt site branch).lhs

StarSite.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : StarSite) (branch : NilConsBranch) :
  GrammarSymbolValues file tokens
    (ProductionId.star site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.star site branch).lhs

PlusSite.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : PlusSite) (branch : OneConsBranch) :
  GrammarSymbolValues file tokens
    (ProductionId.plus site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.plus site branch).lhs

List0Site.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : List0Site) (branch : NilConsBranch) :
  GrammarSymbolValues file tokens
    (ProductionId.list0 site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.list0 site branch).lhs

List1Site.pack
    {file : WorkspaceFile} {tokens : List Token} (site : List1Site) :
  GrammarSymbolValues file tokens (ProductionId.list1 site).rhs ->
  NonterminalValue file tokens (ProductionId.list1 site).lhs

ListSite.pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : ListSite) (branch : NilConsBranch) :
  GrammarSymbolValues file tokens
    (ProductionId.tail site branch).rhs ->
  NonterminalValue file tokens
    (ProductionId.tail site branch).lhs
```

`EbnfValues.ofAuxiliaries` is structural recursion on `sites`. Its empty and
cons equations use the checked `EbnfValues` family equations; the cons equation
preserves the head and recursively converts the tail. It is the only bridge
from the sequence action's HList indexed by
`sites.map (nonterminal . aux)` to the EBNF HList indexed by
`sites.map GrammarSite.expression`.

For each packer, first apply `GrammarSymbolValues.view` with the corresponding
named theorem `ProductionId.rhs_root`, `rhs_atom`, `rhs_seq`, `rhs_group`,
`rhs_choice`, `rhs_opt_none`, `rhs_opt_some`, `rhs_star_nil`,
`rhs_star_cons`, `rhs_plus_one`, `rhs_plus_cons`, `rhs_list0_nil`,
`rhs_list0_cons`, `rhs_list1`, `rhs_tail_nil`, or `rhs_tail_cons`. These
theorems are oriented from the actual production RHS to the canonical RHS, so
the input transport is never reversed implicitly. Output at an auxiliary site
uses `EbnfValue.ofShape` with the site's public outer-expression equation.
The required checked result equations are exactly:

| Required theorem | Canonical result (`RootAction` directly; auxiliary output after its `EbnfValue.atShape`) |
| --- | --- |
| `RootAction.unpack_eq R` | View `rhs_root`; take its one child at `GrammarSite.root R`; transport it forward with `GrammarSite.root_expression : root.expression = m2cV1.rhs R`. |
| `AtomSite.pack_terminal_eq s` | View `rhs_atom`; use `AtomSite.symbol_eq`; the one `MatchedTerminal` becomes the terminal-atom family value; then transport backward with `AtomSite.expression_eq_atom`. |
| `AtomSite.pack_rule_eq s` | View `rhs_atom`; use `AtomSite.symbol_eq`; the one `RuleValue R` becomes the nonterminal-atom family value; then transport backward with `AtomSite.expression_eq_atom`. |
| `SequenceSite.pack_eq s` | View `rhs_seq`; apply `EbnfValues.ofAuxiliaries s.children`; apply the checked sequence-family constructor; then transport backward with `SequenceSite.expression_eq_sequence`. |
| `GroupSite.pack_eq s` | View `rhs_group`; take the one value at `s.child`; apply the checked group-family constructor; then transport backward with `GroupSite.expression_eq_group`. |
| `ChoiceSite.pack_eq s i` | View `rhs_choice`; take the child at `(s.branch i).expression`; transport it forward by `(s.branch_expression i).trans((s.branch_get_toList i).symm)` to `s.branchExpressions.toList.get (s.branchListIndex i)`; tag it with exactly `s.branchListIndex i`; apply the checked choice-family constructor; then transport backward with `ChoiceSite.expression_eq_choice`. |
| `OptionalSite.pack_none_eq s` | View `rhs_opt_none`; construct the checked optional-family `none`; transport backward with `OptionalSite.expression_eq_optional`. |
| `OptionalSite.pack_some_eq s` | View `rhs_opt_some`; take the one value at `s.child`; construct `some child`; transport backward with `OptionalSite.expression_eq_optional`. |
| `StarSite.pack_nil_eq s` | View `rhs_star_nil`; construct the checked star-family `[]`; transport backward with `StarSite.expression_eq_star`. |
| `StarSite.pack_cons_eq s` | View `rhs_star_cons`; take `head` at `s.child`, view the recursively reduced auxiliary at `s.site` forward with `StarSite.expression_eq_star`, construct `head :: tail`, then transport backward with that same site equation. |
| `PlusSite.pack_one_eq s` | View `rhs_plus_one`; construct `NEL(child, [])`; transport backward with `PlusSite.expression_eq_plus`. |
| `PlusSite.pack_cons_eq s` | View `rhs_plus_cons`; view the recursive auxiliary forward with `PlusSite.expression_eq_plus`, prepend the new child to its nonempty value, then transport backward with that equation. |
| `List0Site.pack_nil_eq s` | View `rhs_list0_nil`; construct `[]`; transport backward with `List0Site.expression_eq_list0`. |
| `List0Site.pack_cons_eq s` | View `rhs_list0_cons`; take the child and exact `Tail(ListSite.list0 s)` list, use `ListSite.element_list0`, construct `head :: tail`, then transport backward with `List0Site.expression_eq_list0`. |
| `List1Site.pack_eq s` | View `rhs_list1`; take the child and exact `Tail(ListSite.list1 s)` list, use `ListSite.element_list1`, construct `NEL(head, tail)`, then transport backward with `List1Site.expression_eq_list1`. |
| `ListSite.pack_nil_eq s` | View `rhs_tail_nil`; return `[]` at `s.element.expression`. |
| `ListSite.pack_cons_eq s` | View `rhs_tail_cons`; retain the exact matched comma premise, take the child at `s.element` and the recursive `Tail(s)` list, and return `head :: tail`. |

Every sentence in the result column is a required `[simp]` equation theorem
for the named total function, not implementation commentary. In particular,
the choice result stores `s.branchListIndex i`, whose target is
`Fin s.branchExpressions.toList.length`; it never stores `i` at that different
index. The two public equations for `branchListIndex` prove that the tag and
selected child are exactly the original displayed branch. These functions and
equations were checked in Lean 4.32.1 with a well-founded EBNF carrier,
including the recursive sequence conversion and the dependent choice
`Vector`/`List` index transport.

`ParserJudgment` owns the two independent reduction relations:

```text
RuleReduction :
  (file : WorkspaceFile) -> (tokens : List Token) ->
  (rule : GrammarRuleId) -> (origin finish : Boundary tokens) ->
  EbnfValue file tokens (m2cV1.rhs rule) -> RuleValue rule -> Prop

ActionReduces :
  (file : WorkspaceFile) -> (tokens : List Token) ->
  (action : ActionId) -> (origin finish : Boundary tokens) ->
  GrammarSymbolValues file tokens action.production.rhs ->
  NonterminalValue file tokens action.production.lhs -> Prop

RuleReductionReady
    (file : WorkspaceFile) (tokens : List Token)
    (rule : GrammarRuleId) (origin finish : Boundary tokens) : Prop =
  TokensOwnedBy file tokens and
  origin.val <= finish.val and
  (rule = GrammarRuleId.module ->
    origin = Boundary.start tokens and
    finish = Boundary.afterLogicalEOF tokens)

ActionReductionReady
    (file : WorkspaceFile) (tokens : List Token)
    (action : ActionId) (origin finish : Boundary tokens) : Prop =
  match action.production with
  | ProductionId.root rule =>
      RuleReductionReady file tokens rule origin finish
  | _ => True
```

Neither relation takes `GuardContext`; this makes reduction independent of an
outer context by construction. `ActionReduces` is the least relation with
exactly these eleven constructor families, one for each `ProductionId` shape:

```text
section ActionReducesConstructors

variable {file : WorkspaceFile} {tokens : List Token}

ActionReduces.root
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs)
    (output : RuleValue rule)
    (reduces : RuleReduction file tokens rule origin finish
      (RootAction.unpack rule input) output) :
  ActionReduces file tokens (.actionFor (.root rule))
    origin finish input output

ActionReduces.atom
    (site : AtomSite) (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens (ProductionId.atom site).rhs) :
  ActionReduces file tokens (.actionFor (.atom site)) origin finish
    input (AtomSite.pack site input)

ActionReduces.seq
    (site : SequenceSite) (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens (ProductionId.seq site).rhs) :
  ActionReduces file tokens (.actionFor (.seq site)) origin finish
    input (SequenceSite.pack site input)

ActionReduces.group
    (site : GroupSite) (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens (ProductionId.group site).rhs) :
  ActionReduces file tokens (.actionFor (.group site)) origin finish
    input (GroupSite.pack site input)

ActionReduces.choice
    (site : ChoiceSite) (branch : Fin site.branchCount)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
  ActionReduces file tokens (.actionFor (.choice site branch)) origin finish
    input (ChoiceSite.pack site branch input)

ActionReduces.opt
    (site : OptionalSite) (branch : OptionalBranch)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
  ActionReduces file tokens (.actionFor (.opt site branch)) origin finish
    input (OptionalSite.pack site branch input)

ActionReduces.star
    (site : StarSite) (branch : NilConsBranch)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
  ActionReduces file tokens (.actionFor (.star site branch)) origin finish
    input (StarSite.pack site branch input)

ActionReduces.plus
    (site : PlusSite) (branch : OneConsBranch)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
  ActionReduces file tokens (.actionFor (.plus site branch)) origin finish
    input (PlusSite.pack site branch input)

ActionReduces.list0
    (site : List0Site) (branch : NilConsBranch)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
  ActionReduces file tokens (.actionFor (.list0 site branch)) origin finish
    input (List0Site.pack site branch input)

ActionReduces.list1
    (site : List1Site) (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
  ActionReduces file tokens (.actionFor (.list1 site)) origin finish
    input (List1Site.pack site input)

ActionReduces.tail
    (site : ListSite) (branch : NilConsBranch)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens
      (ProductionId.tail site branch).rhs) :
  ActionReduces file tokens (.actionFor (.tail site branch)) origin finish
    input (ListSite.pack site branch input)

end ActionReducesConstructors
```

In every constructor above, the dependent type of `input` is exactly the RHS
of the production displayed inside its `ActionId`, and the dependent type of
the result is exactly that production's LHS carrier. Thus no separate action,
production, origin, finish, input, or output equality premise is hidden in the
constructor.

| Action shape | Exact output equation |
| --- | --- |
| `A.root[R]` | Its singleton auxiliary input is passed to `RuleReduction file tokens R origin finish`; that relation's result is the rule value. |
| `A.atom[s]` | A terminal `MatchedTerminal` becomes the terminal-atom `EbnfValue`; a source-rule value becomes the nonterminal-atom `EbnfValue`. |
| `A.seq[s]` | The ordered child-auxiliary HList becomes the identically ordered `EbnfValues`; no permutation or flattening occurs. |
| `A.group[s]` | The unique child value is returned unchanged. This is an EBNF group, not a source parenthesis. |
| `A.choice[s,i]` | The unique child is tagged with exactly branch `i`. |
| `A.opt[s,none/some]` | Epsilon maps to `none`; the unique child maps to `some child`. |
| `A.star[s,nil/cons]` | Epsilon maps to `[]`; `(head, recursively reduced tail)` maps to `head :: tail`. |
| `A.plus[s,one/cons]` | One child maps to `{head := child, tail := []}`; `(head, recursive nonempty tail)` prepends `head`. |
| `A.list0[s,nil/cons]` | Epsilon maps to `[]`; `(head, Tail(s))` maps to `head :: tail`. |
| `A.list1[s]` | `(head, Tail(s))` maps to `{head := head, tail := tail}`. |
| `A.tail[s,nil/cons]` | Epsilon maps to `[]`; `MatchedTerminal comma, head, Tail(s)` maps to `head :: tail`; the comma is discarded only after its exact match and span have been retained in the premise. |

There is no cast from an unindexed list, and no constructor may invoke
`RuleReduction` except `ActionReduces.root`. The caller supplies the completed
item's actual `origin` and `finish` directly to the selected constructor.

The following notation fixes the complete `RuleReduction` equation family.
It is normative Lean-level pseudocode, not an informal list of examples.
`#i(value)` is the indexed value of displayed choice branch `i`; parentheses
are `EbnfValues` in source order; `none`/`some`, `[]`/`(::)`, and
`NEL(head, tail)` are the values of optional, star/list0, and plus/list1.
Every quoted terminal metavariable is a `MatchedTerminal` at that exact grammar
class. These total projections are used below:

```text
IdentifierProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier) : Prop

PathSegmentProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) : Prop

ExternalLibraryProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : ExternalLibraryName) : Prop

LiteralProjects
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalPayload : LiteralPayload) : Prop

AssemblySliceProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice) : Prop

sp(terminal)                    = terminal.span
id(terminal, parsedIdentifier)  =
  { span := terminal.span, payload := parsedIdentifier }
path(terminal, parsedPath)      =
  { span := terminal.span, payload := parsedPath }
external(terminal, parsedName)  =
  { span := terminal.span, payload := parsedName }
unit(terminal) = { span := terminal.span, payload := () }
marker(kind, terminal) = { span := terminal.span, payload := kind }
  only for one of the exact terminal/kind equations below
pragma(terminal) =
  { span := terminal.span, payload := terminalPragmaKind }
literal(terminal, literalPayload) =
  { span := terminal.span, payload := literalPayload }

between(firstSpan, lastSpan, payload) =
  { span := { source := file.id,
              startByte := firstSpan.startByte,
              endByte := lastSpan.endByte },
    payload := payload }

moduleLoc(payload) =
  { span := { source := file.id, startByte := 0,
              endByte := file.content.utf8ByteSize },
    payload := payload }

emptyAt(byte, payload) =
  { span := { source := file.id, startByte := byte, endByte := byte },
    payload := payload }

mapNEL(f, NEL(head, tail)) = NEL(f(head), List.map f tail)

option(default, f, none) = default
option(default, f, some value) = f(value)
```

Each of the first three projection relations requires an exact retained-token
spelling equation and respectively
`Identifier.parse spelling = some parsed`,
`PathSegment.parse spelling = some parsed`, or
`ExternalLibraryName.parse spelling = some parsed`.
`PathSegmentProjects` admits the two token shapes already listed by
`TerminalMatches.pathComponent`; the other projection relations permit only
their one exact terminal payload shape. `LiteralProjects` relates a decimal,
hexadecimal, or string matched terminal to the corresponding `Literal` value,
including both original spelling and decoded payload. `AssemblySliceProjects`
relates an assembly-block matched terminal to its exact retained
`AssemblySlice`. All five are propositions. A `RuleReduction` constructor
binds the parsed value or slice as an ordinary explicit Type argument and takes
the corresponding projection proposition as a premise; it never extracts that
value from `MatchedTerminal.matches` into Type.
For each identifier, path, external-library, and assembly matched terminal,
`ParserCore` proves existence and uniqueness of the corresponding projection
inside `Prop`. For `LiteralProjects` it proves the same theorem under the
closed premise that the terminal is decimal, hexadecimal, or string. These
existence theorems are exactly what `ruleReduction_total` eliminates while its
goal remains a proposition; the executable obtains the same data by direct
case analysis on the retained token value.

For compactness in the 75-row tables, `sourceLoc(payload)` is binder notation:
that individual constructor binds a fresh explicit
`witness : ConsumedSpanWitness file tokens origin finish` and the displayed
term is `sourceLoc witness payload`. Likewise `id(terminal)`,
`path(terminal)`, `external(terminal)`, `literal(terminal)`, and
`assemblyToken.slice` each bind the explicit result value and the exact
projection premise just specified. The generated Lean constructor signatures
contain those arguments; these table forms are not functions that choose a
witness from a proposition. Parse-result functionality is used only after two
constructor results exist.

`pragma` copies the exact `PragmaKind`. The marker projection is a dependent
refined helper whose domain is exactly these terminal/kind pairs:
`lib -> libraryRoot`, `std -> standardRoot`, `@ -> externalSigil`,
`* -> wildcard`, `_ -> wildcard`, `fallback -> fallbackName`,
`constructor -> contractConstructorName`, `public -> publicModifier`,
`payable -> payableModifier`, contextual `comptime -> comptimeModifier`, and
`default -> defaultModifier`. It has no constructor for a different kind
paired with one of those terminals and no catch-all case. `unit` is used
for proxy and leading-dot markers, whose AST field is `Located Unit`.

`args(none)=none` and `args(some(open, values, close))=some values`; no written
empty argument form is converted to absence. `firstRest(NEL(h,t)) = h :: t`.
The two deterministic folds are:

```text
foldPostfix(receiver, []) = receiver
foldPostfix(receiver, part :: rest) =
  foldPostfix(
    match part with
    | call _ arguments close =>
        between receiver.span close (.call receiver arguments)
    | select _ field =>
        between receiver.span field.span (.select receiver field)
    | index _ index close =>
        between receiver.span close (.index receiver index),
    rest)

foldInfixLeft(left, []) = left
foldInfixLeft(left, (operator, right) :: rest) =
  foldInfixLeft(
    between left.span right.span (.infix operator left right), rest)
```

Every operator helper constructs a `Located` operator with the operator
terminal's exact span. `!` maps to `PrefixOperator.logicalNot`; `* / % + - & ^
| < > <= >= == != && ||` map in that order to the identically named 16
`InfixOperator` constructors; and `= += -= ^= &= |= %=` map in that order to
the seven displayed `AssignmentOperator` constructors. No text lookup or
default operator case exists.

Here are the first 37 root equations, in `GrammarRuleId` order. A semicolon in
the right column separates equations for different displayed branch tags; it
is not source punctuation.

| Rule | Exact `EbnfValue` branch/tag to `RuleValue` equation |
| --- | --- |
| `module` | `(items, eof) -> moduleLoc { source := file.id, items := items }`, with `origin = Boundary.start tokens`, `finish = Boundary.afterLogicalEOF tokens`, and `eof.value = endOfFile`. |
| `topItem` | `#0 import -> sourceLoc (.importDecl import)`; `#1 export -> sourceLoc (.exportDecl export)`; `#2 pragma -> sourceLoc (.pragmaDecl pragma)`; `#3 data -> sourceLoc (.dataDecl data)`; `#4 alias -> sourceLoc (.typeAliasDecl alias)`; `#5 class -> sourceLoc (.classDecl class)`; `#6 instance -> sourceLoc (.instanceDecl instance)`; `#7 contract -> sourceLoc (.contractDecl contract)`; `#8 function -> sourceLoc (.functionDecl function)`. |
| `moduleRef` | `#0(at, library, dot, next, rest) -> sourceLoc (.external (marker externalSigil at) (external library) (NEL(path next, map (fun (dot, component) => path component) rest)))`; for `#1(first, rest)`, let `tail = map (fun (dot, component) => path component) rest`: if `first` spells `std`, produce `sourceLoc (.standard (marker standardRoot first) tail)`; if `first` spells `lib` and `tail = next :: remaining`, produce `sourceLoc (.libraryRoot (marker libraryRoot first) (NEL(next, remaining)))`; otherwise, including `first = lib` and `tail = []`, produce `sourceLoc (.relative (NEL(path first, tail)))`. Dots are discarded only after their matched premises. |
| `importDecl` | `#0(import, ref, semi) -> sourceLoc { moduleRef := ref, mode := .module none }`; `#1(import, ref, as, name, semi) -> sourceLoc { moduleRef := ref, mode := .module (some (id name)) }`; `#2(import, ref, dot, open, entries, close, hiding, semi) -> sourceLoc { moduleRef := ref, mode := .items (between (sp open) (sp close) {entries := entries}) hiding }`. |
| `importEntry` | `#0 star -> sourceLoc (.wildcard (marker wildcard star))`; `#1(name, none) -> sourceLoc (.named (id name) none)`; `#1(name, some(as, alias)) -> sourceLoc (.named (id name) (some (id alias)))`. |
| `hidingClause` | `(hiding, open, names, close) -> sourceLoc { names := map id names }`. |
| `exportDecl` | `#0(export, open, entries, close, semi) -> sourceLoc (.local (between (sp open) (sp close) { entries := entries }))`; `#1(export, ref, semi) -> sourceLoc (.module ref none)`; `#2(export, ref, as, name, semi) -> sourceLoc (.module ref (some (id name)))`; `#3(export, ref, dot, star, semi) -> sourceLoc (.from ref (between (sp dot) (sp star) (.dotWildcard (marker wildcard star))))`; `#4(export, ref, dot, open, entries, close, semi) -> sourceLoc (.from ref (between (sp open) (sp close) (.braced entries)))`. |
| `localExportEntry` | `#0 star -> sourceLoc (.wildcard (marker wildcard star))`; `#1 item -> sourceLoc (.item item)`; `#2(ref, dot, star) -> sourceLoc (.allFrom ref (marker wildcard star))`. |
| `remoteExportEntry` | `#0 star -> sourceLoc (.wildcard (marker wildcard star))`; `#1 item -> sourceLoc (.item item)`. |
| `exportItem` | `(name, selection) -> sourceLoc { name := id name, constructors := selection }`. |
| `constructorSelection` | `#0(open, star, close) -> sourceLoc (.all (marker wildcard star))`; `#1(open, names, close) -> sourceLoc (.named (mapNEL id names))`. |
| `pragmaDecl` | For each branch `i=0..3`, `(pragmaKw, kind_i, targets, semi) -> sourceLoc { kind := pragma(kind_i), targets := option [] (fun values => firstRest (mapNEL id values)) targets }`, where the branch order is exactly `no-coverage-condition`, `no-patterson-condition`, `no-bounded-variable-condition`, `no-generic-instance-for`. |
| `genericPrefix` | `(forall, none) -> sourceLoc { forallClause := forall, context := none }`; `(forall, some(predicates, arrow)) -> sourceLoc { forallClause := forall, context := some predicates }`. |
| `forallClause` | `(forallKw, first, rest, dot) -> sourceLoc { binders := NEL(first, map (fun (_, binder) => binder) rest) }`; each ignored first component is a fully reduced `OptionalCommaValue`. |
| `forallBinder` | `#0 name -> sourceLoc (.bare (id name))`; `#1(name, colon, class, none) -> sourceLoc (.bounded (id name) class none)`; `#1(name, colon, class, some(open, arguments, close)) -> sourceLoc (.bounded (id name) class (some arguments))`. |
| `optionalComma` | `none -> absent`; `some comma -> present (sp comma)`. |
| `predicateList` | `predicates -> predicates`. |
| `predicate` | `(main, colon, class, none) -> sourceLoc { main := main, className := class, parameters := none }`; `(main, colon, class, some(open, arguments, close)) -> sourceLoc { main := main, className := class, parameters := some arguments }`. |
| `functionSignature` | `(generic, public, payable, functionKw, name, open, parameters, close, return) -> sourceLoc { genericPrefix := generic, public := map (marker publicModifier) public, payable := map (marker payableModifier) payable, name := id name, parameters := parameters, returnType := map (fun (arrow, type) => type) return }`. |
| `functionDecl` | `(signature, body) -> sourceLoc { signature := signature, body := body }`. |
| `classMethod` | `(signature, semi) -> sourceLoc { signature := signature, terminator := sp semi }`. |
| `dataDecl` | `(dataKw, name, parameters, constructors, semi) -> sourceLoc { name := id name, parameters := map (fun (open, names, close) => mapNEL id names) parameters, constructors := map (fun (equal, first, rest) => NEL(first, map (fun (pipe, constructor) => constructor) rest)) constructors }`. |
| `dataConstructor` | `(name, none) -> sourceLoc { name := id name, fields := none }`; `(name, some(open, fields, close)) -> sourceLoc { name := id name, fields := some fields }`. |
| `typeAliasDecl` | `(typeKw, name, parameters, equal, body, semi) -> sourceLoc { name := id name, parameters := map (fun (open, names, close) => mapNEL id names) parameters, body := body }`. |
| `classDecl` | `(generic, classKw, main, colon, name, parameters, open, methods, close) -> sourceLoc { genericPrefix := generic, main := main, className := id name, parameters := map (fun (open, values, close) => values) parameters, methods := methods }`. |
| `instanceDecl` | `(generic, default, instanceKw, main, colon, class, parameters, open, methods, close) -> sourceLoc { genericPrefix := generic, default := map (marker defaultModifier) default, main := main, className := class, parameters := map (fun (open, values, close) => values) parameters, methods := methods }`. |
| `instanceMethod` | `function -> function` (pass-through, preserving the existing `FunctionDecl` span). |
| `contractDecl` | `(contractKw, name, parameters, open, members, close) -> sourceLoc { name := id name, parameters := map (fun (open, names, close) => mapNEL id names) parameters, members := members }`. |
| `contractMember` | `#0 data -> sourceLoc (.dataDecl data)`; `#1 alias -> sourceLoc (.typeAlias alias)`; `#2 field -> sourceLoc (.field field)`; `#3 function -> sourceLoc (.function function)`; `#4 fallback -> sourceLoc (.fallback fallback)`; `#5 constructor -> sourceLoc (.constructor constructor)`. |
| `fieldDecl` | `(name, colon, type, initializer, semi) -> sourceLoc { name := id name, type := type, initializer := map (fun (equal, expression) => expression) initializer }`. |
| `fallbackDecl` | `(generic, public, payable, fallback, open, parameters, close, return, body) -> sourceLoc { genericPrefix := generic, public := map (marker publicModifier) public, payable := map (marker payableModifier) payable, marker := marker fallbackName fallback, parameters := parameters, returnType := map (fun (arrow, type) => type) return, body := body }`. |
| `contractConstructorDecl` | `(public, payable, constructor, open, parameters, close, body) -> sourceLoc { public := map (marker publicModifier) public, payable := map (marker payableModifier) payable, marker := marker contractConstructorName constructor, parameters := parameters, body := body }`. |
| `parameter` | `(comptime, name, type) -> sourceLoc { comptime := map (marker comptimeModifier) comptime, name := id name, type := map (fun (colon, value) => value) type }`. |
| `body` | `(open, statements, close) -> sourceLoc { origin := .braced (sp open) (sp close), statements := statements }`. |
| `type` | `#0(comptime, inner) -> sourceLoc (.comptime (marker comptimeModifier comptime) inner)`; `#1(atom, none) -> atom`; `#1(atom, some(arrow, result)) -> sourceLoc (.function atom result)`. |
| `typeAtom` | `#0(at, inner) -> sourceLoc (.proxy (unit at) inner)`; `#1(name, none) -> sourceLoc (.named name none)`; `#1(name, some(open, arguments, close)) -> sourceLoc (.named name (some arguments))`; `#2(open, close) -> sourceLoc (.tuple [])`; `#3(open, inner, close) -> sourceLoc (.group inner)`; `#4(open, first, comma, second, rest, close) -> sourceLoc (.tuple (first :: second :: map (fun (comma, value) => value) rest))`. |
| `qualifiedName` | `(first, rest) -> sourceLoc { components := NEL(id first, map (fun (dot, name) => id name) rest) }`. |

The remaining 38 equations continue that same table and order:

| Rule | Exact `EbnfValue` branch/tag to `RuleValue` equation |
| --- | --- |
| `statement` | For branches `#0` through `#10`, return the child unchanged, in the exact order `let`, `return`, `match`, `if`, `for`, `assembly`, `block`, `break`, `continue`, `assignment`, `expression`. |
| `letStatement` | `(binding, semi) -> sourceLoc (.letBinding binding)`. |
| `letBinding` | `(letKw, name, none, initializer) -> sourceLoc { comptime := none, name := id name, type := none, initializer := map (fun (equal, value) => value) initializer }`; `(letKw, name, some(colon, none, value), initializer) -> sourceLoc { comptime := none, name := id name, type := some value, initializer := map (fun (equal, expression) => expression) initializer }`; `(letKw, name, some(colon, some comptime, value), initializer) -> sourceLoc { comptime := some (marker comptimeModifier comptime), name := id name, type := some value, initializer := map (fun (equal, expression) => expression) initializer }`. |
| `returnStatement` | `(returnKw, value, semi) -> sourceLoc (.return value (sp semi))`. |
| `blockStatement` | `body -> sourceLoc (.block body)`. |
| `breakStatement` | `(breakKw, semi) -> sourceLoc (.break (sp semi))`. |
| `continueStatement` | `(continueKw, semi) -> sourceLoc (.continue (sp semi))`. |
| `assemblyStatement` | `(assemblyKw, assemblyToken) -> sourceLoc (.assembly assemblyToken.slice)`, where `assemblyToken.slice` is the exact `AssemblySlice` in the token payload. |
| `ifStatement` | `(ifKw, open, condition, close, thenBody, none) -> sourceLoc (.ifThenElse condition thenBody none)`; `(ifKw, open, condition, close, thenBody, some(elseKw, elseBody)) -> sourceLoc (.ifThenElse condition thenBody (some elseBody))`. |
| `forStatement` | `(forKw, open, initializers, semi1, condition, semi2, post, close, body) -> sourceLoc (.forLoop initializers condition post body)`. |
| `forInitItem` | `#0 binding -> sourceLoc (.letBinding binding)`; `#1(left, operator, right) -> sourceLoc (.assignment operator left right)`; `#2 expression -> sourceLoc (.expression expression)`. |
| `forPostItem` | `#0(left, operator, right) -> sourceLoc (.assignment operator left right)`; `#1 expression -> sourceLoc (.expression expression)`. |
| `matchStatement` | `(matchKw, scrutinees, open, arms, close, terminator) -> sourceLoc (.match scrutinees arms (map sp terminator))`. |
| `matchArm` | `(pipe, patterns, fatArrow, statements) -> sourceLoc { patterns := patterns, body := armBody(fatArrow, statements) }`, where `armBody(fatArrow, []) = emptyAt(fatArrow.span.endByte, { origin := .matchArm (sp fatArrow), statements := [] })`, and for a nonempty list it is `between(firstStatement.span, lastStatement.span, { origin := .matchArm (sp fatArrow), statements := statements })`. |
| `armStatement` | `statement -> statement` (pass-through). |
| `assignmentStatement` | `(left, operator, right, semi) -> sourceLoc (.assignment operator left right)`. |
| `assignmentOperator` | Branches `#0..#6` map `=`, `+=`, `-=`, `^=`, `&=`, `|=`, `%=` respectively to values `{ span := sp token, payload := .equal }`, `{ span := sp token, payload := .addEqual }`, `{ span := sp token, payload := .subtractEqual }`, `{ span := sp token, payload := .bitXorEqual }`, `{ span := sp token, payload := .bitAndEqual }`, `{ span := sp token, payload := .bitOrEqual }`, and `{ span := sp token, payload := .moduloEqual }`. |
| `expressionStatement` | `(expression, some semi) -> sourceLoc (.expression expression (some (sp semi)))`; `(expression, none) -> sourceLoc (.expression expression none)`. |
| `terminalExpression` | `expression -> expression` (pass-through). |
| `pattern` | `#0 underscore -> sourceLoc (.wildcard (marker wildcard underscore))`; `#1 literal -> sourceLoc (.literal literal)`; `#2(dot, name, none) -> sourceLoc (.dotConstructor (unit dot) (id name) none)`; `#2(dot, name, some(open, arguments, close)) -> sourceLoc (.dotConstructor (unit dot) (id name) (some arguments))`; `#3(comptime, expression) -> sourceLoc (.comptime (marker comptimeModifier comptime) expression)`; `#4(name, none) -> sourceLoc (.named name none)`; `#4(name, some(open, arguments, close)) -> sourceLoc (.named name (some arguments))`; `#5(open, close) -> sourceLoc (.tuple [])`; `#6(open, inner, close) -> sourceLoc (.group inner)`; `#7(open, first, comma, second, rest, close) -> sourceLoc (.tuple (first :: second :: map (fun (comma, value) => value) rest))`. |
| `expression` | `annotation -> annotation` (pass-through). |
| `annotation` | `(expression, none) -> expression`; `(expression, some(colon, type)) -> sourceLoc (.annotation expression type)`. |
| `conditional` | `#0(ifKw, condition, thenKw, thenBranch, elseKw, elseBranch) -> sourceLoc (.keywordConditional condition thenBranch elseBranch)`; `#1(condition, none) -> condition`; `#1(condition, some(question, thenBranch, colon, elseBranch)) -> sourceLoc (.ternaryConditional condition thenBranch elseBranch)`. |
| `logicalOr` | `(left, rest) -> foldInfixLeft(left, map (fun (op, right) => (infix(op), right)) rest)`, with only `||`. |
| `logicalAnd` | The same left fold, with only `&&`. |
| `equality` | `(left, none) -> left`; `(left, some(opChoice, right)) -> sourceLoc (.infix (infix(opChoice)) left right)`, where `opChoice` is exactly branch `==` or `!=`. |
| `relational` | `(left, none) -> left`; `(left, some(opChoice, right)) -> sourceLoc (.infix (infix(opChoice)) left right)`, where `opChoice` is exactly branch `<`, `>`, `<=`, or `>=`. |
| `bitOr` | The exact left fold over `(pipe, right)` pairs. |
| `bitXor` | The exact left fold over `(caret, right)` pairs. |
| `bitAnd` | The exact left fold over `(amp, right)` pairs. |
| `additive` | The exact left fold over `(#0 plus | #1 minus, right)` pairs. |
| `multiplicative` | The exact left fold over `(#0 star | #1 slash | #2 percent, right)` pairs. |
| `prefix` | `#0(bang, operand) -> sourceLoc (.prefix { span := sp bang, payload := .logicalNot } operand)`; `#1 postfix -> postfix`. Recursion of the first branch makes written prefixes right-associated. |
| `postfix` | `(atom, parts) -> foldPostfix(atom, parts)` in source order. |
| `postfixPart` | `#0(open, arguments, close) -> .call (sp open) arguments (sp close)`; `#1(dot, field) -> .select (sp dot) (id field)`; `#2(open, index, close) -> .index (sp open) index (sp close)`. |
| `atom` | `#0 literal -> sourceLoc (.literal literal)`; `#1 name -> sourceLoc (.name (id name))`; `#2(dot, name, none) -> sourceLoc (.dotConstructor (unit dot) (id name) none)`; `#2(dot, name, some(open, arguments, close)) -> sourceLoc (.dotConstructor (unit dot) (id name) (some arguments))`; `#3(at, type) -> sourceLoc (.proxy (unit at) type)`; `#4 lambda -> lambda`; `#5(open, close) -> sourceLoc (.tuple [])`; `#6(open, inner, close) -> sourceLoc (.group inner)`; `#7(open, first, comma, second, rest, close) -> sourceLoc (.tuple (first :: second :: map (fun (comma, value) => value) rest))`. |
| `lambda` | `(lamKw, open, parameters, close, return, body) -> sourceLoc (.lambda parameters (map (fun (arrow, type) => type) return) body)`. |
| `literal` | `#0 decimal -> literal(decimal)`; `#1 hexadecimal -> literal(hexadecimal)`; `#2 string -> literal(string)`. |

These two tables contain 75 and only 75 rule rows. Within each row every
choice tag and every option presence case is covered. Every constructor that
adds a real located syntax wrapper uses `sourceLoc`, `between`, the exact token
span, the module override, or the empty-arm override shown above; pass-through
rows add no wrapper. They are the constructors of the inductive
`RuleReduction` relation. Consequently no catch-all, proof-irrelevant output
field, `Classical.choice`, reparse, or unchecked output equality is permitted,
and `RuleReduction.functional` follows by case analysis on the rule, branch
tag, these equations, `ConsumedSpan.functional`, and parse-result uniqueness.

The corresponding constructive existence theorems are required, not left
implicit in parser completeness:

```text
ruleReduction_total
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    (ready : RuleReductionReady file tokens rule origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs rule)) :
  exists output : RuleValue rule,
    RuleReduction file tokens rule origin finish input output

actionReduces_total
    {file : WorkspaceFile} {tokens : List Token}
    {action : ActionId} {origin finish : Boundary tokens}
    (ready : ActionReductionReady file tokens action origin finish)
    (input : GrammarSymbolValues file tokens action.production.rhs) :
  exists output : NonterminalValue file tokens action.production.lhs,
    ActionReduces file tokens action origin finish input output
```

The proofs recurse over the 75 rule rows and case-split over the eleven action
shapes. For an ordinary located rule, `ready` supplies
`ConsumedSpanWitness.compute`; terminal projection existence follows inside
the proposition from the corresponding `MatchedTerminal.matches` equation.
The module case uses its stated root boundaries and full-file override.
`actionReduces_total` invokes `ruleReduction_total` only in its root case and
uses the total packer directly in every other case. Together with
`contextualReach_ordered`, these are the action-construction lemmas used by
`chartG_complete`.

Phase C reachability and packed reduction are closed independently of either
executor. Define the production instance of a dot-zero contextual item by its
production, raw origin, and context. `EnabledProductionInstance` requires one
complete `GuardWitnessKey` value for every cell of that instance's `guardOf`
list, all using the same `memo`, `PhaseBCorrect`, and `AllGuardsFinal` proofs;
the empty list is enabled by `Unit`. Then `ContextualReach` is the least
relation generated by exactly these rules:

1. the dot-zero `P.root[GrammarRuleId.module]` item at origin/current zero and context
   `plain` is reached;
2. prediction from a reached waiting item adds the dot-zero child production
   in `descendContext waiting childProduction` exactly when its
   `ProductionInstanceKey` is enabled;
3. a structurally valid scanned edge whose `before` is reached adds its
   `after`; and
4. a structurally valid completed edge whose `waiting` and `finished` are
   reached adds its `after`.

There are no other constructors. `ContextualEdgeReach` is exactly structural
validity plus reachability of all endpoints:

```text
ContextualEdgeReach ... key iff
  ContextualPackedEdgeKey.StructurallyValid file tokens key and
  match key with
  | scanned before after _ =>
      ContextualReach ... before and ContextualReach ... after
  | completed waiting finished after _ =>
      ContextualReach ... waiting and ContextualReach ... finished and
      ContextualReach ... after
```

Induction over those four reach constructors proves the public ordering
theorem:

```text
contextualReach_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens} :
  ContextualReach file tokens memo correct final item ->
  item.raw.origin.val <= item.raw.current.val
```

Prediction begins at equal boundaries, scan moves only the current boundary
forward, and completion uses a finished item that began at the waiting
cursor. This theorem supplies the `ordered` argument to
`ConsumedSpanWitness.compute` for every coherent completed action.

This is the only contextual edge premise accepted by reduction. The semantic
derivation keeps one edge identity at every step:

```text
mutual
  CoherentPrefix
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo) :
    (item : ContextualItemKey tokens) ->
    PrefixValues file tokens item -> Prop

  CoherentReduction
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo) :
    (item : ContextualItemKey tokens) ->
    NonterminalValue file tokens item.raw.production.lhs -> Prop
end
```

The mutual relation has exactly these four constructors; the displayed helper
result is the constructor's dependent output, not an informal append:

```text
section CoherentConstructors

variable {file : WorkspaceFile} {tokens : List Token}
variable {memo : GuardMemo tokens}
variable {correct : PhaseBCorrect file tokens memo}
variable {final : AllGuardsFinal memo}

CoherentPrefix.zero
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
  CoherentPrefix file tokens memo correct final item
    (PrefixValues.zeroValue item zero)

CoherentPrefix.scan
    (before after : ContextualItemKey tokens)
    (cursor : TerminalCursor tokens)
    (priorValues : PrefixValues file tokens before)
    (witness : ScannedEdgeWitness
      file tokens before.raw after.raw cursor)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.scanned before after cursor))
    (prior : CoherentPrefix file tokens memo correct final
      before priorValues) :
  CoherentPrefix file tokens memo correct final after
    (PrefixValues.scanValue before after witness.terminal
      witness.next witness.matched witness.advance priorValues)

CoherentPrefix.complete
    (waiting finished after : ContextualItemKey tokens)
    (shared : Boundary tokens)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs)
    (witness : CompletedEdgeWitness
      tokens waiting.raw finished.raw after.raw shared)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.completed waiting finished after shared))
    (prior : CoherentPrefix file tokens memo correct final
      waiting priorValues)
    (child : CoherentReduction file tokens memo correct final
      finished childValue) :
  CoherentPrefix file tokens memo correct final after
    (PrefixValues.completeValue waiting finished after
      witness.next witness.advance priorValues childValue)

CoherentReduction.reduce
    (item : ContextualItemKey tokens)
    (priorValues : PrefixValues file tokens item)
    (output : NonterminalValue file tokens item.raw.production.lhs)
    (reached : ContextualReach file tokens memo correct final item)
    (complete : CompleteItem item.raw)
    (prefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (action : ActionReduces file tokens
      (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output) :
  CoherentReduction file tokens memo correct final item output

end CoherentConstructors
```

The scan and completion constructors take the evidence carrier belonging to
the same contextual edge key; `packedEdge_*_valid_iff` proves that carrier's
raw equations, while `ContextualEdgeReach` supplies the contextual endpoints.
No Prop-valued existential is eliminated to manufacture semantic data. The
zero, scan, completion, and full-RHS index changes are precisely the four
checked `Eq.mp` helpers. In particular, `CompleteItem` is not claimed to make
`rhs.take dot` definitionally equal to `rhs`. Epsilon reductions use
`zeroValue` followed by `fullValue` and the appropriate nil action. There is no
constructor for splicing a prefix, completion value, or raw projection from
another context.

The one reusable rule-indexed complete-root relation is:

```text
CanonicalCompleteRootReduction
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    (value : RuleValue rule) : Prop =
  ContextualReach file tokens memo correct final
    (CanonicalCompleteRootItem
      tokens rule origin finish context) and
  CompleteItem
    (CanonicalCompleteRootItem
      tokens rule origin finish context).raw and
  CoherentReduction file tokens memo correct final
    (CanonicalCompleteRootItem
      tokens rule origin finish context) value
```

The middle premise is discharged by
`canonicalCompleteRootItem_complete`, but remains explicit in the public
relation. The last premise is well typed by reduction alone: the canonical
item's production and left-hand side reduce definitionally to `.root rule` and
`.rule rule`, so its output carrier reduces definitionally to `RuleValue rule`.
There is no equality proof to eliminate and no cast of an already-reduced
value.

The successful root carrier and public parse judgment are:

```text
SourceBackedRoot
    (file : WorkspaceFile) (tokens : List Token)
    (module : ParsedModuleV1) : Prop =
  exists memo,
  exists correct : PhaseBCorrect file tokens memo,
  exists allFinal : AllGuardsFinal memo,
    CanonicalCompleteRootReduction
      file tokens memo correct allFinal
      GrammarRuleId.module
      (Boundary.start tokens)
      (Boundary.afterLogicalEOF tokens)
      GuardContext.plain
      module

Multi.Parses : WorkspaceFile -> List Token -> ParsedModuleV1 -> Prop
  | sourceBackedRoot
      (file : WorkspaceFile) (tokens : List Token)
      (module : ParsedModuleV1) :
      TokensOwnedBy file tokens ->
      SourceBackedRoot file tokens module ->
      Parses file tokens module
```

The canonical item's fields definitionally force `.root[module]`, origin zero,
post-EOF finish, and `plain`; the `.root[module]` `RuleReduction` equation
additionally forces its source ID, complete item list, and full-file module span, so
`SourceBackedRoot` cannot inject an arbitrary `ParsedModuleV1`. `Parses` has no
recovery/synthetic constructor and no premise equating an executor result.

`G` accepts exactly when the completed module-root contextual item in context
`plain` spans boundary zero through `T`. Thus EOF is consumed and successful
prefix parses do not exist.

On acceptance, the contextual packed root is reduced by the action table. The
guard table, non-null repetition check, precedence construction, and delimiter
rules imply:

```text
uniqueRootReduction :
  completedContextualRoot G tokens plain root1 ->
  completedContextualRoot G tokens plain root2 ->
  root1 = root2
```

The statement quantifies over all contextual packed derivations, not only the
first worklist path. `G` therefore never selects an AST by map iteration order.
Its result is the unique `ParsedModuleV1`, or the closed parse diagnostic
specified below.

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
continue. A parse diagnostic instead comes from the complete finite Phase C
relation, so an earlier dead alternative cannot hide a later failure. The
diagnostic carrier is closed over the same `memo`, `PhaseBCorrect`, and
`AllGuardsFinal` proofs:

```text
GreatestReachableCursor
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) : Prop =
  (exists item,
    ContextualReach file tokens memo correct final item and
    item.raw.current = cursor) and
  (forall item,
    ContextualReach file tokens memo correct final item ->
    item.raw.current.val <= cursor.val)

FrontierReach
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (item : ContextualItemKey tokens) : Prop =
  GreatestReachableCursor file tokens memo correct final cursor and
  ContextualReach file tokens memo correct final item and
  item.raw.current = cursor

ExpectedMember
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (expected : Expected) : Prop =
  exists item terminal,
    FrontierReach file tokens memo correct final cursor item and
    NextSymbol item.raw (terminal terminal) and
    EnabledProductionInstance file tokens memo correct final
      { production := item.raw.production,
        origin := item.raw.origin,
        context := item.context } and
    expected = terminal.expected

CanonicalExpected
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (values : NonemptyList Expected) : Prop =
  (forall expected,
    expected in (values.head :: values.tail) iff
      ExpectedMember file tokens memo correct final cursor expected) and
  (values.head :: values.tail).Nodup and
  (values.head :: values.tail).Pairwise
    (fun left right => Expected.compare left right = lt)

FoundAt
    (file : WorkspaceFile) (tokens : List Token)
    (cursor : Boundary tokens)
    (span : SourceSpan) (found : Found) : Prop
```

The Phase C relation is already fully saturated under predict and complete, so
`FrontierReach` is exactly the reached items at the greatest cursor; starting
a second frontier closure is forbidden. The equivalent closure
characterization is a required theorem. Greatest reach exists because the
root seed is reached. On failure its cursor is a `TerminalCursor` no later than
logical `EOF`, and `CanonicalExpected` exists and is unique.

`Expected.compare` is owned by `ParserCore`. It first uses this constructor
order: `hardKeyword`, `contextualKeyword`, `pragmaName`, `symbol`, `identifier`,
`pathComponent`, `literal`, `assemblyBlock`, `endOfFile`; within the first four
constructors it uses the displayed finite index of `HardKeyword`,
`ContextualKeyword`, `PragmaKind`, or `Symbol`. The strict pairwise condition,
membership iff, and nonempty type therefore specify one sorted, deduplicated
list. `TerminalSymbol.expected` gives quoted terminals their singleton values,
maps decimal/hex/string to `literal`, and maps logical `EOF` to `endOfFile`.
No nonterminal, disabled production, recovery label, or presentation name can
enter `ExpectedMember`. A witness is paired with the exact contextual item;
two equal raw projections cannot exchange witnesses.

`FoundAt` has exactly two constructors. `retained` requires a
`TerminalCursor` whose `beforeBoundary = cursor` and a `TerminalAt` retained
token; it returns that token's exact span and `.token token.payload`.
`endOfFile` requires the unique cursor with `cursor.val = tokens.length` and
returns the empty file-end span and `.endOfFile`. It has no constructor at the
post-EOF boundary.

G10 is indexed by the precedence rule that established the first operation.
Using only the outer `expression` root is insufficient: at the second `<` in
`a == b < c < d`, the completed relational value is the right operand of an
equality value and the outer payload is not the relevant first relational
operation. The carrier therefore retains the coherent **level root** and the
same frontier cursor at which the second operator was found:

```text
NonAssociativeLevel.rule : NonAssociativeLevel -> GrammarRuleId
  | relational => GrammarRuleId.relational
  | equality   => GrammarRuleId.equality

NonAssociativeFrontierValue
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel) = {
  origin    : Boundary tokens,
  context   : GuardContext tokens,
  value     : RuleValue level.rule,
  frontier  : FrontierReach file tokens memo correct final cursor
    (CanonicalCompleteRootItem tokens level.rule
      origin cursor context),
  root      : CanonicalCompleteRootReduction
    file tokens memo correct final level.rule
      origin cursor context value
}

ExplicitGroupBoundary
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens} :
  (level : NonAssociativeLevel) ->
  NonAssociativeFrontierValue
    file tokens memo correct final cursor level -> Prop
  | relational, candidate =>
      exists inner, candidate.value.payload = .group inner
  | equality, candidate =>
      exists inner, candidate.value.payload = .group inner

CompletedNonAssociative
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens} :
  (level : NonAssociativeLevel) ->
  (candidate : NonAssociativeFrontierValue
    file tokens memo correct final cursor level) ->
  (first : Located InfixOperator) -> Prop
  | relational, candidate, first =>
      exists left right,
        candidate.value.payload = .infix first left right and
        first.payload in [less, greater, lessEqual, greaterEqual]
  | equality, candidate, first =>
      exists left right,
        candidate.value.payload = .infix first left right and
        first.payload in [equal, notEqual]

FoundNonAssociativeOperatorAt
    (file : WorkspaceFile) (tokens : List Token)
    (cursor : Boundary tokens) (level : NonAssociativeLevel)
    (operator : Located InfixOperator) : Prop

RepeatedNonAssociativeAt
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (level : NonAssociativeLevel)
    (operator : Located InfixOperator) : Prop =
  exists candidate : NonAssociativeFrontierValue
      file tokens memo correct final cursor level,
  exists first,
    CompletedNonAssociative level candidate first and
    not ExplicitGroupBoundary level candidate and
    FoundNonAssociativeOperatorAt file tokens cursor level operator
```

`FoundNonAssociativeOperatorAt` has exactly six constructors. At the same
`TerminalCursor.beforeBoundary = cursor`, `<`, `>`, `<=`, `>=` produce the
corresponding exact-span `Located InfixOperator` at level `relational`, and
`==`, `!=` do so at level `equality`. It is false for every other token and at
EOF. `RuleValue GrammarRuleId.relational` and
`RuleValue GrammarRuleId.equality` each reduce definitionally to `Expression`
in their respective indexed cases; no equality field changes either output
type. Because
`CompletedNonAssociative` and `ExplicitGroupBoundary` inspect the same
rule-indexed `NonAssociativeFrontierValue`, a completed edge from another context cannot
be substituted. A source-parenthesized expression reduces to outer payload
`.group`, so it cannot satisfy `CompletedNonAssociative`; EBNF metalanguage
`P.group` creates no `ExplicitGroupBoundary`. Thus `(a < b) < c` starts a new
level, while `a < b >= c` selects G10 at `>=`. The level root also selects G10
for the second `<` in `a == b < c < d`, `a && b < c < d`, and a conditional
branch containing `b < c < d`; an unrelated outer expression root cannot hide
that completed relational root.

Finally the diagnostic judgment has exactly these two constructors:

```text
Multi.ParseDiagnostic.Applies :
  WorkspaceFile -> List Token -> ParseDiagnostic -> Prop

| unexpected
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (span : SourceSpan)
    (found : Found) (expected : NonemptyList Expected)
    (noRoot : not (exists module,
      SourceBackedRoot file tokens module))
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (canonical : CanonicalExpected
      file tokens memo correct final cursor expected)
    (foundAt : FoundAt file tokens cursor span found)
    (notRepeated : forall level operator,
      not (RepeatedNonAssociativeAt file tokens memo correct final
        cursor level operator)) :
    Applies file tokens (.unexpected span found expected)

| repeatedNonAssociative
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (level : NonAssociativeLevel)
    (operator : Located InfixOperator)
    (noRoot : not (exists module,
      SourceBackedRoot file tokens module))
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (repeated : RepeatedNonAssociativeAt file tokens memo correct final
      cursor level operator) :
    Applies file tokens
      (.repeatedNonAssociative operator.span level operator)
```

The G10 constructor has no `Expected` premise or payload. The negative G10
premise on `unexpected`, functionality of the six-token mapping, and uniqueness
of the canonical frontier make the constructors exclusive and diagnostic
functional. Both relations are declarative; neither mentions `Chart.G`,
`parseTokens`, a worklist result, or executor failure.

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
stable production and action tables. Its derivations record
`ProductionInstanceKey`, contextual item and packed-edge identities, exact
`GuardWitnessKey`/`GuardAnchor`/`GuardEvidence` premises, action IDs, and
associativity. Its prediction and completion rules use the same
`descendContext` equations, so no derivation rule existentially erases context
before combining premises. It does not contain an equation to `Chart.G` or
`parseTokens`. `ParseDiagnostic.Applies` independently derives the same
contextual greatest cursor, sorted/deduplicated expected union, exact `Found`,
and coherent `G10` override. `StructurallyAccepts` is the conjunction of the
sixteen rules above and does not invoke the validator.

The lexer imports syntax/diagnostics, while both parser executors import the
shared `ParserCore`; no executor imports its sibling judgment:

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

The location half of this certified boundary is already implemented:
`Parses.everyLocationValid` derives `EveryLocationValid file module` from the
lexer and parser judgments. In plain terms, every retained AST location in a
successful parse belongs to the input file and every direct child location is
inside its parent. Exact token correspondence and the facade that bundles all
of these proofs remain to be implemented.

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
K_guard = card PriorityGuardId
  = Multi.Grammar.allPriorityGuardIds.length
  = 9
H = sum ((guardOf p).length for p in
         Multi.Grammar.expanded.productions)
  = 18                                         -- derived guard-table cells
C(T) = card (GuardContext tokens)
  = 1 + 3 * Q
FastMemoKeyKind =
  | rule GrammarRuleId | site GrammarSite
  | guard PriorityGuardId | action ActionId
F = card FastMemoKeyKind
  = card GrammarRuleId + card GrammarSite
    + card PriorityGuardId + card ActionId
N = Multi.astNodeMeasure parsedModule

L(T) = (1 + C(T)) * D * Q * Q
R(T) = (1 + C(T)) * D * P * Q * Q
U(T) = (1 + C(T)) * D * D * Q * Q * Q

lexBound(B) =
  16 * (B + 1)

chartGBound(T) =
  4 + 8 * K_guard * Q * Q
    + P * C(T) * Q
    + 4 * H * C(T) * Q
    + 14 * L(T)
    + 2 * R(T)
    + 8 * U(T)

parseBound(T) =
  1 + 32 * F * Q
    + 256 * F * Q * Q

structureBound(N) =
  32 * (N + 1) * (N + 1)
```

A lexer unit is one cursor-state transition or one delimiter-stack transition.
The `Chart.G` counter uses the closed source tag and three key universes:

```text
ChartSourceTag(tokens) =
  | rawEvidence
  | contextual (context : GuardContext tokens)

card ChartSourceTag = 1 + C(T)

LinearKey =
  ChartSourceTag × DottedRhs × Boundary × Boundary

PredictionKey =
  ChartSourceTag × DottedRhs × ProductionId × Boundary × Boundary

CubicKey =
  ChartSourceTag × DottedRhs × DottedRhs ×
    Boundary × Boundary × Boundary

card LinearKey     = L(T)
card PredictionKey = R(T)
card CubicKey      = U(T)

EvidenceIndexKind =
  | terminalWindow | exactSlice | greatestEnd | delimiterOrRegion
```

`rawEvidence` identifies Phase A; `contextual context` identifies Phase C.
It is a tagged sum, not erasure of a context. `DottedRhs` has cardinality `D`.
The boundary coordinates are the origin/current or
waiting/shared/finished-current coordinates appropriate to the unit family.
For `U01`, the displayed-order pair
`(EvidenceIndexKind, PriorityGuardId ⊕ GrammarRuleId)` injects into two fixed
`DottedRhs` coordinates. The executable tables prove
`card EvidenceIndexKind * (K_guard + card GrammarRuleId) <= D * D`; this is the
tag that keeps the four index families disjoint inside one `U(T)` copy.

Phase B has exactly these eight scheduler slots for each
`GuardInstanceKey`, in order:

```text
GuardFinalizeSlot =
  | initializeUndecided
  | siteTerminalLookup
  | adjacentTerminalWindowLookup
  | exactSliceLookup
  | unguardedSpanLookup
  | greatestEndLookup
  | delimiterOrRegionLookup
  | writeFinalDecision

ChartPhaseSlot =
  | initializePhaseA | sealAEnterB | sealBEnterC | selectFinalOutcome
```

Every key executes all eight slots once; a lookup irrelevant to that guard ID
is a no-op. Only `initializeUndecided` and `writeFinalDecision` mutate the
cell. The middle six read Phase A's finalized indexes. This gives the term
`8 * K_guard * Q^2`; the `ordered` proof only reduces the actual key count.
No Phase B slot constructs a guard witness.

Phase C attempts each `ProductionInstanceKey` once, giving
`P * C(T) * Q`. Each possible guard-table cell of such an instance has four
distinct once-only slots:

```text
GuardWitnessSlot =
  | constructAnchor
  | lookupFinalDecision
  | comparePolarity
  | insertWitness
```

Their tagged injection gives `4 * H * C(T) * Q`. `insertWitness` is a no-op
when no anchor exists or when the finalized decision does not accept that
polarity; after a failed `constructAnchor`, the intervening lookup/comparison
slots are also no-ops. No rejected witness key is inserted, and an undecided
cell is impossible in Phase C.

All remaining unit families and their disjoint injection tags are fixed by
this table. A combined “raw/contextual” row uses `ChartSourceTag.rawEvidence`
for its Phase A units and `ChartSourceTag.contextual context` for its Phase C
units. Thus those units are individually distinguishable even when their raw
item or edge projections coincide.

Both saturation phases have separate ordered item and edge queues. A newly
inserted item or edge is enqueued once and later dequeued once. Phase A edge
dequeue registers only unguarded recognition/index evidence; Phase C edge
dequeue may schedule its stable action. This fixes the dequeue families even
for an implementation that could otherwise fuse them with insertion.

| Injection tag | Phase and exact unit family | Injective payload | Bound copy |
| --- | --- | --- | --- |
| `L01_itemDequeue` | A raw item dequeue; C contextual item dequeue | complete item key | `L(T)` |
| `L02_scannedEdgeDequeue` | A raw scanned-edge dequeue; C contextual scanned-edge dequeue | scanned-edge key; `after` is reconstructed | `L(T)` |
| `L03_itemInsert` | A universal/root seed or a newly predicted item insertion | inserted item key | `L(T)` |
| `L04_scanAttempt` | A raw/contextual scan attempt | item plus its current terminal cursor | `L(T)` |
| `L05_scannedItemInsert` | A successful raw/contextual scanned-item insertion | inserted item key | `L(T)` |
| `L06_scannedEdgeInsert` | A successful raw/contextual scanned-edge insertion | scanned-edge key | `L(T)` |
| `L07_completedItemInsert` | A successful raw/contextual completed-item insertion | inserted item key | `L(T)` |
| `L08_frontierDequeue` | C frontier-item dequeue | contextual item key | `L(T)` |
| `L09_frontierInsert` | C frontier-item insertion | contextual item key | `L(T)` |
| `L10_expectedCandidate` | C `Expected` terminal candidate and ordered-set insertion | contextual item key | `L(T)` |
| `L11_foundCandidate` | C's single retained-token/EOF `Found` and final-diagnostic construction candidate | cursor padded by fixed root dotted key | `L(T)` |
| `L12_scannedAction` | C terminal-atom action scheduled by a scanned edge | contextual scanned-edge key | `L(T)` |
| `L13_epsilonAction` | C epsilon-production action with no child edge | contextual completed-item key | `L(T)` |
| `L14_frontierScannedTraversal` | C frontier scanned-edge traversal | contextual scanned-edge key | `L(T)` |
| `R01_predictionAttempt` | A raw prediction attempt; C contextual prediction attempt | waiting item schema, predicted production, origin/current | `R(T)` |
| `R02_frontierPrediction` | C frontier prediction attempt | frontier item schema, predicted production, origin/current | `R(T)` |
| `U01_evidenceIndex` | A terminal-window, exact-slice, unguarded greatest-end, or delimiter/region-index candidate after raw saturation | guard/subgrammar tag and three boundaries, padded by fixed dotted keys | `U(T)` |
| `U02_completedEdgeDequeue` | A raw completed-edge dequeue; C contextual completed-edge dequeue | completed-edge key | `U(T)` |
| `U03_completionAttempt` | A raw/contextual compatible completion-pair attempt | waiting/finished schemas and three boundaries | `U(T)` |
| `U04_completedEdgeInsert` | A successful raw/contextual completed-edge insertion | completed-edge key | `U(T)` |
| `U05_completedAction` | C non-epsilon `ActionId` application scheduled by a contextual completed edge, including accepted-root reduction; A has no semantic action units | coherent contextual completed edge | `U(T)` |
| `U06_frontierCompletion` | C frontier completion-pair attempt | contextual waiting/finished keys and three boundaries | `U(T)` |
| `U07_frontierCompletedTraversal` | C frontier completed-edge traversal | coherent contextual completed edge | `U(T)` |
| `U08_G10Candidate` | C repeated-nonassociative override candidate | coherent contextual packed edge; found cursor is its frontier-current coordinate | `U(T)` |

The `L01` through `L14`, `R01` through `R02`, and `U01` through `U08`
constructor tags are part of the counter definition. No event can be charged
to two families, and two different families cannot collide after injection.
`L10` atomically inserts its candidate into the canonical ordered expected set,
and `L11` atomically constructs the one final `Found`/diagnostic value; these
two displayed fusions are normative and have no separately counted second
event. No other table row fuses two listed families.
A duplicate item/edge attempt is charged to its prediction, scan, or completion
attempt family; an insertion unit occurs only for a newly inserted key. Every
item or edge is dequeued at most once. `K_guard <= card GrammarRuleId <= P <= D`,
`1 <= Q`, and the fixed root dotted key justify the padding injections used for
the smaller frontier and evidence-index families; these inequalities are
executable consequences of `expanded` and its guard table.

The cardinality injections used by `chartGBound` are fixed:

```text
card Boundary                         = Q
card TerminalCursor                   = T = Q - 1
card GuardContext                     = C(T) = 1 + 3 * Q
card ProductionInstanceKey            = P * C(T) * Q
card GuardInstanceKey                 =
  K_guard * Q * (Q + 1) / 2           <= K_guard * Q * Q
card GuardWitnessKey                  <= H * C(T) * Q
card ContextualItemKey                = C(T) * D * Q * Q
card StructurallyValidContextualPackedEdge.scanned
  <= C(T) * D * Q * Q
card StructurallyValidContextualPackedEdge.completed
  <= C(T) * D * D * Q * Q * Q
```

The `GuardWitnessKey` injection sends a witness to its guard-table cell,
production context, and origin. `GuardAnchor.functional` reconstructs its
`GuardInstanceKey`, so no additional factor is hidden. The contextual
completion injection sends an edge to its waiting context, two raw dotted
schemas, waiting origin, shared cursor, and finished cursor;
`descendContext` reconstructs the finished context, so there is no `C(T)^2`
factor.

`PackedEdge` and `StructurallyValidContextualPackedEdge` are proof-irrelevant
subtypes. The displayed edge bounds count only keys satisfying their exact
structural equations; the unrestricted raw sum type is never enumerated,
stored, dequeued, or used as the domain of a worklist. Erasing the subtype
proof after validation preserves the same valid-key cardinality. `MatchedTerminal`, `EbnfValue`, `RuleValue`,
`GrammarSymbolValues`, `GuardEvidence`, `ScannedEdgeWitness`,
`CompletedEdgeWitness`, `CoherentPrefix`, `CoherentReduction`,
`CanonicalCompleteRootReduction`, `NonAssociativeFrontierValue`, and the validity/correctness
proofs are values or certificates attached to an existing item, edge, action,
guard, frontier, or G10 unit; they are not memo, worklist, or deduplication
identities. `ActionReduces.functional`, `RuleReduction.functional`, and
`CoherentReduction.functional` ensure that an existing coherent key has at
most one such attached semantic output. Their construction is charged respectively to the existing scan
actions `L12`, epsilon actions `L13`, completed actions `U05`, Phase-B lookup
slots, frontier units, and `U08_G10Candidate`. Therefore they introduce no new
cardinality factor and the displayed bound is unchanged. An implementation
that materializes a semantic value, proof term, coherent derivation, or AST
alternative as an additional worklist/memo key is nonconforming to this bound
and must specify a replacement bound before adoption.

The four `ChartPhaseSlot` values contribute the leading `4`; each occurs
exactly once, and neither sealing transition can occur until the preceding
phase's finite enumeration is exhausted. Phase A consumes exactly the
`rawEvidence` portion of the applicable tagged `L`, `R`, and `U` copies and
finishes `U01` before Phase B. Phase B consumes only the eight
guard-finalization slots. Phase C consumes the contextual portions, the
production/witness terms, and all frontier/G10 tags. This is the complete
family list for `Chart.G`; there is no uncharged generic “worklist step.”

Because `C(T) = 1 + 3 * Q`, `chartGBound` is quartic. The prior cubic bound is
not sound for instance-specific ancestry: multiplying only the raw item count
would permit a positive-context item to discharge a negative-context edge.
`P`, `D`, the raw `DottedItem` and `PackedEdgeKey`, and their enumeration are
unchanged. These are bounds on the specified semantic counter, not asymptotic
placeholders.

`F` is exactly the displayed sum of the four finite enumerations; it is not a
tunable numeral and is unchanged by the contextual chart repair. The optimized
`parseTokens` uses the same mandatory phase barrier:

1. Fast Phase A fills and fully saturates all context-free rule/site span and
   unguarded greatest-end/delimiter indexes. Candidate values retain their
   unresolved finite `guardOf` cells. No guarded candidate is combined and no
   guarded action is applied.
2. Fast Phase B initializes every ordered `.guard` memo coordinate that
   corresponds to a `GuardInstanceKey` to `undecided`, then reads only the
   completed Phase A indexes and replaces every such cell exactly once by its
   final `GuardDecision`. Unordered start/end coordinates are fixed no-op slots
   and are never queried. This phase does not generate a witness or combine a
   candidate. Re-running recognition for one guard cell is forbidden.
   Its sealed table carries the Core-owned `FastAllGuardsFinal` barrier.
   `Properties.lean` proves `FastPhaseBCorrect`, the observation-quotient
   counterpart of `PhaseBCorrect`; it is not a proposition imported by the
   executor. An all-neutral table satisfies only the finality barrier.
3. Only after `FastAllGuardsFinal` holds does executable Fast Phase C use
   precedence climbing, combine candidates, and visit each successful
   reduction edge once. Each combine reads the exact final guard cell and uses
   one coherent Core `GuardWitnessKey` observation. The corresponding
   declarative Phase C derivation is constructed in `Properties.lean` only
   after `FastPhaseBCorrect` has also been proved.

Within each phase, memo cells are visited in lexicographic `(fast key kind,
start boundary, end boundary)` order. No `undecided`, absent, or provisional
cell is interpreted as `negative` or `neutral`, and none can authorize a
candidate combine. A guard memo cell is indexed by exactly
`(PriorityGuardId, contextStart, siteCursor)`, so every `GuardInstanceKey`
injects into the already counted `.guard` family. Rule and site memo cells
never cache a result whose guard premises were existentially discharged. A
guarded activation must look up its exact final guard cell before using such a
candidate, and the lookup and action combine must use one guard-witness
observation, not independently projected raw premises.

The fast executor uses a proved observation quotient; it does not add
`GuardContext` as a third boundary coordinate. For `G01`, `G03` through `G06`,
and `G09`, evidence is independent of the retained outer context. For `G02`,
`G07`, and `G08`, `GuardAnchor` reconstructs the only context constructor and
start relevant to the decision from `(guard, contextStart, siteCursor)`;
`nearest_statement_region_functional` handles the `G08` region end. Therefore
two production instances collapsed into one fast guard cell allow exactly the
same polarity. `ActionId` reduction inspects the source span and semantic child
values but not the erased outer `GuardContext`, so an allowed cell also has the
same reduction. This congruence is a required theorem, not an implementation
assumption.

More precisely, a fast guarded-use slot is the tuple

```text
(guardInstance.guard,
 guardInstance.contextStart,
 guardInstance.siteCursor,
 index of the guarded production cell,
 witness phase)
```

where the finite guarded-use phases are final-decision lookup, polarity
comparison, and action combine. The first three fields select a `.guard` memo
key, the guarded production-cell index is drawn from the `H = 18` table cells,
and those three phases use `3 * H = 54` slot indices. The eight
`GuardFinalizeSlot` values occupy eight disjoint earlier indices, so all guard
work uses `8 + 3 * H = 62 < 256` fixed slots and injects into the 256 slots of
that memo cell. Context-free rule/site/action candidates use their existing
slots. Thus the fast schedule has no hidden `C(T)` factor and no uncounted join
over postfix origin, postfix-part origin, and result end.

Each kind/boundary pair has 32 fixed initialization/finalization work slots and
each memo cell has 256 fixed recognition/guard/action slots; an inapplicable
slot is a no-op and a slot is never revisited. A non-no-op slot is one memo
lookup or insertion, token comparison, guard comparison, or AST action. This
schedule is the executor's termination argument and gives the displayed exact
quadratic bound. Acceptance requires both its own bound and extensional
equality with `Chart.G` for success ASTs and complete diagnostics:

```text
parseTokens_eq_chartG :
  Multi.parseTokens file lexed = Multi.Chart.G file lexed
```

Current Lean status is deliberately narrower than that acceptance condition.
`ParserResourceAccounting.lean` exposes the fixed, boundary-slot, and
memo-slot schedule capacities, proves that their total is exactly
`parseBound`, and supplies the final numeric reduction theorem. The counted
fast executor, its operational correspondence to that ledger, the component
bounds, and `parseTokens_eq_chartG` remain to be implemented. The private
`Chart.G` counter continues to belong to the separate `chartGBound` universe.

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
production_rhs_public_bridges_exact
production_rhs_typed_hlist_transport
actionPackers_typed_exact
ruleValue_allGrammarRuleIds_exhaustive
polarity_accepts_guardDecision_table
guardDecision_allows_eq_accepts
terminalCursor_boundary_coercions_exact
tokensOwnedBy_exact
terminalAt_functional
terminalMatches_exact
matchedTerminal_eof_empty_span
boundaryByte_functional
consumedSpan_functional
consumedSpan_boundary_trivia_exact
consumedSpanWitness_compute
consumedSpanWitness_sourceLocates
sourceLocates_functional
matchedTerminal_identifier_projection_exact
matchedTerminal_identifier_projection_exists_unique
matchedTerminal_path_projection_exact
matchedTerminal_path_projection_exists_unique
matchedTerminal_external_projection_exact
matchedTerminal_external_projection_exists_unique
matchedTerminal_literal_projection_exact
matchedTerminal_literal_projection_exists_unique
matchedTerminal_assembly_projection_exact
matchedTerminal_assembly_projection_exists_unique
guard_context_cardinality
guard_instance_cardinality
guard_witness_cardinality
contextual_item_edge_cardinality
guard_anchor_functional
guard_evidence_functional
guard_evidence_total
unguardedReach_least
unguardedRecognizes_exact
greatestUnguardedEnd_functional
exactSlice_exact
delimiterRun_functional
matchingDelimiter_functional
armHeaderAt_same_frame
nearest_statement_region_functional
unguarded_chart_saturated_once
phaseBCorrect_iff_guardEvidence
guard_decisions_final_total
chart_phase_order
contextualReach_requires_phaseBCorrect
contextualReach_requires_allGuardsFinal
contextual_predict_scan_complete_closed
contextualReach_ordered
contextualPackedEdge_structural_equations
contextualEdgeReach_endpoints_reached
contextual_projection_no_anchor_mixing
chart_guard_witnesses_exact
actionReduces_eleven_shapes_exact
actionReduces_total
ActionReduces.functional
ruleReduction_seventyFive_exhaustive
ruleReduction_total
ruleReduction_functional
ruleReduction_source_backed
coherentPrefix_no_context_splice
coherentReduction_functional
sourceBackedRoot_exact
chart_unit_family_injective
chart_unit_family_complete
chart_greatest_cursor_exists
chart_expected_nonempty_on_failure
chart_expected_is_frontier_union
canonicalExpected_sorted_nodup_unique
foundAt_functional
explicit_group_resets_nonassociative_level
repeatedNonAssociative_coherent
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
ParseDiagnostic.Applies.functional
parse_diagnostic_constructors_exclusive
fast_guard_observation_congruent
fast_guard_slot_injective
fast_phaseB_correct
fast_phase_order
fast_guard_final_before_combine
parseTokens_eq_chartG
parseBound_sufficient

structure_sound
structure_complete
structural_diagnostics_canonical
structureBound_sufficient
astNodeMeasure_eq_astCarrier_cardinality

Parses.everyLocationValid
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
Solcore/Surface/Multi/ParserCore.lean
Solcore/Surface/Multi/ResourceBounds.lean
Solcore/Surface/Multi/ParserResourceAccounting.lean

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

`ParserCore.lean` imports `Grammar.lean` and owns `Boundary`, `TerminalCursor`,
their coercions, terminal lookup/matching, `GuardContext`, production/guard
instances, the structural `GuardAnchor` relation/decider,
`GuardMemoState`/`GuardMemo`/`AllGuardsFinal`, the checked
`GuardWitnessKey` subtype, raw/contextual item and edge keys,
structural-validity subtypes, the indexed EBNF/nonterminal/RHS value carriers,
all eleven typed action packers and their equations, `descendContext`,
`TokensOwnedBy`, `BoundaryByte`, `ConsumedSpan`, `ConsumedSpanWitness` and its
total `compute`, `sourceLoc`, `SourceLocates`, and `Expected.compare`. In particular, `GuardAnchor` and
`GuardWitnessKey` have no shadow definition in a judgment or executor. It
imports no judgment or executor.

`ParserResourceAccounting.lean` owns the public three-component fast-schedule
ledger, its exact equality with `parseBound`, and reduction theorems whose
premises state the still-missing executor correspondence and component bounds.
It does not expose the private `Chart.G` counter as fast-parser accounting.

`LexicalJudgment.lean` does not import `Lexer.lean`.
`ParserJudgment.lean`, `Chart.lean`, and `Parser.lean` each import the same
`ParserCore.lean`. `ParserJudgment.lean` owns `UnguardedReach`, delimiter and
guard evidence, `PhaseBCorrect`, judgment-level `GuardWitness` and production
enablement, contextual reach/edge reach, reduction,
`Parses`, and `ParseDiagnostic.Applies`; it does not import `Chart.lean` or
`Parser.lean`.
`StructureJudgment.lean` does not import `Structure.lean`.
`Lexer.lean`, `Chart.lean`, `Parser.lean`, and `Structure.lean` do not import
their sibling judgments. `Parser.lean` does not import `Chart.lean`; only
`Properties.lean` connects either executor to the declarative judgment and
proves that each sealed executor memo satisfies `PhaseBCorrect`, relates each
stored Core `GuardWitnessKey` to the judgment-level `GuardWitness`, and proves
their result equality. `CanonicalData.lean` imports no Surface or resolver
module. The public internal umbrella is added only after all correspondence,
certificate, fixture, and kernel audits pass.

`Grammar.lean` exclusively owns `GuardDecision` and the replacement
`Polarity.accepts : Polarity -> GuardDecision -> Bool`, with
`GuardDecision.allows` only as the definitionally equal argument-order alias.
An implementation that still exposes `Polarity -> Bool -> Bool` is not
conforming to this Accepted ADR. The repository now uses the closed
`GuardDecision` algebra and has passed the ParserCore closedness gate, so
`ParserJudgment.lean`, `Chart.lean`, and the total chart-based parser have been
implemented. Parser-wide location certification is also complete through
`Parses.everyLocationValid`. This milestone does not complete the still-missing
fast parser, final exact-token root closure and proof-argument-free facade,
canonical-standard parse certificates, or umbrella.

Implementation proceeds in this order:

1. neutral canonical raw bytes, strict UTF-8 decoding, source spans, located
   values, tokens, closed diagnostics, and the exact measures;
2. the independent lexical judgment and assembly-slice relation;
3. the pure maximal-munch lexer and its correspondence proofs;
4. the complete AST, checked EBNF expansion, stable production/action tables,
   shared `GuardDecision` algebra, replacement `Polarity.accepts`, and their
   exhaustive table checks, including every public dependent RHS bridge;
5. the shared `ParserCore` carriers, their structural validity equations,
   well-founded value family, eleven typed action packers, constructive
   location witnesses, exact 75-rule value mapping, and cardinality checks;
6. the independent parser judgment only after step 5 and the independent ADR
   closedness audit, then finite-chart `G`
   and the separate fast full-token parser, their phase barriers, bounds,
   correspondence, and exact result-equality proof; the fast schedule's public
   capacity ledger and numeric bound reduction are already present, while the
   counted executor connection remains;
7. independent structural acceptance and the structural validator;
8. parser-wide location certification (now complete), followed by exact token
   correspondence and the remaining diagnostic and resource theorems;
9. checked compatibility, strict UTF-8, byte-round-trip, and six-file standard
   certificates; and
10. the internal `Solcore.Surface.Multi` umbrella.

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
  priority guards, greatest-cursor contextual frontier unions, the
  repeated-nonassociative override, and unique reduction across every
  contextual packed derivation.
- Check the public Grammar RHS bridge for every production and all eleven
  typed action shapes; check that `RuleValue` covers the 75 displayed rule IDs
  exactly and that every branch of every `RuleReduction` row reduces to the
  stated constructor and span. Include absent/present option pairs, left/right
  fold directions, every `PostfixPartValue`, pass-through wrapper counts, the
  module full-file span, empty-arm fat-arrow-end span, and logical-EOF empty
  span.
- Test `TerminalMatches` independently: a contextual word is only the exact
  identifier spelling; identifier rejects every hard-keyword token; path
  component accepts valid identifier and hard-keyword spellings; decimal,
  hexadecimal, and string are exactly the literal categories; and only the
  logical EOF value matches EOF. Test `BoundaryByte` and `ConsumedSpan` across
  leading/inter-token/trailing trivia and UTF-8 token endpoints.
- For `G01`, test both `if (x) {}` statement priority and keyword-conditional
  expression priority. For `G03` through `G06` and `G09`, test both decision
  sides, including incomplete `comptime` prefixes that still take the marker
  side where the table requires it.
- For `G02`, separately test a recognized `| patterns =>` next-arm header, a
  non-header `|` used by bitwise-or parsing, and neutral ordinary-statement and
  arm-close cursors. Include empty, one-statement, and multiple-statement arm
  bodies and a nested match.
- For `G07`, test `.T(`, `f(`, `f.T(`, both call sites in `.T(x)(y)`, and
  `.T.x(`. A direct finite-chart fixture must give one raw dotted item two
  distinct postfix contexts and prove that neither its guard witness nor its
  completed edge can cross between them.
- For `G08`, test a final expression before a braced-body close, before a next
  arm, and before a match close; test a non-final unterminated expression; and
  include nested braced bodies and nested matches so the nearest-region theorem
  is observable.
- Check `GuardAnchor.functional`, `GuardEvidence.functional`, the
  positive/negative/neutral allowance table, contextual scan preservation,
  prediction descent, completion restoration, and the fast observation
  quotient on executable finite keys.
- Give `AllGuardsFinal` a deliberately all-neutral table and prove that it
  fails `PhaseBCorrect` on a non-neutral evidence fixture; then check that no
  contextual reach, edge, reduction, frontier, or diagnostic constructor can
  be formed from that table. Check structural edge validity separately from
  endpoint reach and reject an otherwise valid edge with an unreached `after`.
- Check the exhaustive `Polarity.accepts` table and definitional
  `GuardDecision.allows` alias from `Grammar.lean`; reject the obsolete
  `Polarity -> Bool -> Bool` signature at the module boundary.
- Instrument `Chart.G` to prove that Phase A saturates once, every Phase B cell
  advances from `undecided` to one final decision before any Phase C fact,
  Phase B emits no witness, and Phase C never recomputes raw recognition.
  Exercise every `L01`–`L14`, `R01`–`R02`, and `U01`–`U08` tag and check that
  the tagged injection is exhaustive and collision-free.
- Instrument the fast executor to prove that every guard memo is final before
  the first guarded candidate combine, and that absent/undecided cells never
  act as negative or neutral decisions.
- For G10, test mixed operators at each level, `(a < b) < c`,
  `a < b >= c`, `(a == b) != c`, `a == b < c < d`, `a && b < c < d`, a
  conditional branch containing `b < c < d`, and two contextual derivations
  with the same raw edge. Only the same coherent level-indexed
  `NonAssociativeFrontierValue` may supply the first operation, and an explicit
  source `.group` must reset the level.
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
open. The Accepted decision closes those design questions; an incompatible
change requires explicit review and must not be inferred from either comparison
implementation.

ADR-0016 must define structural syntax identity over
`Multi.CertifiedParsedModule`. ADR-0017 must define module/interface/scope
resolution, including same-name constructor classification and module-binding
validity. M2d must separately define type checking, overload and instance
selection, literal conversion, receiver selection, callability, assignment
targets, implicit final-expression meaning, Yul semantics, and elaboration to
Semantic Core. A publication ADR must separately define wire schemas, limits,
profiles, Oracle behavior, and comparison verdicts.
