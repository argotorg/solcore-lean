# ADR-0012: M2a Surface parser kernel

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M2 frontend

## Context

The published M1c reference boundary accepts a closed Semantic Core directly.
Source-level differential testing additionally requires a parser, resolver, and
elaborator for the same `.solc` workspace that is supplied to the Haskell and
Rust implementations. Those phases must not be collapsed into a compiler
lowering pipeline or introduced through an ad hoc Core-shaped source syntax.

The first frontend unit was audited against these pinned revisions:

- Haskell Solcore at
  `1d490d8bb5f374356f06e0720655496482eb1fb4`
- Rust Solcore at
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`

Both implementations accept a common fragment consisting of a top-level
function, initialized local bindings, a final return statement, calls,
conditionals, and precedence-structured expressions. They also expose behavior
that must not silently become normative.

- `true` and `false` are resolved as ordinary, shadowable names rather than
  irrevocable lexer literals.
- Polymorphic integer literals are converted through standard-library
  machinery, and current word conversions wrap modulo `2^256`.
- `wordNot`, `wordShl`, and `wordShr` have no source operators. They are exposed
  by the ordinary, shadowable standard-library functions `bnotWord`,
  `bshlWord`, and `bshrWord`.
- Both resolvers can leak branch-local bindings across statement branches.
- Haskell source offsets are character offsets even where fields are named as
  byte offsets.
- Existing parsers discard or overwrite some explicit grouping boundaries.

Name identity, shadowing, source integer elaboration, standard-library
resolution, and branch scope therefore require later decisions. Implementing
them in the first parser unit would conflate syntax with unresolved static
semantics.

## Decision

### Milestone boundary

M2a introduces a pure, total `Surface` lexer and parser only. It has no name
resolution, type checking, elaboration, or evaluation behavior.

The closed internal grammar is named
`solcore-surface-grammar/m2a-v1`. It is an implementation milestone analogous
to the pre-publication M1a kernel. It is not assigned to a published
`LanguageVersion`, profile, wire schema, or Oracle query in this change.
Oracle v1 source queries remain `unsupported`, and Oracle v2 and v3 remain
closed Core protocols.

This change starts, but does not declare completion of, the M2a proof work. The
Lean layer now includes independent maximal-munch lexer and full-token
difference-list parser judgments, plus executable conformance predicates for
source spans, grammar shape, and exact AST/token correspondence. Public lexer
success is gated by the lexical judgment. The private parser constructs its
`FileParses` derivation alongside the AST, and public parser success implies
that derivation and the conformance predicate for the exact lexer stream.
Relational determinism and lexer/parser fuel sufficiency are proved.

The reverse parser completeness theorem remains open: a canonical, conforming
`FileParses` derivation is not yet proved to make the executor succeed. Global
uniqueness of accepted lexical judgments and the connection from every public
lexer source failure to its reachable cursor-local rejection judgment also
remain explicit obligations.

A later publication ADR must add a new language version with
`grammarVersion = 1`, a version-local Surface wire schema, a frontend profile,
and a new Oracle version. Publication must not mutate any draft.1 through
draft.3 artifact.

### Source ownership and spans

A source file consists of a path and a Unicode `String`. Every token, comment,
name, operator, and syntax node carries a source span.

Spans are half-open UTF-8 byte ranges `[startByte, endByte)`. A valid span:

1. names the source file that owns it;
2. satisfies `startByte <= endByte`; and
3. satisfies `endByte <= source.utf8ByteSize`.

Token spans cover exactly the token lexeme. Line comments are terminated only
by LF or end of file. Their spans start at `//` and end before LF; in a CRLF
sequence, CR is part of the comment span and LF is not. A bare CR therefore
does not terminate a line comment. Block-comment spans include both delimiters.
A nested block comment produces one retained trivia record for the complete
outer comment, not a separate record for each nested delimiter pair.
Syntax-node spans include their explicit delimiters and exclude leading and
trailing trivia.

Grouping is represented by a distinct Surface constructor. Keyword
`if`/`then`/`else` conditionals are also distinct syntax. A future ternary
conditional must use a different constructor.

### Lexical grammar

M2a recognizes:

- ASCII space, tab, carriage return, line feed, and form feed as whitespace;
- `//` line comments;
- arbitrarily nested `/* ... */` block comments;
- ASCII identifiers matching `[A-Za-z][A-Za-z0-9_]*`;
- decimal literals matching `[0-9]+`;
- hexadecimal literals matching `0x[0-9A-Fa-f]+`;
- the delimiters and operators used by the grammar below.

The hard reserved words in this fragment are `function`, `let`, `if`, `else`,
and `return`. `then` is a contextual keyword. `bool` and `word` are contextual
type spellings. In all other name positions, `then`, `bool`, `word`, `true`,
and `false` remain identifiers. This preserves the distinction between parsing
and the later decision about prelude constructors and shadowing.

The lexer uses maximal munch. Multi-character operators are recognized before
their prefixes. Comments are retained as ordered span records, while
whitespace is discarded. Strings, Unicode identifiers, and all other token
families are outside the closed M2a grammar. Extending the identifier grammar
requires a Unicode-version decision and a new grammar version rather than a
host-library character predicate.

Lexing is fail-fast. The first invalid character or unterminated block comment
produces one structured lexical error and no token stream. Invalid characters
use code `SL0001` and span exactly that UTF-8 code point. Unterminated block
comments use code `SL0002` and span from the unmatched outer `/*` through end
of file.

Maximal munch is defined by the token regular languages rather than by an
additional malformed-number token. Consequently, `0x` tokenizes as decimal
`0` followed by identifier `x`, and `0x1g` tokenizes as hexadecimal `0x1`
followed by identifier `g`. The enclosing parser then reports the unexpected
adjacent token.

### Syntactic grammar

The following EBNF defines the complete M2a file grammar:

```text
file        ::= functionDecl EOF

functionDecl
            ::= "function" identifier "(" ")" "->" type
                "{" letStmt* returnStmt "}"

type        ::= "(" ")" | "bool" | "word"

letStmt     ::= "let" identifier ":" type "=" expression ";"
returnStmt  ::= "return" expression ";"

expression  ::= "if" expression "then" expression "else" expression
              | equality

equality    ::= relational (("==" | "!=") relational)?
relational  ::= bitOr (("<" | ">" | "<=" | ">=") bitOr)?
bitOr       ::= bitXor ("|" bitXor)*
bitXor      ::= bitAnd ("^" bitAnd)*
bitAnd      ::= additive ("&" additive)*
additive    ::= multiplicative (("+" | "-") multiplicative)*
multiplicative
            ::= unary (("*" | "/" | "%") unary)*
unary       ::= "!" unary | primary

primary     ::= "(" ")"
              | decimal
              | hexadecimal
              | identifier ("(" arguments? ")")?
              | "(" expression ")"

arguments   ::= expression ("," expression)*
```

Equality and relational operators are non-associative. The other listed binary
operators are left-associative. Binding strength, from strongest to weakest,
is `unary`, `multiplicative`, `additive`, `bitAnd`, `bitXor`, `bitOr`,
`relational`, `equality`, then keyword conditional. Each conditional operand
is a complete expression.

Calls are retained as generic name-and-argument syntax. Parsing a call does not
claim that functions, the standard library, or any primitive mapping is
supported. In particular, spelling a callee `bnotWord`, `bshlWord`, or
`bshrWord` does not make it an intrinsic.

The file wrapper has exactly one zero-argument function. Every local binding
has an explicit type and initializer, and the body ends in exactly one
value-returning statement. These restrictions create a stable fixture envelope;
they do not yet assign entry-point or Core elaboration semantics to that
function.

The executable parser is deterministic, consumes the complete non-trivia token
stream on success, and is fail-fast. Relational determinism is proved; the
reverse theorem that every suitable declarative derivation makes the executor
succeed remains open. Parser recursion is bounded by a termination measure
derived only from the finite token stream, not by a configurable semantic
resource limit. The input-derived bounds are proved sufficient.
`fuelExhausted` remains an internal parser invariant for defensive
classification, but public parsing proves it unreachable. It cannot produce
`SP0001` or any other source rejection.

An unexpected token uses code `SP0001` and that token's exact span. An
unexpected end of file uses code `SP0001` and the empty span at the source's
UTF-8 byte length. A repeated equality or relational operator at its
non-associative precedence uses code `SP0002` and the second operator's span.
These errors carry a structured expectation or operator; English diagnostic
prose is not normative.

### Explicit exclusions

M2a does not parse or decide:

- imports, exports, contracts, fields, modules, or multiple declarations;
- parameters, polymorphism, classes, instances, or comptime syntax;
- assignment, uninitialized bindings, statement conditionals, or control
  transfer other than the fixture's final return;
- lambdas, products other than unit, ADTs, matching, indexing, or field access;
- expression type annotations, ternary conditionals, `&&`, or `||`;
- string literals, assembly, or non-ASCII identifiers;
- the meaning, range, or type of an integer literal;
- whether `true` and `false` denote booleans;
- any source operator or name to Semantic Core mapping.

Failure to parse a construct outside this closed internal grammar is not yet a
language-level `rejected` verdict. No source query is published in M2a.

## Consequences

- Surface syntax can be developed and proved independently of name resolution
  and Core elaboration.
- The Lean implementation records actual UTF-8 byte positions even when a
  pinned compiler does not.
- Parentheses, raw literal radix and digits, call syntax, and conditional
  spelling remain available to later diagnostics and elaboration.
- Resolver ADRs can decide shadowing and structured identities without changing
  the parser AST silently.
- Source integer and standard-library behavior cannot enter Core merely through
  spelling-based shortcuts.
- M1c profiles, schemas, capabilities, and golden streams remain byte-for-byte
  unchanged.

## Conformance requirements

- Define the Surface source, token, comment, and AST types independently of
  Oracle wire types.
- Implement lexer and parser functions without `partial`, `unsafe`, IO,
  undeclared axioms, or host parser libraries.
- Give executable validity checks for source ownership and UTF-8 span bounds,
  with correspondence lemmas for their declarative predicates.
- Establish lexer progress and prove that every successfully lexed token and
  comment span is valid for its source.
- Establish that every successfully parsed AST span is valid and that the
  parser consumed all tokens.
- Preserve raw decimal and hexadecimal digits without converting them to a
  Core word.
- Test maximal munch, nested comments, unterminated comments, invalid
  characters, contextual `then`, and UTF-8 byte offsets.
- Test every precedence boundary, left associativity, non-associative operator
  rejection, explicit grouping, calls, and malformed fixture envelopes.
- Keep the Surface kernel under the repository's forbidden-declaration scan.
- Do not change any existing profile, schema, capability document, or golden
  byte manifest.
