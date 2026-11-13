import Solcore.Syntax.Lexer

/-!
What the parser reports: `ParseDiagnostic`, `ParseDiagnosticKind`, `ParseExpectation`,
`ParserInvariantError`, `SyntaxInvariantError`.
-/

set_option autoImplicit false

namespace Solcore.Syntax

/-- Closed parser expectation catalog, independent of display prose. -/
inductive ParseExpectation where
  | endOfInput
  | identifier
  | yulIdentifier
  | coreLiteral
  | yulLiteral
  | typeExpr
  | expression
  | pattern
  | statement
  | topItem
  | modulePath
  | selectorName
  | exportName
  | keyword (value : HardKeyword)
  | contextual (value : ContextualKeyword)
  | symbol (value : Symbol)
  deriving Repr, BEq, DecidableEq

/-- Grammar context retained by an uncommitted parser rejection. -/
inductive ParseContext where
  | sourceFile
  | topItem
  | typeAlias
  | importDecl
  | exportDecl
  | pragmaDecl
  | typeExpr
  | parameter
  | expression
  | pattern
  | statement
  | yulExpression
  | yulStatement
  | contractMember
  deriving Repr, BEq, DecidableEq

/-- Site at which malformed tokens were consumed to resume parsing. -/
inductive RecoverySite where
  | topItem
  | contractMember
  | typeAliasValue
  | functionParameter
  | expressionAtom
  | pattern
  | yulExpression
  | yulStatement
  deriving Repr, BEq, DecidableEq

/-- Context-sensitive grammar conditions that are not token expectations. -/
inductive ParseConstraint where
  | mappingRequiresCanonicalForm
  | trailingSemicolonRequired (context : ParseContext)
  | namedParameterRequiresType
  | comptimeParameterRequiresType
  | comptimeTypeInParameter
  | comptimeUsedAsParameterName
  | modifierOutsideContract (keyword : HardKeyword)
  | yulMetaInSource
  | yulSwitchRequiresCase
  | expressionRequiresSemicolon
  | assignmentRequiresSemicolon
  | matchRequiresArm
  | matchArityMismatch (scrutinees patterns : Nat)
  | reservedDeriveTarget (keyword : HardKeyword)
  | deriveRequiresTarget
  | malformedDeriveAttribute
  | unclosedDeriveAttribute
  | deriveOnlyEnum
  | implicitPublicModifier (declaration : HardKeyword)
  | fallbackRequiresNoParameters
  /-- A size inside a type's brackets, `T[k]`: upstream's "fixed-size arrays
  `T[k]` are not supported; use `T[]`". -/
  | fixedSizeArray
  deriving Repr, BEq, DecidableEq

/-- Bounded recursive syntax dimensions. The preflight checks delimiters and
conditionals before recursive parsing, and the type parser checks array suffixes. -/
inductive NestingKind where
  | delimiter
  | conditional
  /-- A run of `[]` suffixes longer than `arraySuffixRoom`, which upstream
  counts against its type nesting limit. The parser checks it, not the
  preflight. -/
  | arraySuffix
  deriving Repr, BEq, DecidableEq

/-- Stable semantic categories for ordinary canonical parse diagnostics. -/
inductive ParseDiagnosticKind where
  | unexpected
      (found : Option TokenKind)
      (expected : NonemptyList ParseExpectation)
      (context : ParseContext)
  | invalidIdentifierHyphen (text : String)
  | constraintViolation (constraint : ParseConstraint)
  | recovered (site : RecoverySite)
  | nestingExceeded (kind : NestingKind) (limit : Nat)
  deriving Repr, BEq, DecidableEq

/-- One ordinary parser diagnostic paired with its exact source range. -/
structure ParseDiagnostic where
  span : SourceSpan
  kind : ParseDiagnosticKind
  deriving Repr, BEq, DecidableEq

/-- The longest run of `[]` suffixes upstream accepts on a type outside any
other type, 127: its nesting limit of 128 (`MAX_SYNTAX_NESTING`,
`crates/parser/src/parse/mod.rs:36`) less the type's own depth
(`crates/parser/src/parse/types.rs:205-214`). -/
def arraySuffixRoom : Nat := 127

/-- Upstream's "type nesting exceeds the compiler limit of 128", over a type
with more than `arraySuffixRoom` suffixes. -/
def arraySuffixNestingDiagnostic (span : SourceSpan) : ParseDiagnostic := {
  span
  kind := .nestingExceeded .arraySuffix (arraySuffixRoom + 1)
}

/-- Upstream's "fixed-size arrays `T[k]` are not supported; use `T[]`", over
the brackets of `T[k]`. -/
def fixedSizeArrayDiagnostic (span : SourceSpan) : ParseDiagnostic := {
  span
  kind := .constraintViolation .fixedSizeArray
}

/-- Executor phase named by an exceptional parser invariant. -/
inductive ParserPhase where
  | preflight
  | typeExpr
  | typeAlias
  | topLevel
  | expression
  | pattern
  | statement
  | yul
  deriving Repr, BEq, DecidableEq

/-- Failures of the total parser implementation rather than source errors. -/
inductive ParserInvariantError where
  | invalidLexedSource (expected actual : SourceId)
  | invalidTokenSpan (index : Nat) (span : SourceSpan)
  | invalidCommentSpan (index : Nat) (span : SourceSpan)
  | invalidLexicalDiagnosticSpan (index : Nat) (span : SourceSpan)
  | invalidWindow
      (cursor : Nat)
      (endIndex : Nat)
      (tokenCount : Nat)
  | fuelExhausted (phase : ParserPhase) (span : SourceSpan)
  | noProgress (phase : ParserPhase) (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- Internal failure of the lexer or parser composing the source frontend. -/
inductive SyntaxInvariantError where
  | lexerInvariant (diagnostic : LexicalDiagnostic)
  | parserInvariant (error : ParserInvariantError)
  deriving Repr, BEq, DecidableEq

end Solcore.Syntax
