import Solcore.Syntax.Lexer

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
  | keyword (value : HardKeyword)
  | contextual (value : ContextualKeyword)
  | symbol (value : Symbol)
  deriving Repr, BEq, DecidableEq

/-- Grammar context retained by an uncommitted parser rejection. -/
inductive ParseContext where
  | sourceFile
  | topItem
  | typeAlias
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
  deriving Repr, BEq, DecidableEq

/-- Bounded recursive syntax dimensions checked before recursive parsing. -/
inductive NestingKind where
  | delimiter
  | conditional
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
