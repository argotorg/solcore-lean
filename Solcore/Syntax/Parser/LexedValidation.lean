import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Parser.Diagnostic

/-! Executable provenance validation for already-tokenized syntax input. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace LexedValidation

/-- Validate token spans in source order, returning the first bad index. -/
def tokens (file : SourceFile) :
    Nat → Nat → List Token → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, token :: rest =>
      if token.span.isValidFor file &&
          previousEnd ≤ token.span.startByte &&
          token.span.startByte < token.span.endByte then
        tokens file (index + 1) token.span.endByte rest
      else
        .error (.invalidTokenSpan index token.span)

/-- Validate comment spans in source order, returning the first bad index. -/
def comments (file : SourceFile) :
    Nat → Nat → List Comment → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, comment :: rest =>
      if comment.span.isValidFor file &&
          previousEnd ≤ comment.span.startByte &&
          comment.span.startByte < comment.span.endByte then
        comments file (index + 1) comment.span.endByte rest
      else
        .error (.invalidCommentSpan index comment.span)

/-- Validate lexical-diagnostic ownership and UTF-8 boundaries in order. -/
def lexicalDiagnostics (file : SourceFile) :
    Nat → List LexicalDiagnostic → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, diagnostic :: rest =>
      if diagnostic.span.isValidFor file then
        lexicalDiagnostics file (index + 1) rest
      else
        .error (.invalidLexicalDiagnosticSpan index diagnostic.span)

end LexedValidation

/-- Validate all provenance consumed or retained by `parseLexed`. -/
def validateLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError Unit := do
  if lexed.source ≠ file.id then
    throw (.invalidLexedSource file.id lexed.source)
  LexedValidation.tokens file 0 0 lexed.tokens
  LexedValidation.comments file 0 0 lexed.comments
  LexedValidation.lexicalDiagnostics file 0 lexed.diagnostics

end Solcore.Syntax.Parser
