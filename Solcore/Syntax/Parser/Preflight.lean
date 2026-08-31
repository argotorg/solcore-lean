import Solcore.Syntax.Parser.State

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def validateTokens (file : SourceFile) :
    Nat → Nat → List Token → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, token :: rest =>
      if token.span.isValidFor file &&
          previousEnd ≤ token.span.startByte &&
          token.span.startByte < token.span.endByte then
        validateTokens file (index + 1) token.span.endByte rest
      else
        .error (.invalidTokenSpan index token.span)

private def validateComments (file : SourceFile) :
    Nat → List Comment → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, comment :: rest =>
      if comment.span.isValidFor file &&
          comment.span.startByte < comment.span.endByte then
        validateComments file (index + 1) rest
      else
        .error (.invalidCommentSpan index comment.span)

private def validateLexicalDiagnostics (file : SourceFile) :
    Nat → List LexicalDiagnostic → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, diagnostic :: rest =>
      if diagnostic.span.isValidFor file then
        validateLexicalDiagnostics file (index + 1) rest
      else
        .error (.invalidLexicalDiagnosticSpan index diagnostic.span)

/-- Validate all provenance consumed or retained by `parseLexed`. -/
def validateLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError Unit := do
  if lexed.source != file.id then
    throw (.invalidLexedSource file.id lexed.source)
  validateTokens file 0 0 lexed.tokens
  validateComments file 0 lexed.comments
  validateLexicalDiagnostics file 0 lexed.diagnostics

end Solcore.Syntax.Parser
