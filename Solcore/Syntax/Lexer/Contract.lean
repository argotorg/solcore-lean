import Solcore.Syntax.Lexer.Result
import Solcore.Syntax.SpanSequence

set_option autoImplicit false

namespace Solcore.Syntax

namespace LexedFile

/-- Declarative provenance and source-order contract for lexical output. -/
structure ValidFor (lexed : LexedFile) (file : SourceFile) : Prop where
  source_eq : lexed.source = file.id
  tokens : SpanSequence.ValidFor file
    (fun token : Token => token.span) 0 lexed.tokens
  comments : SpanSequence.ValidFor file
    (fun comment : Comment => comment.span) 0 lexed.comments
  diagnostics : ∀ diagnostic ∈ lexed.diagnostics,
    diagnostic.span.ValidFor file

namespace ValidFor

theorem token_span {file : SourceFile} {lexed : LexedFile}
    (valid : lexed.ValidFor file) {token : Token}
    (member : token ∈ lexed.tokens) : token.span.ValidFor file :=
  SpanSequence.ValidFor.span_valid valid.tokens member

theorem comment_span {file : SourceFile} {lexed : LexedFile}
    (valid : lexed.ValidFor file) {comment : Comment}
    (member : comment ∈ lexed.comments) : comment.span.ValidFor file :=
  SpanSequence.ValidFor.span_valid valid.comments member

theorem diagnostic_span {file : SourceFile} {lexed : LexedFile}
    (valid : lexed.ValidFor file) {diagnostic : LexicalDiagnostic}
    (member : diagnostic ∈ lexed.diagnostics) :
    diagnostic.span.ValidFor file :=
  valid.diagnostics diagnostic member

end ValidFor

end LexedFile

end Solcore.Syntax
