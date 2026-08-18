import Solcore.Surface.Wire.V1.Diagnostic
import Solcore.Surface.Wire.V1.ParseResult
import Solcore.Surface.Wire.V1.Properties

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

/-!
Proof-facing connections between public Surface execution and the frozen v1
publication values.  This module does not define an Oracle protocol or JSON
representation.
-/

theorem diagnostic_of_lexer_source_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (failure :
      Solcore.Surface.Lexer.lex file =
        .error (.source error)) :
    ∃ diagnostic,
      ofLexError? file error = some diagnostic ∧
        diagnostic.toLexError? = some error := by
  obtain ⟨diagnostic, projection⟩ :=
    exists_ofLexError?_eq_some_of_lexer_failure file error failure
  exact ⟨
    diagnostic,
    projection,
    toLexError?_eq_some_of_ofLexError?_eq_some projection
  ⟩

theorem diagnostic_of_parseLexed_source_failure
    (file : Solcore.Surface.SourceFile)
    (lexed : Solcore.Surface.Lexed)
    (error : Solcore.Surface.ParseError)
    (failure :
      Solcore.Surface.Parser.parseLexed file lexed =
        .error (.source error)) :
    ∃ diagnostic,
      ofParseError? file error = some diagnostic ∧
        diagnostic.toParseError? = some error := by
  have wellFormed :=
    Solcore.Surface.Parser.parseLexed_source_failure_wellFormed
      file lexed error failure
  obtain ⟨diagnostic, projection⟩ :=
    exists_ofParseError?_eq_some_of_wellFormedFor
      file error wellFormed
  exact ⟨
    diagnostic,
    projection,
    toParseError?_eq_some_of_ofParseError?_eq_some projection
  ⟩

theorem diagnostic_of_frontend_syntactic_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.ParseError)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.syntactic error)) :
    ∃ diagnostic,
      ofFrontendError? file (.syntactic error) = some diagnostic ∧
        diagnostic.toFrontendError = .syntactic error := by
  have wellFormed :=
    Solcore.Surface.Parser.parse_syntactic_failure_wellFormed
      file error failure
  obtain ⟨diagnostic, projection⟩ :=
    exists_ofParseError?_eq_some_of_wellFormedFor
      file error wellFormed
  have frontendProjection :
      ofFrontendError? file (.syntactic error) = some diagnostic := by
    exact projection
  exact ⟨
    diagnostic,
    frontendProjection,
    toFrontendError_eq_of_ofFrontendError?_eq_some frontendProjection
  ⟩

theorem parseResult_of_parse_success
    (file : Solcore.Surface.SourceFile)
    (parsed : Solcore.Surface.ParsedFile)
    (success : Solcore.Surface.Parser.parse file = .ok parsed) :
    ∃ result,
      ParseResult.ofSurface? parsed = some result ∧
        result.toSurface = parsed := by
  obtain ⟨wire, projection⟩ :=
    File.projectable_of_parse_success file parsed success
  let result : ParseResult := { value := wire }
  refine ⟨result, ?_, ?_⟩
  · simp [ParseResult.ofSurface?, projection, result]
  · exact ParseResult.toSurface_eq_of_ofSurface?_eq_some
      (by simp [ParseResult.ofSurface?, projection, result])

theorem lexError_eq_of_diagnostic_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.LexError}
    {diagnostic : Diagnostic}
    (projection : ofLexError? file error = some diagnostic) :
    diagnostic.toFrontendError = .lexical error := by
  have frontendProjection :
      ofFrontendError? file (.lexical error) = some diagnostic := projection
  exact toFrontendError_eq_of_ofFrontendError?_eq_some frontendProjection

theorem parseError_eq_of_diagnostic_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.ParseError}
    {diagnostic : Diagnostic}
    (projection : ofParseError? file error = some diagnostic) :
    diagnostic.toFrontendError = .syntactic error := by
  have frontendProjection :
      ofFrontendError? file (.syntactic error) = some diagnostic := projection
  exact toFrontendError_eq_of_ofFrontendError?_eq_some frontendProjection

theorem parsedFile_eq_of_parseResult_projection
    {parsed : Solcore.Surface.ParsedFile}
    {result : ParseResult}
    (projection : ParseResult.ofSurface? parsed = some result) :
    result.toSurface = parsed :=
  ParseResult.toSurface_eq_of_ofSurface?_eq_some projection

/-!
The classifier below is an executable proof boundary, not a wire protocol.
Every defensive projection failure stays explicit and distinct from a source
rejection.  The following theorems show that public execution reaches none of
those defensive branches.
-/

inductive PublicationInternalFailure where
  | frontendInvariant (invariant : Solcore.Surface.FrontendInvariant)
  | diagnosticProjectionFailed (error : Solcore.Surface.FrontendError)
  | surfaceProjectionFailed (parsed : Solcore.Surface.ParsedFile)
  | unclassifiedFrontendError (error : Solcore.Surface.FrontendError)
  deriving Repr, BEq

inductive PublicationOutcome where
  | accepted (result : ParseResult)
  | rejected (diagnostic : Diagnostic)
  | internal (failure : PublicationInternalFailure)
  deriving Repr, BEq

set_option match.ignoreUnusedAlts true in
def classifyPublication
    (file : Solcore.Surface.SourceFile) : PublicationOutcome :=
  match Solcore.Surface.Parser.parse file with
  | .ok parsed =>
      match ParseResult.ofSurface? parsed with
      | some result => .accepted result
      | none => .internal (.surfaceProjectionFailed parsed)
  | .error (.lexical error) =>
      match ofLexError? file error with
      | some diagnostic => .rejected diagnostic
      | none => .internal (.diagnosticProjectionFailed (.lexical error))
  | .error (.syntactic error) =>
      match ofParseError? file error with
      | some diagnostic => .rejected diagnostic
      | none => .internal (.diagnosticProjectionFailed (.syntactic error))
  | .error (.internal invariant) =>
      .internal (.frontendInvariant invariant)
  | .error error =>
      .internal (.unclassifiedFrontendError error)

theorem classifyPublication_eq_accepted_of_parse_success
    (file : Solcore.Surface.SourceFile)
    (parsed : Solcore.Surface.ParsedFile)
    (success : Solcore.Surface.Parser.parse file = .ok parsed) :
    ∃ result,
      classifyPublication file = .accepted result ∧
        ParseResult.ofSurface? parsed = some result ∧
        result.toSurface = parsed := by
  obtain ⟨result, projection, reconstruction⟩ :=
    parseResult_of_parse_success file parsed success
  exact ⟨
    result,
    by simp [classifyPublication, success, projection],
    projection,
    reconstruction
  ⟩

private theorem lexer_failure_of_frontend_lexical_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.lexical error)) :
    Solcore.Surface.Lexer.lex file = .error (.source error) := by
  cases lexing : Solcore.Surface.Lexer.lex file with
  | ok lexed =>
      cases parsing : Solcore.Surface.Parser.parseLexed file lexed with
      | ok parsed =>
          simp [Solcore.Surface.Parser.parse, lexing, parsing] at failure
      | error parseFailure =>
          cases parseFailure <;>
            simp [Solcore.Surface.Parser.parse, lexing, parsing] at failure
  | error lexFailure =>
      cases lexFailure with
      | source actual =>
          simp [Solcore.Surface.Parser.parse, lexing] at failure
          cases failure
          rfl
      | internal invariant =>
          simp [Solcore.Surface.Parser.parse, lexing] at failure

theorem classifyPublication_eq_rejected_of_frontend_lexical_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.lexical error)) :
    ∃ diagnostic,
      classifyPublication file = .rejected diagnostic ∧
        ofLexError? file error = some diagnostic ∧
        diagnostic.toFrontendError = .lexical error := by
  have lexing :=
    lexer_failure_of_frontend_lexical_failure file error failure
  obtain ⟨diagnostic, projection, _⟩ :=
    diagnostic_of_lexer_source_failure file error lexing
  exact ⟨
    diagnostic,
    by simp [classifyPublication, failure, projection],
    projection,
    lexError_eq_of_diagnostic_projection projection
  ⟩

theorem classifyPublication_eq_rejected_of_frontend_syntactic_failure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.ParseError)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.syntactic error)) :
    ∃ diagnostic,
      classifyPublication file = .rejected diagnostic ∧
        ofParseError? file error = some diagnostic ∧
        diagnostic.toFrontendError = .syntactic error := by
  obtain ⟨diagnostic, frontendProjection, reconstruction⟩ :=
    diagnostic_of_frontend_syntactic_failure file error failure
  have projection : ofParseError? file error = some diagnostic :=
    frontendProjection
  exact ⟨
    diagnostic,
    by simp [classifyPublication, failure, projection],
    projection,
    reconstruction
  ⟩

theorem classifyPublication_eq_internal_of_frontend_invariant
    (file : Solcore.Surface.SourceFile)
    (invariant : Solcore.Surface.FrontendInvariant)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.internal invariant)) :
    classifyPublication file = .internal (.frontendInvariant invariant) := by
  simp [classifyPublication, failure]

end Solcore.Surface.Wire.V1
