import Solcore.Oracle.V4.Validation
import Solcore.Surface.Wire.V1.PublicationProperties

set_option autoImplicit false

namespace Solcore.Oracle.V4

/-!
The v4 handler consumes the proof-carrying request values from `Schema`. Raw
JSON validation is deliberately outside this module. Consequently every
response repeats the request identifier and selects a response body whose
query kind agrees with the request by construction.
-/

def frontendPhaseOfInvariant :
    Solcore.Surface.FrontendInvariant -> FrontendPhase
  | .lexer _ => .surfaceLexing
  | .parser _ => .surfaceParsing

def frontendPhaseOfError :
    Solcore.Surface.FrontendError -> FrontendPhase
  | .lexical _ => .surfaceLexing
  | .syntactic _ => .surfaceParsing
  | .internal invariant => frontendPhaseOfInvariant invariant

def internalErrorOfPublication :
    Solcore.Surface.Wire.V1.PublicationInternalFailure -> InternalError
  | .frontendInvariant invariant =>
      .frontendInvariant (frontendPhaseOfInvariant invariant)
  | .diagnosticProjectionFailed error =>
      .frontendInvariant (frontendPhaseOfError error)
  | .surfaceProjectionFailed _ => .surfaceWireProjectionFailed
  | .unclassifiedFrontendError error =>
      .frontendInvariant (frontendPhaseOfError error)

def parseVerdictOfPublication :
    Solcore.Surface.Wire.V1.PublicationOutcome -> ParseVerdict
  | .accepted result => .accepted result
  | .rejected diagnostic => .rejected diagnostic
  | .internal failure => .internalError (internalErrorOfPublication failure)

private theorem lexer_invariant_of_public_parse_failure
    (file : Solcore.Surface.SourceFile)
    (invariant : Solcore.Surface.LexerInvariant)
    (failure :
      Solcore.Surface.Parser.parse file =
        .error (.internal (.lexer invariant))) :
    Solcore.Surface.Lexer.lex file = .error (.internal invariant) := by
  cases lexing : Solcore.Surface.Lexer.lex file with
  | error lexFailure =>
      cases lexFailure with
      | source error =>
          simp [Solcore.Surface.Parser.parse, lexing] at failure
      | internal actual =>
          simp [Solcore.Surface.Parser.parse, lexing] at failure
          cases failure
          rfl
  | ok lexed =>
      cases parsing : Solcore.Surface.Parser.parseLexed file lexed with
      | ok parsed =>
          simp [Solcore.Surface.Parser.parse, lexing, parsing] at failure
      | error parseFailure =>
          cases parseFailure <;>
            simp [Solcore.Surface.Parser.parse, lexing, parsing] at failure

/-!
All defensive frontend invariants are unreachable through the public parser.
The lexer cases use its public validation theorems, and the parser cases use
the corresponding public input, output, and fuel theorems.
-/
theorem public_parse_ne_frontend_invariant
    (file : Solcore.Surface.SourceFile)
    (invariant : Solcore.Surface.FrontendInvariant) :
    Solcore.Surface.Parser.parse file ≠ .error (.internal invariant) := by
  cases invariant with
  | lexer lexerInvariant =>
      intro failure
      have lexing :=
        lexer_invariant_of_public_parse_failure file lexerInvariant failure
      cases lexerInvariant with
      | fuelExhausted span =>
          exact Solcore.Surface.Lexer.lex_ne_fuel_exhausted file span lexing
      | invalidOutput lexed =>
          exact Solcore.Surface.Lexer.lex_ne_invalid_output file lexed lexing
  | parser parserInvariant =>
      cases parserInvariant with
      | fuelExhausted phase span =>
          exact Solcore.Surface.Parser.parse_ne_parser_fuel_exhausted
            file phase span
      | invalidInput lexed =>
          exact Solcore.Surface.Parser.parse_ne_parser_invalid_input file lexed
      | invalidOutput parsed =>
          exact Solcore.Surface.Parser.parse_ne_parser_invalid_output file parsed

/-!
The defensive publication classifier is total, but its internal result is
unreachable for public draft.4 parsing. Successful trees always project, and
both source-failure families always produce their closed diagnostic value.
-/
theorem classifyPublication_ne_internal
    (file : Solcore.Surface.SourceFile)
    (internalFailure :
      Solcore.Surface.Wire.V1.PublicationInternalFailure) :
    Solcore.Surface.Wire.V1.classifyPublication file ≠
      .internal internalFailure := by
  intro classified
  cases parsing : Solcore.Surface.Parser.parse file with
  | ok parsed =>
      obtain ⟨result, accepted, _, _⟩ :=
        Solcore.Surface.Wire.V1.classifyPublication_eq_accepted_of_parse_success
          file parsed parsing
      rw [accepted] at classified
      cases classified
  | error error =>
      cases error with
      | lexical lexicalError =>
          obtain ⟨diagnostic, rejected, _, _⟩ :=
            Solcore.Surface.Wire.V1.classifyPublication_eq_rejected_of_frontend_lexical_failure
              file lexicalError parsing
          rw [rejected] at classified
          cases classified
      | syntactic parseError =>
          obtain ⟨diagnostic, rejected, _, _⟩ :=
            Solcore.Surface.Wire.V1.classifyPublication_eq_rejected_of_frontend_syntactic_failure
              file parseError parsing
          rw [rejected] at classified
          cases classified
      | internal invariant =>
          exact (public_parse_ne_frontend_invariant file invariant) parsing

theorem classifyPublication_accepted_provenance
    (file : Solcore.Surface.SourceFile)
    (result : Solcore.Surface.Wire.V1.ParseResult)
    (classified :
      Solcore.Surface.Wire.V1.classifyPublication file = .accepted result) :
    Solcore.Surface.Parser.parse file = .ok result.toSurface ∧
      Solcore.Surface.Wire.V1.ParseResult.ofSurface? result.toSurface =
        some result := by
  cases parsing : Solcore.Surface.Parser.parse file with
  | ok parsed =>
      cases projection :
          Solcore.Surface.Wire.V1.ParseResult.ofSurface? parsed with
      | none =>
          simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
            projection] at classified
      | some projected =>
          have projectedEq : projected = result := by
            simpa [Solcore.Surface.Wire.V1.classifyPublication, parsing,
              projection] using classified
          subst projected
          have reconstruction : result.toSurface = parsed :=
            Solcore.Surface.Wire.V1.ParseResult.toSurface_eq_of_ofSurface?_eq_some
              projection
          exact ⟨by rw [reconstruction],
            by simpa [reconstruction] using projection⟩
  | error error =>
      cases error with
      | lexical lexicalError =>
          cases projection :
              Solcore.Surface.Wire.V1.ofLexError? file lexicalError <;>
            simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
              projection] at classified
      | syntactic parseError =>
          cases projection :
              Solcore.Surface.Wire.V1.ofParseError? file parseError <;>
            simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
              projection] at classified
      | internal invariant =>
          simp [Solcore.Surface.Wire.V1.classifyPublication, parsing]
            at classified

theorem classifyPublication_rejected_provenance
    (file : Solcore.Surface.SourceFile)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic)
    (classified :
      Solcore.Surface.Wire.V1.classifyPublication file =
        .rejected diagnostic) :
    Solcore.Surface.Parser.parse file =
        .error diagnostic.toFrontendError ∧
      Solcore.Surface.Wire.V1.ofFrontendError?
          file diagnostic.toFrontendError = some diagnostic := by
  cases parsing : Solcore.Surface.Parser.parse file with
  | ok parsed =>
      cases projection :
          Solcore.Surface.Wire.V1.ParseResult.ofSurface? parsed <;>
        simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
          projection] at classified
  | error error =>
      cases error with
      | lexical lexicalError =>
          cases projection :
              Solcore.Surface.Wire.V1.ofLexError? file lexicalError with
          | none =>
              simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
                projection] at classified
          | some projected =>
              have projectedEq : projected = diagnostic := by
                simpa [Solcore.Surface.Wire.V1.classifyPublication, parsing,
                  projection] using classified
              subst projected
              have reconstruction :
                  diagnostic.toFrontendError = .lexical lexicalError :=
                Solcore.Surface.Wire.V1.lexError_eq_of_diagnostic_projection
                  projection
              exact ⟨by rw [reconstruction],
                by simpa [Solcore.Surface.Wire.V1.ofFrontendError?,
                  reconstruction] using projection⟩
      | syntactic parseError =>
          cases projection :
              Solcore.Surface.Wire.V1.ofParseError? file parseError with
          | none =>
              simp [Solcore.Surface.Wire.V1.classifyPublication, parsing,
                projection] at classified
          | some projected =>
              have projectedEq : projected = diagnostic := by
                simpa [Solcore.Surface.Wire.V1.classifyPublication, parsing,
                  projection] using classified
              subst projected
              have reconstruction :
                  diagnostic.toFrontendError = .syntactic parseError :=
                Solcore.Surface.Wire.V1.parseError_eq_of_diagnostic_projection
                  projection
              exact ⟨by rw [reconstruction],
                by simpa [Solcore.Surface.Wire.V1.ofFrontendError?,
                  reconstruction] using projection⟩
      | internal invariant =>
          simp [Solcore.Surface.Wire.V1.classifyPublication, parsing]
            at classified

/-!
`handleParse` performs the only v4 request-resource check. The measured demand
is exactly the UTF-8 byte length of source content; the opaque path label and
the request envelope are not inputs to this calculation.
-/
def handleParse (limits : Limits) (source : SourceInput) : ParseVerdict :=
  let consumed := source.content.utf8ByteSize
  if exceeded : limits.sourceBytes < consumed then
    .inconclusive {
      limit := limits.sourceBytes
      consumed
      exceeded
    }
  else
    parseVerdictOfPublication
      (Solcore.Surface.Wire.V1.classifyPublication source.toSurface)

theorem handleParse_validFor (limits : Limits) (source : SourceInput) :
    (handleParse limits source).ValidFor limits source := by
  unfold handleParse
  dsimp only
  split
  next exceeded =>
    exact ⟨rfl, rfl⟩
  next notExceeded =>
    have within : source.WithinLimit limits :=
      Nat.le_of_not_gt notExceeded
    cases classified :
        Solcore.Surface.Wire.V1.classifyPublication source.toSurface with
    | accepted result =>
        exact ParseVerdict.accepted_validFor_of_classified within classified
    | rejected diagnostic =>
        exact ParseVerdict.rejected_validFor_of_classified within classified
    | internal internalFailure =>
        exact False.elim
          ((classifyPublication_ne_internal
            source.toSurface internalFailure) classified)

def handleUnchecked (request : Request) : Response :=
  match request.query with
  | .capabilities => {
      id := request.id
      body := .capabilities (.accepted capabilityReport)
    }
  | .parse source => {
      id := request.id
      body := .parse (handleParse request.limits source)
    }

theorem handleUnchecked_validFor (request : Request) :
    (handleUnchecked request).ValidFor request := by
  rw [Response.validFor_iff_id_and_body]
  cases request with
  | mk id limits query =>
      cases query with
      | capabilities => exact ⟨rfl, rfl⟩
      | parse source => exact ⟨rfl, handleParse_validFor limits source⟩

@[simp] theorem handleUnchecked_isValidFor (request : Request) :
    (handleUnchecked request).isValidFor request = true :=
  (Response.isValidFor_eq_true_iff _ _).mpr
    (handleUnchecked_validFor request)

def oracleResponseInvariantResponse (request : Request) : Response :=
  match request.query with
  | .capabilities => {
      id := request.id
      body := .capabilities .oracleResponseInvariant
    }
  | .parse _ => {
      id := request.id
      body := .parse (.internalError .oracleResponseInvariant)
    }

theorem oracleResponseInvariantResponse_validFor (request : Request) :
    (oracleResponseInvariantResponse request).ValidFor request := by
  rw [Response.validFor_iff_id_and_body]
  cases request with
  | mk id limits query =>
      cases query <;> exact ⟨rfl, by simp [oracleResponseInvariantResponse,
        ResponseBody.ValidFor,
        CapabilitiesVerdict.Valid, ParseVerdict.ValidFor,
        InternalError.ValidFor, InternalError.ClosedCombination,
        InternalError.code, InternalError.phase]⟩

/-!
The public handler validates its complete request-relative response before it
crosses the protocol boundary. The closed invariant response is retained as a
defensive fallback, even though the proof below establishes that every public
candidate passes the executable validator.
-/
def handle (request : Request) : Response :=
  let candidate := handleUnchecked request
  if candidate.isValidFor request then
    candidate
  else
    oracleResponseInvariantResponse request

@[simp] theorem handle_eq_handleUnchecked (request : Request) :
    handle request = handleUnchecked request := by
  simp [handle]

theorem handle_validFor (request : Request) :
    (handle request).ValidFor request := by
  rw [handle_eq_handleUnchecked]
  exact handleUnchecked_validFor request

@[simp] theorem handle_capabilities
    (id : RequestId)
    (limits : Limits) :
    handle { id, limits, query := .capabilities } = {
      id
      body := .capabilities (.accepted capabilityReport)
    } := by
  rw [handle_eq_handleUnchecked]
  rfl

@[simp] theorem handle_parse
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput) :
    handle { id, limits, query := .parse source } = {
      id
      body := .parse (handleParse limits source)
    } := by
  rw [handle_eq_handleUnchecked]
  rfl

@[simp] theorem handle_id (request : Request) :
    (handle request).id = request.id := by
  rw [handle_eq_handleUnchecked]
  cases request with
  | mk id limits query =>
      cases query <;> rfl

@[simp] theorem handle_schema (request : Request) :
    (handle request).schema = schemaVersion := by
  rfl

@[simp] theorem handle_spec (request : Request) :
    (handle request).spec = Solcore.m2bLanguage.id := by
  rfl

@[simp] theorem handle_profile (request : Request) :
    (handle request).profile = ProfileRef.canonical := by
  rfl

@[simp] theorem handle_queryKind (request : Request) :
    (handle request).queryKind = request.queryKind := by
  rw [handle_eq_handleUnchecked]
  cases request with
  | mk id limits query =>
      cases query <;> rfl

theorem handle_envelope_preserved (request : Request) :
    (handle request).schema = request.schema ∧
      (handle request).id = request.id ∧
      (handle request).spec = request.spec ∧
      (handle request).profile = request.profile ∧
      (handle request).queryKind = request.queryKind := by
  rw [handle_eq_handleUnchecked]
  cases request with
  | mk id limits query =>
      cases query <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem handleParse_eq_inconclusive_of_exceeded
    (limits : Limits)
    (source : SourceInput)
    (exceeded : limits.sourceBytes < source.content.utf8ByteSize) :
    handleParse limits source = .inconclusive {
      limit := limits.sourceBytes
      consumed := source.content.utf8ByteSize
      exceeded
    } := by
  simp [handleParse, exceeded]

theorem handleParse_eq_publication_of_within_limit
    (limits : Limits)
    (source : SourceInput)
    (within : source.content.utf8ByteSize <= limits.sourceBytes) :
    handleParse limits source =
      parseVerdictOfPublication
        (Solcore.Surface.Wire.V1.classifyPublication source.toSurface) := by
  simp [handleParse, Nat.not_lt_of_ge within]

theorem handleParse_eq_publication_at_exact_limit
    (source : SourceInput) :
    handleParse { sourceBytes := source.content.utf8ByteSize } source =
      parseVerdictOfPublication
        (Solcore.Surface.Wire.V1.classifyPublication source.toSurface) := by
  exact handleParse_eq_publication_of_within_limit _ _ (Nat.le_refl _)

theorem handleParse_ne_inconclusive_of_within_limit
    (limits : Limits)
    (source : SourceInput)
    (within : source.content.utf8ByteSize <= limits.sourceBytes)
    (exhaustion : SourceBytesExceeded) :
    handleParse limits source ≠ .inconclusive exhaustion := by
  rw [handleParse_eq_publication_of_within_limit limits source within]
  cases Solcore.Surface.Wire.V1.classifyPublication source.toSurface <;>
    simp [parseVerdictOfPublication]

theorem handleParse_inconclusive_provenance
    (limits : Limits)
    (source : SourceInput)
    (exhaustion : SourceBytesExceeded)
    (handled : handleParse limits source = .inconclusive exhaustion) :
    limits.sourceBytes < source.content.utf8ByteSize ∧
      exhaustion.limit = limits.sourceBytes ∧
      exhaustion.consumed = source.content.utf8ByteSize := by
  unfold handleParse at handled
  dsimp only at handled
  split at handled
  next exceeded =>
    cases handled
    exact ⟨exceeded, rfl, rfl⟩
  next notExceeded =>
    cases classified :
        Solcore.Surface.Wire.V1.classifyPublication source.toSurface with
    | accepted result =>
        simp [parseVerdictOfPublication, classified] at handled
    | rejected diagnostic =>
        simp [parseVerdictOfPublication, classified] at handled
    | internal internalFailure =>
        simp [parseVerdictOfPublication, classified] at handled

theorem handleParse_is_inconclusive_iff
    (limits : Limits)
    (source : SourceInput) :
    (∃ exhaustion, handleParse limits source = .inconclusive exhaustion) ↔
      limits.sourceBytes < source.content.utf8ByteSize := by
  constructor
  · rintro ⟨exhaustion, handled⟩
    exact (handleParse_inconclusive_provenance
      limits source exhaustion handled).1
  · intro exceeded
    exact ⟨{
      limit := limits.sourceBytes
      consumed := source.content.utf8ByteSize
      exceeded
    }, handleParse_eq_inconclusive_of_exceeded limits source exceeded⟩

theorem handleParse_ne_internalError
    (limits : Limits)
    (source : SourceInput)
    (error : InternalError) :
    handleParse limits source ≠ .internalError error := by
  intro handled
  unfold handleParse at handled
  dsimp only at handled
  split at handled
  next exceeded =>
    simp at handled
  next notExceeded =>
    cases classified :
        Solcore.Surface.Wire.V1.classifyPublication source.toSurface with
    | accepted result =>
        simp [parseVerdictOfPublication, classified] at handled
    | rejected diagnostic =>
        simp [parseVerdictOfPublication, classified] at handled
    | internal internalFailure =>
        exact (classifyPublication_ne_internal
          source.toSurface internalFailure) classified

theorem handle_parse_eq_inconclusive_of_exceeded
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (exceeded : limits.sourceBytes < source.content.utf8ByteSize) :
    (handle { id, limits, query := .parse source }).body =
      .parse (.inconclusive {
        limit := limits.sourceBytes
        consumed := source.content.utf8ByteSize
        exceeded
      }) := by
  rw [handle_eq_handleUnchecked]
  change ResponseBody.parse (handleParse limits source) = _
  rw [handleParse_eq_inconclusive_of_exceeded limits source exceeded]

theorem handle_parse_accepted_of_parser_success
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (parsed : Solcore.Surface.ParsedFile)
    (within : source.content.utf8ByteSize <= limits.sourceBytes)
    (success :
      Solcore.Surface.Parser.parse source.toSurface = .ok parsed) :
    ∃ result,
      (handle { id, limits, query := .parse source }).body =
          .parse (.accepted result) ∧
        Solcore.Surface.Wire.V1.ParseResult.ofSurface? parsed = some result ∧
        result.toSurface = parsed := by
  obtain ⟨result, classified, projection, reconstruction⟩ :=
    Solcore.Surface.Wire.V1.classifyPublication_eq_accepted_of_parse_success
      source.toSurface parsed success
  refine ⟨result, ?_, projection, reconstruction⟩
  rw [handle_eq_handleUnchecked]
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.accepted result)
  rw [handleParse_eq_publication_of_within_limit limits source within]
  rw [classified]
  rfl

theorem handle_parse_rejected_of_frontend_lexical_failure
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (error : Solcore.Surface.LexError)
    (within : source.content.utf8ByteSize <= limits.sourceBytes)
    (failure :
      Solcore.Surface.Parser.parse source.toSurface =
        .error (.lexical error)) :
    ∃ diagnostic,
      (handle { id, limits, query := .parse source }).body =
          .parse (.rejected diagnostic) ∧
        Solcore.Surface.Wire.V1.ofLexError? source.toSurface error =
          some diagnostic ∧
        diagnostic.toFrontendError = .lexical error := by
  obtain ⟨diagnostic, classified, projection, reconstruction⟩ :=
    Solcore.Surface.Wire.V1.classifyPublication_eq_rejected_of_frontend_lexical_failure
        source.toSurface error failure
  refine ⟨diagnostic, ?_, projection, reconstruction⟩
  rw [handle_eq_handleUnchecked]
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.rejected diagnostic)
  rw [handleParse_eq_publication_of_within_limit limits source within]
  rw [classified]
  rfl

theorem handle_parse_rejected_of_frontend_syntactic_failure
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (error : Solcore.Surface.ParseError)
    (within : source.content.utf8ByteSize <= limits.sourceBytes)
    (failure :
      Solcore.Surface.Parser.parse source.toSurface =
        .error (.syntactic error)) :
    ∃ diagnostic,
      (handle { id, limits, query := .parse source }).body =
          .parse (.rejected diagnostic) ∧
        Solcore.Surface.Wire.V1.ofParseError? source.toSurface error =
          some diagnostic ∧
        diagnostic.toFrontendError = .syntactic error := by
  obtain ⟨diagnostic, classified, projection, reconstruction⟩ :=
    Solcore.Surface.Wire.V1.classifyPublication_eq_rejected_of_frontend_syntactic_failure
        source.toSurface error failure
  refine ⟨diagnostic, ?_, projection, reconstruction⟩
  rw [handle_eq_handleUnchecked]
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.rejected diagnostic)
  rw [handleParse_eq_publication_of_within_limit limits source within]
  rw [classified]
  rfl

theorem handle_parse_accepted_provenance
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (result : Solcore.Surface.Wire.V1.ParseResult)
    (handled :
      (handle { id, limits, query := .parse source }).body =
        .parse (.accepted result)) :
    source.content.utf8ByteSize <= limits.sourceBytes ∧
      Solcore.Surface.Parser.parse source.toSurface = .ok result.toSurface ∧
      Solcore.Surface.Wire.V1.ParseResult.ofSurface? result.toSurface =
        some result := by
  have valid := Response.validFor_body
    (handle_validFor { id, limits, query := .parse source })
  rw [handled] at valid
  exact ⟨valid.1, valid.2,
    Solcore.Surface.Wire.V1.ParseResult.ofSurface?_toSurface result⟩

theorem handle_parse_accepted_grammar_provenance
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (result : Solcore.Surface.Wire.V1.ParseResult)
    (handled :
      (handle { id, limits, query := .parse source }).body =
        .parse (.accepted result)) :
    ∃ lexed,
      Solcore.Surface.Lexer.lex source.toSurface = .ok lexed ∧
        Solcore.Surface.LexicalGrammar.Lexes source.toSurface lexed ∧
        Solcore.Surface.FileParses lexed result.toSurface ∧
        result.toSurface.ValidFor source.toSurface ∧
        result.toSurface.CorrespondsTo lexed ∧
        result.toSurface.GrammarValid := by
  have accepted : AcceptedResultValidFor source result :=
    (handle_parse_accepted_provenance
      id limits source result handled).2.1
  obtain ⟨lexed, lexing, lexical, parses⟩ :=
    acceptedResultValidFor_provenance accepted
  have conformance :=
    Solcore.Surface.FileParses.conformsTo_of_lexes
      source.toSurface parses lexical
  exact ⟨lexed, lexing, lexical, parses,
    acceptedResultValidFor_spans accepted,
    conformance.2.1,
    acceptedResultValidFor_grammar accepted⟩

theorem handle_parse_rejected_provenance
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic)
    (handled :
      (handle { id, limits, query := .parse source }).body =
        .parse (.rejected diagnostic)) :
    source.content.utf8ByteSize <= limits.sourceBytes ∧
      diagnostic.CanonicalFor source.toSurface ∧
      Solcore.Surface.Parser.parse source.toSurface =
        .error diagnostic.toFrontendError ∧
      Solcore.Surface.Wire.V1.ofFrontendError?
          source.toSurface diagnostic.toFrontendError = some diagnostic := by
  have valid := Response.validFor_body
    (handle_validFor { id, limits, query := .parse source })
  rw [handled] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2,
    Solcore.Surface.Wire.V1.ofFrontendError?_toFrontendError_of_canonicalFor
      source.toSurface diagnostic valid.2.1⟩

theorem handle_parse_inconclusive_provenance
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (exhaustion : SourceBytesExceeded)
    (handled :
      (handle { id, limits, query := .parse source }).body =
        .parse (.inconclusive exhaustion)) :
    limits.sourceBytes < source.content.utf8ByteSize ∧
      exhaustion.limit = limits.sourceBytes ∧
      exhaustion.consumed = source.content.utf8ByteSize := by
  rw [handle_eq_handleUnchecked] at handled
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.inconclusive exhaustion) at handled
  injection handled with handled
  exact handleParse_inconclusive_provenance limits source exhaustion handled

theorem handle_parse_ne_internalError
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (error : InternalError) :
    (handle { id, limits, query := .parse source }).body ≠
      .parse (.internalError error) := by
  intro handled
  rw [handle_eq_handleUnchecked] at handled
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.internalError error) at handled
  injection handled with handled
  exact (handleParse_ne_internalError limits source error) handled

theorem handle_parse_ne_frontendInvariant
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (phase : FrontendPhase) :
    (handle { id, limits, query := .parse source }).body ≠
      .parse (.internalError (.frontendInvariant phase)) :=
  handle_parse_ne_internalError id limits source (.frontendInvariant phase)

theorem handle_parse_ne_surfaceWireProjectionFailed
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput) :
    (handle { id, limits, query := .parse source }).body ≠
      .parse (.internalError .surfaceWireProjectionFailed) :=
  handle_parse_ne_internalError id limits source
    .surfaceWireProjectionFailed

theorem handle_parse_ne_oracleResponseInvariant
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput) :
    (handle { id, limits, query := .parse source }).body ≠
      .parse (.internalError .oracleResponseInvariant) :=
  handle_parse_ne_internalError id limits source .oracleResponseInvariant

theorem handle_parse_internal_of_frontend_invariant
    (id : RequestId)
    (limits : Limits)
    (source : SourceInput)
    (invariant : Solcore.Surface.FrontendInvariant)
    (within : source.content.utf8ByteSize <= limits.sourceBytes)
    (failure :
      Solcore.Surface.Parser.parse source.toSurface =
        .error (.internal invariant)) :
    (handle { id, limits, query := .parse source }).body =
      .parse (.internalError
        (.frontendInvariant (frontendPhaseOfInvariant invariant))) := by
  have classified :=
    Solcore.Surface.Wire.V1.classifyPublication_eq_internal_of_frontend_invariant
        source.toSurface invariant failure
  rw [handle_eq_handleUnchecked]
  change ResponseBody.parse (handleParse limits source) =
    ResponseBody.parse (.internalError
      (.frontendInvariant (frontendPhaseOfInvariant invariant)))
  rw [handleParse_eq_publication_of_within_limit limits source within]
  rw [classified]
  rfl

end Solcore.Oracle.V4
