import Solcore.Oracle.V4.Capabilities
import Solcore.Surface.Wire.V1.PublicationProperties

set_option autoImplicit false

namespace Solcore.Oracle.V4

open Solcore.Surface.Wire.V1

/-!
Executable, request-relative validation for closed Oracle v4 values.

The protocol types already make unknown schemas, profiles, queries, verdict
shapes, phases, resources, and internal-error combinations unrepresentable.
This module retains the corresponding envelope equations in `Response.ValidFor`
so the complete publication contract remains visible at its validation
boundary.  The checks that still depend on a request are the response ID and
query, the selected source-byte limit, and the exact source used to produce a
parse result or diagnostic.
-/

def SourceInput.WithinLimit (source : SourceInput) (limits : Limits) : Prop :=
  source.content.utf8ByteSize <= limits.sourceBytes

def SourceInput.isWithinLimit (source : SourceInput) (limits : Limits) : Bool :=
  decide (source.content.utf8ByteSize <= limits.sourceBytes)

@[simp] theorem SourceInput.isWithinLimit_eq_true_iff
    (source : SourceInput)
    (limits : Limits) :
    source.isWithinLimit limits = true ↔ source.WithinLimit limits := by
  simp [SourceInput.isWithinLimit, SourceInput.WithinLimit]

/-!
Surface expressions are recursive through both direct children and argument
lists.  The internal AST intentionally exposes only `BEq`, so the validation
boundary supplies a reflected equality procedure instead of assuming an
unproved law for that generated instance.
-/
mutual
  private def surfaceExprEqual :
      Solcore.Surface.Expr -> Solcore.Surface.Expr -> Bool
    | .unit first, .unit second => decide (first = second)
    | .integer first, .integer second => decide (first = second)
    | .name first, .name second => decide (first = second)
    | .group firstSpan first, .group secondSpan second =>
        decide (firstSpan = secondSpan) && surfaceExprEqual first second
    | .call firstSpan firstCallee firstArguments,
        .call secondSpan secondCallee secondArguments =>
        decide (firstSpan = secondSpan) &&
          decide (firstCallee = secondCallee) &&
          surfaceExprListEqual firstArguments secondArguments
    | .unary firstSpan firstOperator first,
        .unary secondSpan secondOperator second =>
        decide (firstSpan = secondSpan) &&
          decide (firstOperator = secondOperator) &&
          surfaceExprEqual first second
    | .binary firstSpan firstOperator firstLeft firstRight,
        .binary secondSpan secondOperator secondLeft secondRight =>
        decide (firstSpan = secondSpan) &&
          decide (firstOperator = secondOperator) &&
          surfaceExprEqual firstLeft secondLeft &&
          surfaceExprEqual firstRight secondRight
    | .ifThenElse firstSpan firstCondition firstThen firstElse,
        .ifThenElse secondSpan secondCondition secondThen secondElse =>
        decide (firstSpan = secondSpan) &&
          surfaceExprEqual firstCondition secondCondition &&
          surfaceExprEqual firstThen secondThen &&
          surfaceExprEqual firstElse secondElse
    | _, _ => false

  private def surfaceExprListEqual :
      List Solcore.Surface.Expr -> List Solcore.Surface.Expr -> Bool
    | [], [] => true
    | first :: firstRest, second :: secondRest =>
        surfaceExprEqual first second &&
          surfaceExprListEqual firstRest secondRest
    | _, _ => false
end

mutual
  private theorem surfaceExprEqual_eq_true_iff
      (first second : Solcore.Surface.Expr) :
      surfaceExprEqual first second = true ↔ first = second := by
    cases first <;> cases second <;>
      simp [surfaceExprEqual, surfaceExprEqual_eq_true_iff,
        surfaceExprListEqual_eq_true_iff, and_assoc]

  private theorem surfaceExprListEqual_eq_true_iff
      (first second : List Solcore.Surface.Expr) :
      surfaceExprListEqual first second = true ↔ first = second := by
    cases first <;> cases second <;>
      simp [surfaceExprListEqual, surfaceExprEqual_eq_true_iff,
        surfaceExprListEqual_eq_true_iff]
end

private def surfaceLetStatementEqual
    (first second : Solcore.Surface.LetStatement) : Bool :=
  decide (first.span = second.span) &&
    decide (first.name = second.name) &&
    decide (first.type = second.type) &&
    surfaceExprEqual first.value second.value

private theorem surfaceLetStatementEqual_eq_true_iff
    (first second : Solcore.Surface.LetStatement) :
    surfaceLetStatementEqual first second = true ↔ first = second := by
  cases first
  cases second
  simp [surfaceLetStatementEqual, surfaceExprEqual_eq_true_iff, and_assoc]

private def surfaceLetStatementListEqual :
    List Solcore.Surface.LetStatement ->
      List Solcore.Surface.LetStatement -> Bool
  | [], [] => true
  | first :: firstRest, second :: secondRest =>
      surfaceLetStatementEqual first second &&
        surfaceLetStatementListEqual firstRest secondRest
  | _, _ => false

private theorem surfaceLetStatementListEqual_eq_true_iff
    (first second : List Solcore.Surface.LetStatement) :
    surfaceLetStatementListEqual first second = true ↔ first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp [surfaceLetStatementListEqual]
  | cons head tail inductionHypothesis =>
      cases second with
      | nil => simp [surfaceLetStatementListEqual]
      | cons other rest =>
          simp [surfaceLetStatementListEqual,
            surfaceLetStatementEqual_eq_true_iff,
            inductionHypothesis]

private def surfaceReturnStatementEqual
    (first second : Solcore.Surface.ReturnStatement) : Bool :=
  decide (first.span = second.span) &&
    surfaceExprEqual first.value second.value

private theorem surfaceReturnStatementEqual_eq_true_iff
    (first second : Solcore.Surface.ReturnStatement) :
    surfaceReturnStatementEqual first second = true ↔ first = second := by
  cases first
  cases second
  simp [surfaceReturnStatementEqual, surfaceExprEqual_eq_true_iff]

private def surfaceFunctionDeclEqual
    (first second : Solcore.Surface.FunctionDecl) : Bool :=
  decide (first.span = second.span) &&
    decide (first.name = second.name) &&
    decide (first.returnType = second.returnType) &&
    surfaceLetStatementListEqual first.bindings second.bindings &&
    surfaceReturnStatementEqual first.result second.result

private theorem surfaceFunctionDeclEqual_eq_true_iff
    (first second : Solcore.Surface.FunctionDecl) :
    surfaceFunctionDeclEqual first second = true ↔ first = second := by
  cases first
  cases second
  simp [surfaceFunctionDeclEqual,
    surfaceLetStatementListEqual_eq_true_iff,
    surfaceReturnStatementEqual_eq_true_iff, and_assoc]

private def surfaceParsedFileEqual
    (first second : Solcore.Surface.ParsedFile) : Bool :=
  decide (first.span = second.span) &&
    surfaceFunctionDeclEqual first.function second.function &&
    decide (first.comments = second.comments)

private theorem surfaceParsedFileEqual_eq_true_iff
    (first second : Solcore.Surface.ParsedFile) :
    surfaceParsedFileEqual first second = true ↔ first = second := by
  cases first
  cases second
  simp [surfaceParsedFileEqual, surfaceFunctionDeclEqual_eq_true_iff,
    and_assoc]

def AcceptedResultValidFor
    (source : SourceInput)
    (result : Solcore.Surface.Wire.V1.ParseResult) : Prop :=
  Solcore.Surface.Parser.parse source.toSurface = .ok result.toSurface

def acceptedResultIsValidFor
    (source : SourceInput)
    (result : Solcore.Surface.Wire.V1.ParseResult) : Bool :=
  match Solcore.Surface.Parser.parse source.toSurface with
  | .ok parsed => surfaceParsedFileEqual parsed result.toSurface
  | .error _ => false

@[simp] theorem acceptedResultIsValidFor_eq_true_iff
    (source : SourceInput)
    (result : Solcore.Surface.Wire.V1.ParseResult) :
    acceptedResultIsValidFor source result = true ↔
      AcceptedResultValidFor source result := by
  unfold acceptedResultIsValidFor AcceptedResultValidFor
  split
  next parsed success =>
    rw [surfaceParsedFileEqual_eq_true_iff]
    simp [success]
  next error failure => simp [failure]

theorem acceptedResultValidFor_spans
    {source : SourceInput}
    {result : Solcore.Surface.Wire.V1.ParseResult}
    (valid : AcceptedResultValidFor source result) :
    result.toSurface.ValidFor source.toSurface :=
  Solcore.Surface.Parser.parse_success_spans_valid
    source.toSurface result.toSurface valid

theorem acceptedResultValidFor_grammar
    {source : SourceInput}
    {result : Solcore.Surface.Wire.V1.ParseResult}
    (valid : AcceptedResultValidFor source result) :
    result.toSurface.GrammarValid :=
  Solcore.Surface.Parser.parse_success_grammar_valid
    source.toSurface result.toSurface valid

theorem acceptedResultValidFor_provenance
    {source : SourceInput}
    {result : Solcore.Surface.Wire.V1.ParseResult}
    (valid : AcceptedResultValidFor source result) :
    ∃ lexed,
      Solcore.Surface.Lexer.lex source.toSurface = .ok lexed ∧
        Solcore.Surface.LexicalGrammar.Lexes source.toSurface lexed ∧
        Solcore.Surface.FileParses lexed result.toSurface := by
  obtain ⟨lexed, lexing, _, lexical, _, parses⟩ :=
    Solcore.Surface.Parser.parse_success_provenance
      source.toSurface result.toSurface valid
  exact ⟨lexed, lexing, lexical, parses⟩

theorem acceptedResultValidFor_of_classified
    {source : SourceInput}
    {result : ParseResult}
    (classified :
      classifyPublication source.toSurface = .accepted result) :
    AcceptedResultValidFor source result := by
  unfold classifyPublication at classified
  cases parsing : Solcore.Surface.Parser.parse source.toSurface with
  | ok parsed =>
      cases projection : ParseResult.ofSurface? parsed with
      | none => simp [parsing, projection] at classified
      | some projected =>
          simp [parsing, projection] at classified
          subst projected
          rw [AcceptedResultValidFor, parsing]
          congr 1
          exact (ParseResult.toSurface_eq_of_ofSurface?_eq_some
            projection).symm
  | error error =>
      cases error with
      | lexical lexicalError =>
          cases projection : ofLexError? source.toSurface lexicalError <;>
            simp [parsing, projection] at classified
      | syntactic parseError =>
          cases projection : ofParseError? source.toSurface parseError <;>
            simp [parsing, projection] at classified
      | internal invariant => simp [parsing] at classified

def diagnosticIsCanonicalFor
    (source : SourceInput)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) : Bool :=
  decide (diagnostic.display = none) &&
    match diagnostic.toFrontendError with
    | .lexical error =>
        decide (Solcore.Surface.LexicalGrammar.failureAt
            source.toSurface error.span.startByte = some error)
    | .syntactic error => error.isWellFormedFor source.toSurface
    | .internal _ => false

@[simp] theorem diagnosticIsCanonicalFor_eq_true_iff
    (source : SourceInput)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) :
    diagnosticIsCanonicalFor source diagnostic = true ↔
      diagnostic.CanonicalFor source.toSurface := by
  cases diagnostic with
  | mk primary kind display =>
      cases kind <;>
        simp [diagnosticIsCanonicalFor,
          Solcore.Surface.Wire.V1.Diagnostic.CanonicalFor,
          Solcore.Surface.Wire.V1.Diagnostic.ValidFor,
          Solcore.Surface.Wire.V1.Diagnostic.toFrontendError,
          Solcore.Surface.ParseError.isWellFormedFor_eq_true_iff]

theorem diagnostic_display_eq_none_of_lex_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.LexError}
    {diagnostic : Diagnostic}
    (projection : ofLexError? file error = some diagnostic) :
    diagnostic.display = none := by
  unfold ofLexError? at projection
  split at projection <;> rename_i recognized
  · cases error with
    | mk code span kind =>
        cases kind <;> simp_all
        all_goals rcases projection with ⟨_, rfl⟩
        all_goals rfl
  · simp at projection

theorem diagnostic_display_eq_none_of_parse_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.ParseError}
    {diagnostic : Diagnostic}
    (projection : ofParseError? file error = some diagnostic) :
    diagnostic.display = none := by
  unfold ofParseError? at projection
  split at projection <;> rename_i wellFormed
  · cases error with
    | mk code span kind =>
        cases kind with
        | expected expectation found =>
            simp only at projection
            cases expectationProjection :
                ParseExpectation.ofSurface? expectation with
            | none => simp [expectationProjection] at projection
            | some projectedExpectation =>
                rw [expectationProjection] at projection
                change ((match found with
                  | none => some none
                  | some kind => some <$> TokenKind.ofSurface? kind).bind
                    fun projectedFound =>
                      some ({
                        primary := SourceSpan.ofSurface span
                        kind := DiagnosticKind.expected
                          projectedExpectation projectedFound
                      } : Diagnostic)) = some diagnostic at projection
                cases found with
                | none =>
                    simp at projection
                    cases projection
                    rfl
                | some foundKind =>
                    cases foundProjection : TokenKind.ofSurface? foundKind <;>
                      simp [foundProjection] at projection
                    cases projection
                    rfl
        | nonAssociative operator =>
            generalize operatorEquation :
              NonAssociativeBinaryOp.ofSurface? operator =
                projectedOperator at projection
            cases projectedOperator <;> simp_all
            cases projection
            rfl
  · simp at projection

theorem diagnostic_canonicalFor_of_lex_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.LexError}
    {diagnostic : Diagnostic}
    (projection : ofLexError? file error = some diagnostic)
    (recognized :
      Solcore.Surface.LexicalGrammar.failureAt file error.span.startByte =
        some error) :
    diagnostic.CanonicalFor file := by
  have reconstruction :=
    toFrontendError_eq_of_ofFrontendError?_eq_some
      (file := file) (error := .lexical error) projection
  refine ⟨diagnostic_display_eq_none_of_lex_projection projection, ?_⟩
  rw [Diagnostic.ValidFor, reconstruction]
  exact recognized

theorem diagnostic_canonicalFor_of_parse_projection
    {file : Solcore.Surface.SourceFile}
    {error : Solcore.Surface.ParseError}
    {diagnostic : Diagnostic}
    (projection : ofParseError? file error = some diagnostic)
    (wellFormed : error.WellFormedFor file) :
    diagnostic.CanonicalFor file := by
  have reconstruction :=
    toFrontendError_eq_of_ofFrontendError?_eq_some
      (file := file) (error := .syntactic error) projection
  refine ⟨diagnostic_display_eq_none_of_parse_projection projection, ?_⟩
  rw [Diagnostic.ValidFor, reconstruction]
  exact wellFormed

private theorem lexerSourceFailure_of_parseLexicalFailure
    (file : Solcore.Surface.SourceFile)
    (error : Solcore.Surface.LexError)
    (failure :
      Solcore.Surface.Parser.parse file = .error (.lexical error)) :
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

def RejectedDiagnosticValidFor
    (source : SourceInput)
    (diagnostic : Diagnostic) : Prop :=
  diagnostic.CanonicalFor source.toSurface ∧
    Solcore.Surface.Parser.parse source.toSurface =
      .error diagnostic.toFrontendError

theorem rejectedDiagnosticValidFor_of_classified
    {source : SourceInput}
    {diagnostic : Diagnostic}
    (classified :
      classifyPublication source.toSurface = .rejected diagnostic) :
    RejectedDiagnosticValidFor source diagnostic := by
  unfold classifyPublication at classified
  cases parsing : Solcore.Surface.Parser.parse source.toSurface with
  | ok parsed =>
      cases projection : ParseResult.ofSurface? parsed <;>
        simp [parsing, projection] at classified
  | error error =>
      cases error with
      | lexical lexicalError =>
          cases projection : ofLexError? source.toSurface lexicalError with
          | none => simp [parsing, projection] at classified
          | some projected =>
              simp [parsing, projection] at classified
              subst projected
              have reconstruction :=
                toFrontendError_eq_of_ofFrontendError?_eq_some
                  (file := source.toSurface)
                  (error := .lexical lexicalError) projection
              refine ⟨?_, ?_⟩
              · have lexing :=
                  lexerSourceFailure_of_parseLexicalFailure
                    source.toSurface lexicalError parsing
                exact diagnostic_canonicalFor_of_lex_projection projection
                  (Solcore.Surface.Lexer.lex_source_failure_recognized
                    source.toSurface lexicalError lexing)
              · rw [reconstruction]
                exact parsing
      | syntactic parseError =>
          cases projection : ofParseError? source.toSurface parseError with
          | none => simp [parsing, projection] at classified
          | some projected =>
              simp [parsing, projection] at classified
              subst projected
              have reconstruction :=
                toFrontendError_eq_of_ofFrontendError?_eq_some
                  (file := source.toSurface)
                  (error := .syntactic parseError) projection
              refine ⟨?_, ?_⟩
              · exact diagnostic_canonicalFor_of_parse_projection projection
                  (Solcore.Surface.Parser.parse_syntactic_failure_wellFormed
                    source.toSurface parseError parsing)
              · rw [reconstruction]
                exact parsing
      | internal invariant => simp [parsing] at classified

private def frontendErrorMatchesDiagnostic
    (error : Solcore.Surface.FrontendError)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) : Bool :=
  match error, diagnostic.toFrontendError with
  | .lexical actual, .lexical expected => decide (actual = expected)
  | .syntactic actual, .syntactic expected => decide (actual = expected)
  | _, _ => false

private theorem frontendErrorMatchesDiagnostic_eq_true_iff
    (error : Solcore.Surface.FrontendError)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) :
    frontendErrorMatchesDiagnostic error diagnostic = true ↔
      error = diagnostic.toFrontendError := by
  cases error <;> cases diagnostic with
  | mk primary kind display =>
      cases kind <;>
        simp [frontendErrorMatchesDiagnostic,
          Solcore.Surface.Wire.V1.Diagnostic.toFrontendError]

def rejectedDiagnosticIsValidFor
    (source : SourceInput)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) : Bool :=
  diagnosticIsCanonicalFor source diagnostic &&
    match Solcore.Surface.Parser.parse source.toSurface with
    | .error error => frontendErrorMatchesDiagnostic error diagnostic
    | .ok _ => false

@[simp] theorem rejectedDiagnosticIsValidFor_eq_true_iff
    (source : SourceInput)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) :
    rejectedDiagnosticIsValidFor source diagnostic = true ↔
      RejectedDiagnosticValidFor source diagnostic := by
  unfold rejectedDiagnosticIsValidFor RejectedDiagnosticValidFor
  rw [Bool.and_eq_true]
  rw [diagnosticIsCanonicalFor_eq_true_iff]
  constructor
  · rintro ⟨canonical, matching⟩
    refine ⟨canonical, ?_⟩
    split at matching
    next actual failure =>
      rw [frontendErrorMatchesDiagnostic_eq_true_iff] at matching
      rw [failure, matching]
    next parsed success => exact Bool.noConfusion matching
  · rintro ⟨canonical, matching⟩
    refine ⟨canonical, ?_⟩
    simp only [matching]
    exact (frontendErrorMatchesDiagnostic_eq_true_iff
      diagnostic.toFrontendError diagnostic).mpr rfl

namespace SourceBytesExceeded

def ValidFor
    (exhaustion : SourceBytesExceeded)
    (limits : Limits)
    (source : SourceInput) : Prop :=
  exhaustion.limit = limits.sourceBytes ∧
    exhaustion.consumed = source.content.utf8ByteSize

def isValidFor
    (exhaustion : SourceBytesExceeded)
    (limits : Limits)
    (source : SourceInput) : Bool :=
  decide (exhaustion.limit = limits.sourceBytes) &&
    decide (exhaustion.consumed = source.content.utf8ByteSize)

@[simp] theorem isValidFor_eq_true_iff
    (exhaustion : SourceBytesExceeded)
    (limits : Limits)
    (source : SourceInput) :
    exhaustion.isValidFor limits source = true ↔
      exhaustion.ValidFor limits source := by
  simp [isValidFor, ValidFor]

theorem validFor_exact_demand_exceeds_limit
    {exhaustion : SourceBytesExceeded}
    {limits : Limits}
    {source : SourceInput}
    (valid : exhaustion.ValidFor limits source) :
    limits.sourceBytes < source.content.utf8ByteSize := by
  rw [← valid.1, ← valid.2]
  exact exhaustion.exceeded

theorem validFor_not_within_limit
    {exhaustion : SourceBytesExceeded}
    {limits : Limits}
    {source : SourceInput}
    (valid : exhaustion.ValidFor limits source) :
    ¬ source.WithinLimit limits := by
  exact Nat.not_le_of_gt (validFor_exact_demand_exceeds_limit valid)

/-!
Unlike Oracle v2 and v3 resource accounting, v4 preflight reports exact
demand.  Consequently `consumed` is strictly greater than `limit`; no
`consumed <= limit` premise belongs to this validator.
-/
theorem validFor_consumed_gt_limit
    {exhaustion : SourceBytesExceeded}
    {limits : Limits}
    {source : SourceInput}
    (_valid : exhaustion.ValidFor limits source) :
    exhaustion.limit < exhaustion.consumed :=
  exhaustion.exceeded

end SourceBytesExceeded

namespace InternalError

/-!
All legal phase/code pairs are already selected by the closed constructor.
This proposition records that redundancy at the proof boundary.
-/
def ClosedCombination (error : InternalError) : Prop :=
  match error with
  | .frontendInvariant phase =>
      error.code = "frontend-invariant" ∧
        error.phase = some phase.toPhase
  | .surfaceWireProjectionFailed =>
      error.code = "surface-wire-projection-failed" ∧
        error.phase = some .surfaceEncoding
  | .oracleResponseInvariant =>
      error.code = "oracle-response-invariant" ∧
        error.phase = none

def hasClosedCombination (error : InternalError) : Bool :=
  match error with
  | .frontendInvariant phase =>
      decide (error.code = "frontend-invariant") &&
        decide (error.phase = some phase.toPhase)
  | .surfaceWireProjectionFailed =>
      decide (error.code = "surface-wire-projection-failed") &&
        decide (error.phase = some .surfaceEncoding)
  | .oracleResponseInvariant =>
      decide (error.code = "oracle-response-invariant") &&
        decide (error.phase = none)

@[simp] theorem hasClosedCombination_eq_true_iff (error : InternalError) :
    error.hasClosedCombination = true ↔ error.ClosedCombination := by
  cases error <;> simp [hasClosedCombination, ClosedCombination, code, phase]

@[simp] theorem closedCombination (error : InternalError) :
    error.ClosedCombination := by
  cases error <;> simp [ClosedCombination, code, phase]

def ValidFor
    (error : InternalError)
    (limits : Limits)
    (source : SourceInput) : Prop :=
  error.ClosedCombination ∧
    match error with
    | .frontendInvariant _ | .surfaceWireProjectionFailed =>
        source.WithinLimit limits
    | .oracleResponseInvariant => True

def isValidFor
    (error : InternalError)
    (limits : Limits)
    (source : SourceInput) : Bool :=
  error.hasClosedCombination &&
    match error with
    | .frontendInvariant _ | .surfaceWireProjectionFailed =>
        source.isWithinLimit limits
    | .oracleResponseInvariant => true

@[simp] theorem isValidFor_eq_true_iff
    (error : InternalError)
    (limits : Limits)
    (source : SourceInput) :
    error.isValidFor limits source = true ↔ error.ValidFor limits source := by
  cases error <;>
    simp [isValidFor, ValidFor, SourceInput.isWithinLimit_eq_true_iff]

end InternalError

namespace CapabilityReport

def Canonical (report : CapabilityReport) : Prop :=
  report = capabilityReport

def isCanonical (report : CapabilityReport) : Bool :=
  match report with
  | .canonical => true

@[simp] theorem isCanonical_eq_true_iff (report : CapabilityReport) :
    report.isCanonical = true ↔ report.Canonical := by
  cases report
  simp [isCanonical, Canonical, capabilityReport]

@[simp] theorem allCanonical (report : CapabilityReport) : report.Canonical := by
  cases report
  simp [Canonical, capabilityReport]

end CapabilityReport

namespace CapabilitiesVerdict

def Valid (verdict : CapabilitiesVerdict) : Prop :=
  match verdict with
  | .accepted report => report.Canonical
  | .oracleResponseInvariant => True

def isValid (verdict : CapabilitiesVerdict) : Bool :=
  match verdict with
  | .accepted report => report.isCanonical
  | .oracleResponseInvariant => true

@[simp] theorem isValid_eq_true_iff (verdict : CapabilitiesVerdict) :
    verdict.isValid = true ↔ verdict.Valid := by
  cases verdict <;> simp [isValid, Valid]

@[simp] theorem canonicalAccepted_valid :
    (CapabilitiesVerdict.accepted capabilityReport).Valid := by
  simp [Valid]

@[simp] theorem oracleResponseInvariant_valid :
    CapabilitiesVerdict.oracleResponseInvariant.Valid := by
  simp [Valid]

end CapabilitiesVerdict

namespace ParseVerdict

def ValidFor
    (verdict : ParseVerdict)
    (limits : Limits)
    (source : SourceInput) : Prop :=
  match verdict with
  | .accepted result =>
      source.WithinLimit limits ∧ AcceptedResultValidFor source result
  | .rejected diagnostic =>
      source.WithinLimit limits ∧ RejectedDiagnosticValidFor source diagnostic
  | .inconclusive exhaustion => exhaustion.ValidFor limits source
  | .internalError error => error.ValidFor limits source

def isValidFor
    (verdict : ParseVerdict)
    (limits : Limits)
    (source : SourceInput) : Bool :=
  match verdict with
  | .accepted result =>
      source.isWithinLimit limits && acceptedResultIsValidFor source result
  | .rejected diagnostic =>
      source.isWithinLimit limits &&
        rejectedDiagnosticIsValidFor source diagnostic
  | .inconclusive exhaustion => exhaustion.isValidFor limits source
  | .internalError error => error.isValidFor limits source

@[simp] theorem isValidFor_eq_true_iff
    (verdict : ParseVerdict)
    (limits : Limits)
    (source : SourceInput) :
    verdict.isValidFor limits source = true ↔ verdict.ValidFor limits source := by
  cases verdict <;>
    simp [isValidFor, ValidFor, SourceInput.isWithinLimit_eq_true_iff]

theorem accepted_validFor_iff
    (result : Solcore.Surface.Wire.V1.ParseResult)
    (limits : Limits)
    (source : SourceInput) :
    (ParseVerdict.accepted result).ValidFor limits source ↔
      source.content.utf8ByteSize <= limits.sourceBytes ∧
        Solcore.Surface.Parser.parse source.toSurface =
          .ok result.toSurface := by
  rfl

theorem rejected_validFor_iff
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic)
    (limits : Limits)
    (source : SourceInput) :
    (ParseVerdict.rejected diagnostic).ValidFor limits source ↔
      source.content.utf8ByteSize <= limits.sourceBytes ∧
        diagnostic.CanonicalFor source.toSurface ∧
        Solcore.Surface.Parser.parse source.toSurface =
          .error diagnostic.toFrontendError := by
  rfl

@[simp] theorem rejected_phase_matches_diagnostic
    (diagnostic : Diagnostic) :
    (ParseVerdict.rejected diagnostic).phase =
      some (FrontendPhase.ofDiagnosticPhase diagnostic.phase).toPhase := by
  rfl

theorem accepted_validFor_spans
    {result : ParseResult}
    {limits : Limits}
    {source : SourceInput}
    (valid : (ParseVerdict.accepted result).ValidFor limits source) :
    result.toSurface.ValidFor source.toSurface :=
  acceptedResultValidFor_spans valid.2

theorem accepted_validFor_grammar
    {result : ParseResult}
    {limits : Limits}
    {source : SourceInput}
    (valid : (ParseVerdict.accepted result).ValidFor limits source) :
    result.toSurface.GrammarValid :=
  acceptedResultValidFor_grammar valid.2

theorem rejected_validFor_canonical
    {diagnostic : Diagnostic}
    {limits : Limits}
    {source : SourceInput}
    (valid : (ParseVerdict.rejected diagnostic).ValidFor limits source) :
    diagnostic.CanonicalFor source.toSurface :=
  valid.2.1

theorem rejected_validFor_exact_failure
    {diagnostic : Diagnostic}
    {limits : Limits}
    {source : SourceInput}
    (valid : (ParseVerdict.rejected diagnostic).ValidFor limits source) :
    Solcore.Surface.Parser.parse source.toSurface =
      .error diagnostic.toFrontendError :=
  valid.2.2

theorem inconclusive_validFor_iff
    (exhaustion : SourceBytesExceeded)
    (limits : Limits)
    (source : SourceInput) :
    (ParseVerdict.inconclusive exhaustion).ValidFor limits source ↔
      exhaustion.limit = limits.sourceBytes ∧
        exhaustion.consumed = source.content.utf8ByteSize := by
  rfl

theorem accepted_validFor_of_classified
    {result : ParseResult}
    {limits : Limits}
    {source : SourceInput}
    (within : source.WithinLimit limits)
    (classified : classifyPublication source.toSurface = .accepted result) :
    (ParseVerdict.accepted result).ValidFor limits source :=
  ⟨within, acceptedResultValidFor_of_classified classified⟩

theorem rejected_validFor_of_classified
    {diagnostic : Diagnostic}
    {limits : Limits}
    {source : SourceInput}
    (within : source.WithinLimit limits)
    (classified :
      classifyPublication source.toSurface = .rejected diagnostic) :
    (ParseVerdict.rejected diagnostic).ValidFor limits source :=
  ⟨within, rejectedDiagnosticValidFor_of_classified classified⟩

theorem inconclusive_validFor_of_exact_measurement
    {exhaustion : SourceBytesExceeded}
    {limits : Limits}
    {source : SourceInput}
    (limit : exhaustion.limit = limits.sourceBytes)
    (consumed :
      exhaustion.consumed = source.content.utf8ByteSize) :
    (ParseVerdict.inconclusive exhaustion).ValidFor limits source :=
  ⟨limit, consumed⟩

@[simp] theorem oracleResponseInvariant_validFor
    (limits : Limits)
    (source : SourceInput) :
    (ParseVerdict.internalError .oracleResponseInvariant).ValidFor
      limits source := by
  simp [ValidFor, InternalError.ValidFor]

end ParseVerdict

namespace ResponseBody

def ValidFor (body : ResponseBody) (request : Request) : Prop :=
  match request.query, body with
  | .capabilities, .capabilities verdict => verdict.Valid
  | .parse source, .parse verdict => verdict.ValidFor request.limits source
  | _, _ => False

def isValidFor (body : ResponseBody) (request : Request) : Bool :=
  match request.query, body with
  | .capabilities, .capabilities verdict => verdict.isValid
  | .parse source, .parse verdict => verdict.isValidFor request.limits source
  | _, _ => false

@[simp] theorem isValidFor_eq_true_iff
    (body : ResponseBody)
    (request : Request) :
    body.isValidFor request = true ↔ body.ValidFor request := by
  cases request with
  | mk id limits query =>
      cases query <;> cases body <;>
        simp [isValidFor, ValidFor]

theorem validFor_queryKind
    {body : ResponseBody}
    {request : Request}
    (valid : body.ValidFor request) :
    body.queryKind = request.queryKind := by
  cases request with
  | mk id limits query =>
      cases query <;> cases body <;>
        simp [ValidFor, ResponseBody.queryKind, Request.queryKind,
          Query.kind] at valid ⊢

end ResponseBody

namespace Response

def ValidFor (response : Response) (request : Request) : Prop :=
  response.schema = request.schema ∧
    response.id = request.id ∧
    response.spec = request.spec ∧
    response.profile = request.profile ∧
    response.queryKind = request.queryKind ∧
    response.body.ValidFor request

def isValidFor (response : Response) (request : Request) : Bool :=
  decide (response.schema = request.schema) &&
    decide (response.id = request.id) &&
    decide (response.spec = request.spec) &&
    decide (response.profile = request.profile) &&
    decide (response.queryKind = request.queryKind) &&
    response.body.isValidFor request

@[simp] theorem isValidFor_eq_true_iff
    (response : Response)
    (request : Request) :
    response.isValidFor request = true ↔ response.ValidFor request := by
  simp [isValidFor, ValidFor, ResponseBody.isValidFor_eq_true_iff,
    and_assoc]

theorem validFor_id
    {response : Response}
    {request : Request}
    (valid : response.ValidFor request) :
    response.id = request.id :=
  valid.2.1

theorem validFor_queryKind
    {response : Response}
    {request : Request}
    (valid : response.ValidFor request) :
    response.queryKind = request.queryKind :=
  valid.2.2.2.2.1

theorem validFor_body
    {response : Response}
    {request : Request}
    (valid : response.ValidFor request) :
    response.body.ValidFor request :=
  valid.2.2.2.2.2

theorem fixed_envelope
    (response : Response)
    (request : Request) :
    response.schema = request.schema ∧
      response.spec = request.spec ∧
      response.profile = request.profile := by
  exact ⟨rfl, rfl, rfl⟩

theorem validFor_iff_id_and_body
    (response : Response)
    (request : Request) :
    response.ValidFor request ↔
      response.id = request.id ∧ response.body.ValidFor request := by
  constructor
  · intro valid
    exact ⟨validFor_id valid, validFor_body valid⟩
  · rintro ⟨idMatches, bodyValid⟩
    have queryMatches := ResponseBody.validFor_queryKind bodyValid
    exact ⟨rfl, idMatches, rfl, rfl, queryMatches, bodyValid⟩

end Response

end Solcore.Oracle.V4
