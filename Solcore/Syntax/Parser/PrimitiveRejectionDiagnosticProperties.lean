import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.Parser.RawIdentifierOrdinaryOutcomeSoundnessProperties

/-! Exact diagnostic reports for current-input and identifier rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable current span and token realize the independent observation. -/
theorem currentInputAt_currentSpan_peekKind (input : State) :
    DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder input.currentSpan input.peekKind? := by
  cases found : input.peek? with
  | some token =>
      have observed := DeclarativeGrammar.CurrentInputAt.token
        (source := input.file.id) (endByte := input.window.endByte)
        (input := input.declarativeRemainder)
        (tokenAt_of_peek?_eq_some found)
      simpa only [State.currentSpan, State.peekKind?, found, Option.map_some]
        using observed
  | none =>
      by_cases inside : input.cursor < input.window.endIndex
      · have missing : input.tokens[input.cursor]? = none := by
          simpa only [State.peek?, inside, if_true] using found
        have observed := DeclarativeGrammar.CurrentInputAt.missingToken
          (source := input.file.id) (endByte := input.window.endByte)
          (input := input.declarativeRemainder) inside missing
        simpa only [State.currentSpan, State.peekKind?, found, Option.map_none,
          Lexer.sourceSpan] using observed
      · have observed := DeclarativeGrammar.CurrentInputAt.windowEnd
          (source := input.file.id) (endByte := input.window.endByte)
          (input := input.declarativeRemainder) (Nat.le_of_not_gt inside)
        simpa only [State.currentSpan, State.peekKind?, found, Option.map_none,
          Lexer.sourceSpan] using observed

/-- Independent observation fixes both executable fields, including EOF. -/
theorem currentInputAt_iff_currentSpan_peekKind
    {input : State} {span : SourceSpan} {found : Option TokenKind} :
    DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found ↔
      input.currentSpan = span ∧ input.peekKind? = found := by
  constructor
  · intro observed
    rcases observed.result_unique (currentInputAt_currentSpan_peekKind input) with
      ⟨spanEq, foundEq⟩
    exact ⟨spanEq.symm, foundEq.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact currentInputAt_currentSpan_peekKind input

/-- Converting an uncommitted failure retains every payload field exactly. -/
theorem Failure.toDiagnostic_injective : Function.Injective Failure.toDiagnostic := by
  intro left right equal
  cases left
  cases right
  simp only [Failure.toDiagnostic, ParseDiagnostic.mk.injEq,
    ParseDiagnosticKind.unexpected.injEq] at equal
  rcases equal with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- Independent reports exactly identify the failure created by rejection.
No event is committed by this primitive, and its input state is retained. -/
theorem rejectAt_reports_iff {alpha : Type}
    {input : State} {expected : NonemptyList ParseExpectation}
    {context : ParseContext} {diagnostic : ParseDiagnostic} :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      expected context input.declarativeRemainder diagnostic ↔
      ∃ failure, rejectAt (α := alpha) input expected context =
        .reject failure input ∧ failure.toDiagnostic = diagnostic := by
  constructor
  · intro reported
    cases reported with
    | reported observed =>
        rcases currentInputAt_iff_currentSpan_peekKind.mp observed with
          ⟨spanEq, foundEq⟩
        refine ⟨_, rfl, ?_⟩
        simp only [Failure.toDiagnostic, spanEq, foundEq]
  · rintro ⟨failure, result, diagnosticEq⟩
    unfold rejectAt at result
    cases result
    subst diagnostic
    exact .reported (currentInputAt_currentSpan_peekKind input)

/-- Every primitive rejection has its independent report and adds no event. -/
theorem rejectAt_reject_reports {alpha : Type}
    {input rejected : State} {failure : Failure}
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (result : rejectAt (α := alpha) input expected context =
      .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        expected context input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  unfold rejectAt at result
  cases result
  exact ⟨.reported (currentInputAt_currentSpan_peekKind input), rfl⟩

/-- An unavailable identifier selects the exact uncommitted rejection. -/
theorem rawIdentifier_eq_rejectAt_of_identifierAbsent (context : ParseContext)
    {input : State}
    (absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder) :
    rawIdentifier context input =
      rejectAt input { head := .identifier, tail := [] } context := by
  unfold rawIdentifier
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case identifier text =>
        exact False.elim (absent ⟨span, text, tokenAt_of_peek?_eq_some found⟩)

/-- Checked names preserve the raw failure and cannot add a hyphen diagnostic. -/
theorem identifier_eq_rejectAt_of_identifierAbsent (context : ParseContext)
    {input : State}
    (absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder) :
    identifier context input =
      rejectAt input { head := .identifier, tail := [] } context := by
  unfold identifier
  rw [rawIdentifier_eq_rejectAt_of_identifierAbsent context absent]
  rfl

/-- The raw-name rejection report is complete in either direction. -/
theorem rawIdentifier_reject_reports_iff (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, rawIdentifier context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure,
      (rawIdentifier_eq_rejectAt_of_identifierAbsent context absent).trans result,
      reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
      cases rawIdentifier_reject_ordinaryOutcome_sound context result with
      | absent missing => exact missing
    refine ⟨absent, (rejectAt_reports_iff (alpha := Identifier)).mpr ?_⟩
    exact ⟨failure,
      (rawIdentifier_eq_rejectAt_of_identifierAbsent context absent).symm.trans result,
      reportEq⟩

/-- Checked-name rejection has the same exact report as raw-name rejection. -/
theorem identifier_reject_reports_iff (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, identifier context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure,
      (identifier_eq_rejectAt_of_identifierAbsent context absent).trans result,
      reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent := identifier_reject_identifierAbsentAt context result
    refine ⟨absent, (rejectAt_reports_iff (alpha := Identifier)).mpr ?_⟩
    exact ⟨failure,
      (identifier_eq_rejectAt_of_identifierAbsent context absent).symm.trans result,
      reportEq⟩

/-- Raw-name rejection preserves the complete existing diagnostic sequence. -/
theorem rawIdentifier_reject_diagnostics_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics := by
  have absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
    have rejection := rawIdentifier_reject_ordinaryOutcome_sound context result
    generalize endpointEq : rejected.declarativeRemainder = endpoint at rejection
    cases rejection with
    | absent missing => exact missing
  rw [rawIdentifier_eq_rejectAt_of_identifierAbsent context absent] at result
  exact (rejectAt_reject_reports _ context result).2

/-- Checked-name rejection also preserves all earlier diagnostics. -/
theorem identifier_reject_diagnostics_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics := by
  rw [identifier_reject_state_eq context result]

end Solcore.Syntax.Parser
