import Solcore.Syntax.DeclarativeIdentifierTraceProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Exact raw and checked identifier success, including complete diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_success_ordinary_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name remainder ↔
      ∃ output, rawIdentifier context input = .ok name output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (rawIdentifier context)
    DeclarativeGrammar.identifierExactOutcomeSpec
    (rawIdentifier_ne_invariant context input)
    (rawIdentifier_success_ordinaryOutcome_sound context)
    (rawIdentifier_reject_ordinaryOutcome_sound context)

private theorem identifier_success_ordinary_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name remainder ↔
      ∃ output, identifier context input = .ok name output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (identifier context)
    DeclarativeGrammar.identifierExactOutcomeSpec
    (identifier_ne_invariant context input)
    (identifier_success_sound context) (identifier_reject_sound context)

/-- Raw names consume their token without changing any earlier diagnostics. -/
theorem rawIdentifier_success_diagnostics_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    output.diagnostics = input.diagnostics := by
  rw [(rawIdentifier_ok_tokenAt context result).2]
  rfl

/-- Raw success has its exact AST, endpoint, and independent empty trace. -/
theorem rawIdentifier_success_trace_sound (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    DeclarativeGrammar.RawIdentifierTraceParses input.declarativeRemainder name
        output.declarativeRemainder [] ∧
      output.diagnostics = input.diagnostics :=
  ⟨.parsed (rawIdentifier_success_ordinaryOutcome_sound context result),
    rawIdentifier_success_diagnostics_eq context result⟩

/-- Checked success selects exactly its spelling-dependent added events. -/
theorem identifier_success_diagnosticTrace (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    ∃ trace, DeclarativeGrammar.IdentifierDiagnosticTrace name trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      have previous := rawIdentifier_success_diagnostics_eq context raw
      simp only [raw] at result
      by_cases hyphen : DeclarativeGrammar.IdentifierHyphenSpelling parsed.value
      · have contains :=
          (DeclarativeGrammar.identifierHyphenSpelling_iff_contains parsed.value).mp hyphen
        simp only [contains, if_true] at result
        cases result
        refine ⟨_, .hyphen hyphen, ?_⟩
        simpa only [State.diagnostics, State.emit, List.reverse_cons] using
          congrArg (fun diagnostics => diagnostics ++
            [{ span := name.span, kind := .invalidIdentifierHyphen name.value }]) previous
      · have absent : parsed.value.toList.contains '-' = false := by
          apply Bool.eq_false_iff.mpr
          intro contains
          exact hyphen
            ((DeclarativeGrammar.identifierHyphenSpelling_iff_contains parsed.value).mpr
              contains)
        simp only [absent, Bool.false_eq_true, if_false] at result
        cases result
        exact ⟨[], .clean hyphen, by simpa only [List.append_nil] using previous⟩

/-- The independently chosen spelling trace fixes the entire added suffix. -/
theorem identifier_success_diagnostics_eq_of_trace (context : ParseContext)
    {input output : State} {name : Identifier} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok name output)
    (diagnostics : DeclarativeGrammar.IdentifierDiagnosticTrace name trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_diagnosticTrace context result with
    ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Executable checked success derives the full independent traced grammar. -/
theorem identifier_success_trace_sound (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    ∃ trace, DeclarativeGrammar.IdentifierTraceParses input.declarativeRemainder name
        output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_diagnosticTrace context result with
    ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, .parsed (identifier_success_sound context result) diagnostics,
    diagnosticEq⟩

/-- Raw token and trace derivation is equivalent to exact executable success. -/
theorem rawIdentifier_trace_success_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.RawIdentifierTraceParses input.declarativeRemainder name
        remainder trace ↔
      ∃ output, rawIdentifier context input = .ok name output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  rw [DeclarativeGrammar.rawIdentifierTraceParses_iff]
  constructor
  · rintro ⟨ordinary, rfl⟩
    rcases (rawIdentifier_success_ordinary_iff context).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      by simpa only [List.append_nil] using rawIdentifier_success_diagnostics_eq context result⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(rawIdentifier_success_ordinary_iff context).mpr ⟨output, result, after⟩, ?_⟩
    have unchanged := rawIdentifier_success_diagnostics_eq context result
    have empty : input.diagnostics ++ trace = input.diagnostics ++ [] := by
      simpa only [List.append_nil] using diagnosticEq.symm.trans unchanged
    exact List.append_cancel_left empty

/-- Checked token, spelling, and trace derivation is equivalent to execution
with the same full AST and remainder, preserving all earlier diagnostics. -/
theorem identifier_trace_success_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierTraceParses input.declarativeRemainder name
        remainder trace ↔
      ∃ output, identifier context input = .ok name output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  rw [DeclarativeGrammar.identifierTraceParses_iff]
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases (identifier_success_ordinary_iff context).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      identifier_success_diagnostics_eq_of_trace context result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(identifier_success_ordinary_iff context).mpr ⟨output, result, after⟩, ?_⟩
    rcases identifier_success_diagnosticTrace context result with
      ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser
