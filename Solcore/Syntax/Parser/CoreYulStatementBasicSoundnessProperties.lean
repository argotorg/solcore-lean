import Solcore.Syntax.DeclarativeCoreYulStatementBasicGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Diagnostic reflection and exact soundness for keyword-only Yul statements and
optional semicolon termination.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

theorem yulControlToken_reflectsDiagnosticFreeOnSuccess
    (keywordValue : HardKeyword) (statementValue : YulStmtValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulControlToken keywordValue statementValue) := by
  unfold yulControlToken
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess keywordValue .yulStatement)
  intro marker
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess
    (value : YulStmt) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .yulStatement)
    intro semicolon
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulStatementTerminated_reflectsDiagnosticFreeOnSuccess
    (core : Parser YulStmt)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess core) :
    Parser.ReflectsDiagnosticFreeOnSuccess (do
      optionalYulSemicolon (← core)) := by
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess coreReflects
  intro value
  exact optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess value

theorem yulControlToken_success_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input next : State} {value : YulStmt}
    (result : yulControlToken keywordValue statementValue input =
      .ok value next) :
    DeclarativeGrammar.YulControlTokenParses keywordValue statementValue
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulControlToken at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses keywordValue .yulStatement markerResult)

theorem optionalYulSemicolon_success_sound (value : YulStmt)
    {input next : State}
    (result : optionalYulSemicolon value input = .ok value next) :
    DeclarativeGrammar.OptionalYulSemicolonParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at result
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult, pure] at result
        cases result
        exact .present semicolon.span
          (symbol_success_exactTokenParses .semicolon .yulStatement
            semicolonResult)
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)

theorem yulStatementTerminated_success_sound
    (core : Parser YulStmt)
    (coreParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (coreSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → core input = .ok value next →
      coreParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : (do optionalYulSemicolon (← core)) input = .ok value next) :
    DeclarativeGrammar.YulStatementTerminatedParses coreParses
      input.declarativeRemainder value next.declarativeRemainder := by
  rcases bind_ok_components result with
    ⟨coreValue, afterCore, coreResult, semicolonResult⟩
  have afterCoreFree := optionalYulSemicolon_reflectsDiagnosticFreeOnSuccess
    coreValue afterCore value next semicolonResult diagnosticFree
  have valueEq : coreValue = value := by
    unfold optionalYulSemicolon getState at semicolonResult
    simp only [bind] at semicolonResult
    split at semicolonResult
    · cases symbolResult : symbol .semicolon .yulStatement afterCore with
      | invariant error => simp [symbolResult] at semicolonResult
      | reject failure rejected => simp [symbolResult] at semicolonResult
      | ok semicolon afterSemicolon =>
          simp only [symbolResult, pure] at semicolonResult
          cases semicolonResult
          rfl
    · simp only [pure] at semicolonResult
      cases semicolonResult
      rfl
  subst coreValue
  exact ⟨afterCore.declarativeRemainder,
    coreSound afterCoreFree coreResult,
    optionalYulSemicolon_success_sound value semicolonResult⟩

end Solcore.Syntax.Parser
