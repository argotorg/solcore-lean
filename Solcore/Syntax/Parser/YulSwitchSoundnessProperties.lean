import Solcore.Syntax.Parser.YulCaseSoundnessProperties

/-! Exact diagnostic-free soundness for complete inline-Yul switches. -/

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

/-- Every diagnostic-free switch success has at least one case and follows
the exact maximal case/default grammar.  The executable empty-case `.error`
success is excluded by its mandatory constraint diagnostic. -/
theorem yulSwitchStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulSwitchStatement statement input = .ok value next) :
    DeclarativeGrammar.YulSwitchStatementParses statementParses
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold yulSwitchStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, scrutineeStage⟩
  rcases bind_ok_components scrutineeStage with
    ⟨scrutinee, afterScrutinee, scrutineeResult, casesStage⟩
  rcases bind_ok_components casesStage with
    ⟨cases, afterCases, casesResult, defaultStage⟩
  rcases bind_ok_components defaultStage with
    ⟨defaultBody, afterDefault, defaultResult, finished⟩
  cases cases with
  | nil =>
      rcases bind_ok_components finished with
        ⟨emitted, afterEmit, emittedResult, completed⟩
      cases completed
      unfold emitDiagnostic modifyState at emittedResult
      cases emittedResult
      simp [State.emit] at diagnosticFree
  | cons head tail =>
      cases finished
      have afterCasesFree :=
        YulControl.optionalDefault_reflectsDiagnosticFreeOnSuccess statement
          statementReflects afterCases defaultBody next defaultResult
            diagnosticFree
      rcases YulControl.caseList_success_sound statement statementParses
          statementReflects statementSound
          (afterScrutinee.remainingCount + 1) [] afterScrutinee
          (head :: tail) afterCases afterCasesFree casesResult with
        ⟨suffix, casesEq, casesGrammar, afterScrutineeFree⟩
      have suffixEq : suffix = head :: tail := by simpa using casesEq.symm
      subst suffix
      have scrutineeGrammar := expressionSound afterScrutineeFree
        scrutineeResult
      cases defaultBody with
      | none =>
          have defaultGrammar :=
            YulControl.optionalDefault_success_sound statement
              statementParses statementReflects statementSound diagnosticFree
                defaultResult
          exact
            DeclarativeGrammar.YulSwitchStatementParses.parsed marker.span
              (keyword_success_exactTokenParses .switchKw .yulStatement
                markerResult)
              scrutineeGrammar casesGrammar defaultGrammar
      | some body =>
          have defaultGrammar :=
            YulControl.optionalDefault_success_sound statement
              statementParses statementReflects statementSound diagnosticFree
                defaultResult
          exact
            DeclarativeGrammar.YulSwitchStatementParses.parsed marker.span
              (keyword_success_exactTokenParses .switchKw .yulStatement
                markerResult)
              scrutineeGrammar casesGrammar defaultGrammar

end Solcore.Syntax.Parser
