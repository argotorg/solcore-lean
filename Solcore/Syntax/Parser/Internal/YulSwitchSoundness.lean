import Solcore.Syntax.Parser.Internal.YulBlockSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.YulStatementSoundness
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Parser.Internal.Basics

/-!
Soundness of the parsers of Yul `switch` cases: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchDiagnosticReflectionProperties
/-! Diagnostic reflection for inline-Yul switch parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulControl

/-- One case arm reflects through its literal and recursive block. -/
theorem caseArm_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (caseArm statement) := by
  unfold caseArm
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- The maximal case loop reflects through every committed case arm. -/
theorem caseList_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    ∀ fuel casesRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next result diagnosticFree
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next result diagnosticFree
      unfold caseList at result
      split at result
      · cases armResult : caseArm statement input with
        | invariant error => simp [armResult] at result
        | reject failure rejected => simp [armResult] at result
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · have afterArmFree := inductionHypothesis (arm :: casesRev)
                afterArm cases next result diagnosticFree
              exact caseArm_reflectsDiagnosticFreeOnSuccess statement
                statementReflects input arm afterArm armResult afterArmFree
            · contradiction
      · cases result
        exact diagnosticFree

/-- Optional default parsing reflects through its preferred keyword branch. -/
theorem optionalDefault_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (optionalDefault statement) := by
  unfold optionalDefault
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end YulControl

/-- Complete switch parsing reflects diagnostic freedom.  The no-case branch
has no diagnostic-free success because it always emits the switch constraint. -/
theorem yulSwitchStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulSwitchStatement statement) := by
  unfold yulSwitchStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .switchKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro scrutinee
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
  · intro input cases next result diagnosticFree
    exact YulControl.caseList_reflectsDiagnosticFreeOnSuccess statement
      statementReflects (input.remainingCount + 1) [] input cases next result
        diagnosticFree
  intro cases
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (YulControl.optionalDefault_reflectsDiagnosticFreeOnSuccess statement
      statementReflects)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | nil =>
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
      intro emitted
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulCaseSoundnessProperties
/-!
Exact diagnostic-free soundness for Yul switch arms, the reverse-accumulating
case loop, and the prioritized optional default.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

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

/-- One diagnostic-free case arm has its exact marker, literal, block, span,
AST, and remainder. -/
theorem caseArm_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {arm : YulCase}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : caseArm statement input = .ok arm next) :
    DeclarativeGrammar.YulCaseArmParses statementParses
      input.declarativeRemainder arm next.declarativeRemainder := by
  unfold caseArm at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, literalStage⟩
  rcases bind_ok_components literalStage with
    ⟨literal, afterLiteral, literalResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .caseKw .yulStatement markerResult)
    (yulLiteral_success_sound literalResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

/-- The executable reverse accumulator is the prefix of the returned cases;
the declarative relation is the remaining forward, maximal suffix. -/
theorem caseList_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder) :
    ∀ fuel casesRev input cases next,
      next.diagnosticsRev = [] →
      caseList statement fuel casesRev input = .ok cases next →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.YulCaseListParses statementParses
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next diagnosticFree result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next diagnosticFree result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (keywordAbsentAt_of_isKeyword_eq_false .caseKw casePresent),
            diagnosticFree⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    next diagnosticFree result with
                  ⟨suffix, casesEq, tailGrammar, afterArmFree⟩
                have armGrammar := caseArm_success_sound statement
                  statementParses statementReflects statementSound
                    afterArmFree armResult
                have inputFree := caseArm_reflectsDiagnosticFreeOnSuccess
                  statement statementReflects input arm afterArm armResult
                    afterArmFree
                refine ⟨arm :: suffix, ?_,
                  .next armGrammar (by
                    simpa [State.declarativeRemainder] using progress)
                    tailGrammar,
                  inputFree⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- Optional default success retains exact keyword priority and its block. -/
theorem optionalDefault_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {defaultBody : Option YulParsedBlock}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalDefault statement input = .ok defaultBody next) :
    DeclarativeGrammar.OptionalYulDefaultParses statementParses
      input.declarativeRemainder (defaultBody.map (fun body => body.span))
        (defaultBody.map (fun body => body.body))
          next.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨marker, afterMarker, markerResult, bodyStage⟩
    rcases bind_ok_components bodyStage with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact .present marker.span body.span
      (keyword_success_exactTokenParses .defaultKw .yulStatement markerResult)
      (yulBlock_success_sound statement statementParses statementReflects
        statementSound diagnosticFree bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

end Solcore.Syntax.Parser.YulControl
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreDiagnosticReflectionProperties
/-! Diagnostic reflection for public Yul statement parsing layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The complete ordered non-terminating Yul dispatcher reflects diagnostics. -/
theorem yulStatementCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementCore nested) := by
  intro input value next result diagnosticFree
  unfold yulStatementCore at result
  split at result
  · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
      (yulBlockStatement nested) yulExpressionStatement
        (yulBlockStatement_reflectsDiagnosticFreeOnSuccess nested
          nestedReflects) input value next result diagnosticFree
  · split at result
    · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
        yulLetStatement yulExpressionStatement
          yulLetStatement_reflectsDiagnosticFreeOnSuccess input value next
            result diagnosticFree
    · split at result
      · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
          (yulIfStatement nested) yulExpressionStatement
            (yulIfStatement_reflectsDiagnosticFreeOnSuccess nested
              nestedReflects) input value next result diagnosticFree
      · split at result
        · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
            (yulForStatement nested) yulExpressionStatement
              (yulForStatement_reflectsDiagnosticFreeOnSuccess nested
                nestedReflects) input value next result diagnosticFree
        · split at result
          · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
              (yulSwitchStatement nested) yulExpressionStatement
                (yulSwitchStatement_reflectsDiagnosticFreeOnSuccess nested
                  nestedReflects) input value next result diagnosticFree
          · split at result
            · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                (yulFunctionStatement nested) yulExpressionStatement
                  (yulFunctionStatement_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects) input value next result diagnosticFree
            · split at result
              · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                  yulReturnBuiltin yulExpressionStatement
                    yulReturnBuiltin_reflectsDiagnosticFreeOnSuccess input
                      value next result diagnosticFree
              · split at result
                · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                    (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (yulControlToken_reflectsDiagnosticFreeOnSuccess .leaveKw
                        .leave) input value next result diagnosticFree
                · split at result
                  · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                      (yulControlToken .breakKw .break) yulExpressionStatement
                        (yulControlToken_reflectsDiagnosticFreeOnSuccess
                          .breakKw .break) input value next result diagnosticFree
                  · split at result
                    · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                        (yulControlToken .continueKw .continue)
                          yulExpressionStatement
                          (yulControlToken_reflectsDiagnosticFreeOnSuccess
                            .continueKw .continue) input value next result
                              diagnosticFree
                    · split at result
                      · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
                          yulAssignment_reflectsDiagnosticFreeOnSuccess
                          yulExpressionStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree
                      · exact
                          yulExpressionStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree

/-- The concrete optional-semicolon layer reflects through its exact core. -/
theorem yulStatementTerminated_reflectsDiagnosticFreeOnSuccess_of_core
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  exact yulStatementTerminated_reflectsDiagnosticFreeOnSuccess
    (yulStatementCore nested)
      (yulStatementCore_reflectsDiagnosticFreeOnSuccess nested nestedReflects)

/-- Clean recovery-layer success reflects through the terminated parser. -/
theorem yulStatementLayer_reflectsDiagnosticFreeOnSuccess_of_core
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementLayer nested) :=
  yulStatementLayer_reflectsDiagnosticFreeOnSuccess nested
    (yulStatementTerminated_reflectsDiagnosticFreeOnSuccess_of_core nested
      nestedReflects)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementRecursiveDiagnosticReflectionProperties
/-! Diagnostic reflection for recursive and public inline-Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every explicit recursive fuel layer reflects diagnostic freedom through
its preceding nested layer. -/
theorem yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel,
      Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input value output result diagnosticFree
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      simpa only [yulStatementWithFuel] using
        yulStatementLayer_reflectsDiagnosticFreeOnSuccess_of_core
          (yulStatementWithFuel fuel) inductionHypothesis

/-- The public remaining-token fuel selection also reflects diagnostic
freedom. -/
theorem yulStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulStatement := by
  intro input value output result diagnosticFree
  unfold yulStatement at result
  exact yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value output result diagnosticFree

end Solcore.Syntax.Parser
end
