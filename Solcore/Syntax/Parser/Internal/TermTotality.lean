import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DelimitedTotality

/-!
Totality of the parsers of patterns and statements through the term recursion: on valid
input they make progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TermPatternFuelTotalityProperties
/-! Fuel-inductive totality for the recursive canonical pattern family. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

theorem corePatternWithFuel_fuelElementTotalityContract
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract (coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    ∀ fuel,
      FuelElementTotalityContract (corePatternWithFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        validFor := by
          intro input inputValid
          simp only [corePatternWithFuel]
          trivial
        preservesTokenWindow := by
          intro input
          trivial
        cursorLtOnSuccess := by
          intro input next value result
          simp [corePatternWithFuel] at result
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      have expressionValidFamily : ∀ level,
          (coreExpressionWithFuel level).ValidFor
            (Expr.ValidFor statementValid) :=
        fun level => (expressionSyntax level).validFor
      have expressionStartsFamily : ∀ level,
          Parser.StartsAtCurrentTokenOnSuccess
            (coreExpressionWithFuel level) (·.span) :=
        fun level => (expressionSyntax level).startsAtCurrentTokenOnSuccess
      have expressionWindowFamily : ∀ level,
          Parser.PreservesTokenWindow (coreExpressionWithFuel level) :=
        fun level => (expressionSyntax level).preservesTokenWindow
      have nestedValid := corePatternWithFuel_validFor
        (Expr.ValidFor statementValid) expressionValidFamily
        expressionSpanValid expressionStartsFamily expressionWindowFamily fuel
      have layer := PatternInternals.patternLayer_fuelElementTotalityContract
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        fuel fuel inductionHypothesis (expressionTotality fuel)
        (Expr.ValidFor statementValid) nestedValid
        (expressionSyntax fuel).validFor expressionSpanValid
        (expressionSyntax fuel).startsAtCurrentTokenOnSuccess
      simpa only [corePatternWithFuel, Nat.min_self] using layer

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPatternTotalityProperties
/-! Public totality for the canonical pattern parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem pattern_invariantFreeOnValid_of_coreExpressionTotality
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    Parser.InvariantFreeOnValid pattern := by
  intro input inputValid
  have patternTotality :=
    TermInternals.corePatternWithFuel_fuelElementTotalityContract
      statementValid expressionSyntax expressionTotality expressionSpanValid
        (input.remainingCount + 1)
  unfold pattern
  exact patternTotality.ordinary input inputValid (by omega)

theorem pattern_ne_invariant_of_coreExpressionTotality
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    pattern input ≠ .invariant error :=
  (pattern_invariantFreeOnValid_of_coreExpressionTotality statementValid
    expressionSyntax expressionTotality expressionSpanValid).ne_invariant
      input inputValid error

theorem pattern_elementTotalityContract_of_coreExpression
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    ElementTotalityContract pattern := by
  have expressionValid : ∀ fuel,
      (TermInternals.coreExpressionWithFuel fuel).ValidFor
        (Expr.ValidFor statementValid) :=
    fun fuel => (expressionSyntax fuel).validFor
  have expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (TermInternals.coreExpressionWithFuel fuel) (·.span) :=
    fun fuel => (expressionSyntax fuel).startsAtCurrentTokenOnSuccess
  have expressionWindow : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel) :=
    fun fuel => (expressionSyntax fuel).preservesTokenWindow
  exact {
    validFor := (pattern_validFor_of_coreExpression
      (Expr.ValidFor statementValid) expressionValid expressionSpanValid
        expressionStarts expressionWindow).mono (fun _ _ _ => trivial)
    preservesTokenWindow :=
      pattern_preservesTokenWindow_of_coreExpression expressionWindow
    cursorLtOnSuccess := by
      intro input next value parsed
      unfold pattern at parsed
      exact (TermInternals.corePatternWithFuel_fuelElementTotalityContract
        statementValid expressionSyntax expressionTotality expressionSpanValid
          (input.remainingCount + 1)).cursorLtOnSuccess parsed
    invariantFree :=
      (pattern_invariantFreeOnValid_of_coreExpressionTotality statementValid
        expressionSyntax expressionTotality expressionSpanValid).ne_invariant
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermStatementTotalityProperties
/-! Valid-input totality for the recognized-statement fallback boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/--
Recognized-statement fallback is ordinary when both parsers are ordinary on
valid input. After a primary rejection, the fallback is rerun at the original
input; a successful fallback keeps its value and cursor while replacing its
diagnostics with the primary failure diagnostic.
-/
theorem recognizedStatementOrFallback_invariantFreeOnValid
    (primary fallback : Parser Statement)
    (primaryFree : Parser.InvariantFreeOnValid primary)
    (fallbackFree : Parser.InvariantFreeOnValid fallback) :
    Parser.InvariantFreeOnValid
      (recognizedStatementOrFallback primary fallback) := by
  intro input inputValid
  rcases primaryFree input inputValid with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedStatementOrFallback, primaryResult]⟩
  · rcases fallbackFree input inputValid with
      ⟨value, next, fallbackResult⟩ |
      ⟨fallbackFailure, fallbackRejected, fallbackResult⟩
    · let reset : State := {
        next with diagnosticsRev := input.diagnosticsRev
      }
      exact Or.inl ⟨value, reset.emit failure.toDiagnostic, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult, reset]⟩
    · exact Or.inr ⟨failure, input, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult]⟩

/-- No invariant reply can escape the recognized fallback boundary. -/
theorem recognizedStatementOrFallback_ne_invariant
    (primary fallback : Parser Statement)
    (primaryFree : Parser.InvariantFreeOnValid primary)
    (fallbackFree : Parser.InvariantFreeOnValid fallback)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    recognizedStatementOrFallback primary fallback input ≠
      .invariant error :=
  (recognizedStatementOrFallback_invariantFreeOnValid primary fallback
    primaryFree fallbackFree).ne_invariant input inputValid error

/-- Statement provenance/state contracts paired with valid-input totality. -/
structure StatementTotalityContract
    (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) : Prop
    extends StatementParserContract valueValid parser where
  invariantFree : Parser.InvariantFreeOnValid parser

namespace StatementTotalityContract

/-- A totality contract excludes every invariant reply on valid input. -/
theorem ne_invariant
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement}
    (contract : StatementTotalityContract valueValid parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  contract.invariantFree.ne_invariant input inputValid error

end StatementTotalityContract

/-- Both complete branch contracts compose through recognized fallback. -/
theorem recognizedStatementOrFallback_totalityContract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryContract : StatementTotalityContract valueValid primary)
    (fallbackContract : StatementTotalityContract valueValid fallback) :
    StatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback) := {
  toStatementParserContract :=
    recognizedStatementOrFallback_contract primary fallback
      primaryContract.toStatementParserContract
      fallbackContract.toStatementParserContract
  invariantFree := recognizedStatementOrFallback_invariantFreeOnValid
    primary fallback primaryContract.invariantFree
      fallbackContract.invariantFree
}

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermStatementFallbackTotalityProperties
/-! Valid-input totality for the terminal Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- The custom value-assignment operator parser has no invariant branch. -/
theorem valueAssignOperator_invariantFreeOnValid :
    Parser.InvariantFreeOnValid valueAssignOperator := by
  intro input _inputValid
  cases result : valueAssignOperator input with
  | ok operator next => exact Or.inl ⟨operator, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold valueAssignOperator at result
      cases decoded : valueAssignAt? input with
      | none => simp [decoded, rejectAt] at result
      | some operator => simp [decoded] at result

/-- Assignment suffixes inherit valid-input totality from expressions. -/
theorem assignmentTail_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (assignmentTail expression) := by
  intro input inputValid
  unfold assignmentTail
  split
  · exact (Parser.bind_invariantFreeOnValid
      (symbol_validFor .tildeEqual .statement)
      (symbol_ordinary .tildeEqual .statement).invariantFreeOnValid
      (fun operator => Parser.pure_invariantFreeOnValid
        (AssignmentTail.bitNot operator.span))) input inputValid
  · cases selected : valueAssignAt? input with
    | none =>
        exact (Parser.rejectAt_invariantFreeOnValid
          (alpha := AssignmentTail)
          { head := .expression, tail := [] } .statement) input inputValid
    | some selectedOperator =>
        exact (Parser.bind_invariantFreeOnValid
          valueAssignOperator_validFor
          valueAssignOperator_invariantFreeOnValid
          (fun operator => Parser.bind_invariantFreeOnValid
            expressionValid expressionFree
            (fun right => Parser.pure_invariantFreeOnValid
              (AssignmentTail.value operator right)))) input inputValid

/-- Optional assignment suffix selection adds no invariant result. -/
theorem optionalAssignmentTail_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalAssignmentTail expression) := by
  intro input inputValid
  unfold optionalAssignmentTail
  split
  · exact (Parser.bind_invariantFreeOnValid
      (assignmentTail_validFor expression (fun _ _ => True)
        expressionValid)
      (assignmentTail_invariantFreeOnValid expression expressionValid
        expressionFree)
      (fun tail => Parser.pure_invariantFreeOnValid (some tail)))
        input inputValid
  · exact (Parser.pure_invariantFreeOnValid none) input inputValid

/-- Optional semicolon parsing is ordinary on every valid input. -/
theorem optionalSemicolon_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalSemicolon := by
  unfold optionalSemicolon
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .semicolon
  · simp only [present, if_true]
    exact Parser.bind_invariantFreeOnValid
      (symbol_validFor .semicolon .statement)
      (symbol_ordinary .semicolon .statement).invariantFreeOnValid
      (fun marker => Parser.pure_invariantFreeOnValid (some marker.span))
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

/-- The final diagnostic/pure branch is total for every parsed prefix. -/
private theorem finishAssignmentOrExpression_invariantFreeOnValid
    (left : Expr) (tail : Option AssignmentTail)
    (semicolon : Option SourceSpan) :
    Parser.InvariantFreeOnValid (do
      let endSpan := statementEnd left tail semicolon
      let span := SourceSpan.cover left.span endSpan
      match tail with
      | some (.value operator right) =>
          if semicolon.isNone then
            let _ ← emitDiagnostic {
              span
              kind := .constraintViolation .assignmentRequiresSemicolon
            }
          pure ({
            span
            value := StatementValue.assignValue left operator right
          } : Statement)
      | some (.bitNot operator) =>
          if semicolon.isNone then
            let _ ← emitDiagnostic {
              span
              kind := .constraintViolation .assignmentRequiresSemicolon
            }
          pure ({
            span
            value := StatementValue.assignBitNot left operator
          } : Statement)
      | none => pure ({
          span
          value := StatementValue.expression left semicolon.isSome
        } : Statement)) := by
  intro input _inputValid
  dsimp only
  cases tail with
  | none => exact Or.inl ⟨_, input, rfl⟩
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            exact Or.inl ⟨_, input.emit _, rfl⟩
          · simp only [missing]
            exact Or.inl ⟨_, input, rfl⟩
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            exact Or.inl ⟨_, input.emit _, rfl⟩
          · simp only [missing]
            exact Or.inl ⟨_, input, rfl⟩

end StatementSimpleInternals

/--
The assignment/expression fallback is ordinary whenever expressions preserve
valid states and are ordinary on valid input.
-/
theorem assignmentOrExpressionStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid
      (assignmentOrExpressionStatement expression) := by
  unfold assignmentOrExpressionStatement
  apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
  intro left
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalAssignmentTail_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalAssignmentTail_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro tail
  apply Parser.bind_invariantFreeOnValid
    StatementSimpleInternals.optionalSemicolon_validFor
    StatementSimpleInternals.optionalSemicolon_invariantFreeOnValid
  intro semicolon
  exact StatementSimpleInternals.finishAssignmentOrExpression_invariantFreeOnValid
    left tail semicolon

/-- The fallback excludes every invariant result under the same premises. -/
theorem assignmentOrExpressionStatement_ne_invariant
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error :=
  (assignmentOrExpressionStatement_invariantFreeOnValid expression
    expressionValid expressionFree).ne_invariant input inputValid error

/-- A generic element-totality contract discharges both expression premises. -/
theorem assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
    (expression : Parser Expr)
    (expressionTotality : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid
      (assignmentOrExpressionStatement expression) :=
  assignmentOrExpressionStatement_invariantFreeOnValid expression
    expressionTotality.validFor
    (Parser.invariantFreeOnValid_of_ne_invariant
      expressionTotality.invariantFree)

/-- Element totality directly excludes fallback invariants on valid input. -/
theorem assignmentOrExpressionStatement_ne_invariant_of_elementTotality
    (expression : Parser Expr)
    (expressionTotality : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error :=
  (assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
    expression expressionTotality).ne_invariant input inputValid error

/-- Package the fallback's syntax/state laws together with its totality. -/
theorem assignmentOrExpressionStatement_totalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expression : Parser Expr)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality : ElementTotalityContract expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid yulValueValid)
      (assignmentOrExpressionStatement expression) := {
  toStatementParserContract := {
    validFor := assignmentOrExpressionStatement_validFor expression
      (Expr.ValidFor statementValid) patternValueValid yulValueValid
      expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
      expressionSyntax.preservesTokenWindow
      expressionSyntax.cursorLtOnSuccess
      expressionSyntax.startsAtCurrentTokenOnSuccess
    preservesTokenWindow :=
      assignmentOrExpressionStatement_preservesTokenWindow expression
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess :=
      assignmentOrExpressionStatement_cursorMonotoneOnSuccess expression
        expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess expression
        expressionSyntax.startsAtCurrentTokenOnSuccess
  }
  invariantFree :=
    assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
      expression expressionTotality
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermStatementFallbackFuelTotalityProperties
/-! Recursive-fuel totality for the terminal Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- Assignment suffixes remain ordinary below the expression fuel bound. -/
theorem assignmentTail_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ tail next, assignmentTail expression input = .ok tail next) ∨
    (∃ failure next,
      assignmentTail expression input = .reject failure next) := by
  unfold assignmentTail
  split
  · rcases (symbol_ordinary .tildeEqual .statement) input with
      ⟨operator, next, operatorResult⟩ |
      ⟨failure, rejected, operatorResult⟩
    · exact Or.inl ⟨AssignmentTail.bitNot operator.span, next, by
        simp only [bind, operatorResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, operatorResult]⟩
  · cases selected : valueAssignAt? input with
    | none =>
        exact (Parser.rejectAt_invariantFreeOnValid
          (alpha := AssignmentTail)
          { head := .expression, tail := [] } .statement) input inputValid
    | some selectedOperator =>
        rcases valueAssignOperator_invariantFreeOnValid input inputValid with
          ⟨operator, afterOperator, operatorResult⟩ |
          ⟨failure, rejected, operatorResult⟩
        · have operatorReply := valueAssignOperator_validFor input inputValid
          rw [operatorResult] at operatorReply
          have operatorWindow := valueAssignOperator_preservesTokenWindow input
          rw [operatorResult] at operatorWindow
          have expressionAdequate :
              afterOperator.remainingCount < expressionFuel :=
            remainingCount_lt_of_cursor_le operatorWindow.2
              (valueAssignOperator_cursorMonotoneOnSuccess input operator
                afterOperator operatorResult) adequate
          rcases contract.ordinary afterOperator operatorReply.2.1
              expressionAdequate with
            ⟨right, final, rightResult⟩ |
            ⟨failure, rejected, rightResult⟩
          · exact Or.inl ⟨AssignmentTail.value operator right, final, by
              simp only [bind, operatorResult, rightResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [bind, operatorResult, rightResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [bind, operatorResult]⟩

/-- Optional suffix selection preserves the same expression-fuel bound. -/
theorem optionalAssignmentTail_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ tail next,
      optionalAssignmentTail expression input = .ok tail next) ∨
    (∃ failure next,
      optionalAssignmentTail expression input = .reject failure next) := by
  unfold optionalAssignmentTail
  split
  · rcases assignmentTail_ordinary_of_expressionFuel expression
        expressionFuel contract input inputValid adequate with
      ⟨tail, next, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨some tail, next, by
        simp only [bind, tailResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, tailResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

end StatementSimpleInternals

/--
The fallback stays ordinary below the expression fuel bound. A successful
left expression preserves the bound for a possible assignment right-hand
expression through its token-window and cursor contracts.
-/
theorem assignmentOrExpressionStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ statement next,
      assignmentOrExpressionStatement expression input = .ok statement next) ∨
    (∃ failure next,
      assignmentOrExpressionStatement expression input =
        .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, afterLeft, leftResult⟩ |
    ⟨failure, rejected, leftResult⟩
  · have leftReply := contract.validFor input inputValid
    rw [leftResult] at leftReply
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have tailAdequate : afterLeft.remainingCount < expressionFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    rcases StatementSimpleInternals.optionalAssignmentTail_ordinary_of_expressionFuel
        expression expressionFuel contract afterLeft leftReply.2.1
          tailAdequate with
      ⟨tail, afterTail, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · have tailReply :=
        StatementSimpleInternals.optionalAssignmentTail_validFor expression
          (fun _ _ => True) contract.validFor afterLeft leftReply.2.1
      rw [tailResult] at tailReply
      rcases StatementSimpleInternals.optionalSemicolon_invariantFreeOnValid
          afterTail tailReply.2.1 with
        ⟨semicolon, afterSemicolon, semicolonResult⟩ |
        ⟨failure, rejected, semicolonResult⟩
      · let endSpan := StatementSimpleInternals.statementEnd left tail semicolon
        let span := SourceSpan.cover left.span endSpan
        cases tail with
        | none =>
            exact Or.inl ⟨{
              span
              value := .expression left semicolon.isSome
            }, afterSemicolon, by
              simp only [assignmentOrExpressionStatement, bind, leftResult,
                tailResult, semicolonResult, pure]
              rfl⟩
        | some tail =>
            cases tail with
            | value operator right =>
                let statement : Statement := {
                  span
                  value := .assignValue left operator right
                }
                by_cases missing : semicolon.isNone
                · exact Or.inl ⟨statement, afterSemicolon.emit {
                      span
                      kind := .constraintViolation
                        .assignmentRequiresSemicolon
                    }, by
                    simp only [assignmentOrExpressionStatement, leftResult,
                      tailResult, semicolonResult, missing, if_true,
                      emitDiagnostic, modifyState, bind, pure]
                    rfl⟩
                · exact Or.inl ⟨statement, afterSemicolon, by
                    simp only [assignmentOrExpressionStatement, bind,
                      leftResult, tailResult, semicolonResult, missing, pure]
                    rfl⟩
            | bitNot operator =>
                let statement : Statement := {
                  span
                  value := .assignBitNot left operator
                }
                by_cases missing : semicolon.isNone
                · exact Or.inl ⟨statement, afterSemicolon.emit {
                      span
                      kind := .constraintViolation
                        .assignmentRequiresSemicolon
                    }, by
                    simp only [assignmentOrExpressionStatement, leftResult,
                      tailResult, semicolonResult, missing, if_true,
                      emitDiagnostic, modifyState, bind, pure]
                    rfl⟩
                · exact Or.inl ⟨statement, afterSemicolon, by
                    simp only [assignmentOrExpressionStatement, bind,
                      leftResult, tailResult, semicolonResult, missing, pure]
                    rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [assignmentOrExpressionStatement, bind, leftResult,
            tailResult, semicolonResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [assignmentOrExpressionStatement, bind, leftResult,
          tailResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [assignmentOrExpressionStatement, bind, leftResult]⟩

/-- The fuel-bounded fallback cannot expose an invariant reply. -/
theorem assignmentOrExpressionStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error := by
  intro failed
  rcases assignmentOrExpressionStatement_ordinary_of_expressionFuel expression
      expressionFuel contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

namespace TermInternals

/-- Statement syntax/state laws paired with fuel-bounded ordinary control. -/
structure FuelStatementTotalityContract
    (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) (fuel : Nat) : Prop
    extends StatementParserContract valueValid parser where
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelStatementTotalityContract

/-- A statement contract at a larger fuel bound proves every smaller bound. -/
theorem weaken
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement} {smallFuel largeFuel : Nat}
    (contract : FuelStatementTotalityContract valueValid parser largeFuel)
    (bound : smallFuel ≤ largeFuel) :
    FuelStatementTotalityContract valueValid parser smallFuel := {
  toStatementParserContract := contract.toStatementParserContract
  ordinary := fun input inputValid adequate =>
    contract.ordinary input inputValid
      (Nat.lt_of_lt_of_le adequate bound)
}

/-- Adequate fuel excludes every statement-parser invariant. -/
theorem ne_invariant
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement} {fuel : Nat}
    (contract : FuelStatementTotalityContract valueValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelStatementTotalityContract
end TermInternals

/-- Package the recursive fallback with its fixed expression-fuel bound. -/
theorem assignmentOrExpressionStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid yulValueValid)
      (assignmentOrExpressionStatement expression) expressionFuel := {
  toStatementParserContract := {
    validFor := assignmentOrExpressionStatement_validFor expression
      (Expr.ValidFor statementValid) patternValueValid yulValueValid
      expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
      expressionSyntax.preservesTokenWindow
      expressionSyntax.cursorLtOnSuccess
      expressionSyntax.startsAtCurrentTokenOnSuccess
    preservesTokenWindow :=
      assignmentOrExpressionStatement_preservesTokenWindow expression
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess :=
      assignmentOrExpressionStatement_cursorMonotoneOnSuccess expression
        expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess expression
        expressionSyntax.startsAtCurrentTokenOnSuccess
  }
  ordinary := assignmentOrExpressionStatement_ordinary_of_expressionFuel
    expression expressionFuel expressionTotality
}

end Solcore.Syntax.Parser
end
