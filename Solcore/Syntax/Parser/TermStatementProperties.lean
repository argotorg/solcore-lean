import Solcore.Syntax.Parser.Term
import Solcore.Syntax.Parser.Statement.ControlProperties
import Solcore.Syntax.Parser.Statement.MatchProperties

/-! Contracts for the canonical statement dispatch boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Recognized-statement fallback preserves either branch's provenance. -/
theorem recognizedStatementOrFallback_validFor
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryValid : primary.ValidFor valueValid)
    (fallbackValid : fallback.ValidFor valueValid) :
    (recognizedStatementOrFallback primary fallback).ValidFor valueValid := by
  intro input inputValid
  have primaryContract := primaryValid input inputValid
  unfold recognizedStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      rw [primaryResult] at primaryContract
      have fallbackContract := fallbackValid input inputValid
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.ValidFor]
          exact ⟨primaryContract.1, inputValid, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          let reset : State := {
            next with diagnosticsRev := input.diagnosticsRev
          }
          have resetValid : reset.ValidFor := {
            tokens := fallbackContract.2.1.tokens
            cursor_le_endIndex := fallbackContract.2.1.cursor_le_endIndex
            endIndex_le_size := fallbackContract.2.1.endIndex_le_size
            endByte_le_source := fallbackContract.2.1.endByte_le_source
            endByte_boundary := fallbackContract.2.1.endByte_boundary
            diagnosticsRev := by
              intro diagnostic member
              simpa [reset, fallbackContract.2.2] using
                inputValid.diagnosticsRev diagnostic member
          }
          have emittedValid := resetValid.emit_validFor failure.toDiagnostic
            (by simpa [reset, fallbackContract.2.2] using
              failure.toDiagnostic_span_validFor primaryContract.1)
          simp only [Reply.ValidFor]
          exact ⟨fallbackContract.1, emittedValid,
            by simpa [reset, State.emit] using fallbackContract.2.2⟩

/-- Recognized-statement fallback preserves every ordinary token window. -/
theorem recognizedStatementOrFallback_preservesTokenWindow
    (primary fallback : Parser Statement)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokenWindow
      (recognizedStatementOrFallback primary fallback) := by
  intro input
  have primaryContract := primaryShape input
  unfold recognizedStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      have fallbackContract := fallbackShape input
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨trivial, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          simpa only [primaryResult, fallbackResult, State.emit,
            Reply.PreservesTokenWindow] using fallbackContract

/-- Successful fallback retains the selected branch's token carrier. -/
theorem recognizedStatementOrFallback_preservesTokensOnSuccess
    (primary fallback : Parser Statement)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedStatementOrFallback primary fallback) :=
  (recognizedStatementOrFallback_preservesTokenWindow primary fallback
    primaryShape fallbackShape).preservesTokensOnSuccess

/-- Success-only carrier contracts also compose through this boundary. -/
theorem recognizedStatementOrFallback_preservesTokensOnSuccess_of_success
    (primary fallback : Parser Statement)
    (primaryPreserves : Parser.PreservesTokensOnSuccess primary)
    (fallbackPreserves : Parser.PreservesTokensOnSuccess fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have preserved := primaryPreserves input primaryValue afterPrimary
        primaryResult
      cases result
      exact preserved
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have preserved := fallbackPreserves input fallbackValue afterFallback
            fallbackResult
          cases result
          exact preserved

/-- Recognized fallback never rewinds either successful branch. -/
theorem recognizedStatementOrFallback_cursorMonotoneOnSuccess
    (primary fallback : Parser Statement)
    (primaryMonotone : Parser.CursorMonotoneOnSuccess primary)
    (fallbackMonotone : Parser.CursorMonotoneOnSuccess fallback) :
    Parser.CursorMonotoneOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have monotone := primaryMonotone input primaryValue afterPrimary
        primaryResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have monotone := fallbackMonotone input fallbackValue afterFallback
            fallbackResult
          cases result
          exact monotone

/-- Success begins at the input token of whichever branch was selected. -/
theorem recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess
    (primary fallback : Parser Statement)
    (primaryStarts : Parser.StartsAtCurrentTokenOnSuccess primary (·.span))
    (fallbackStarts : Parser.StartsAtCurrentTokenOnSuccess fallback (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (recognizedStatementOrFallback primary fallback) (·.span) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have starts := primaryStarts input primaryValue afterPrimary primaryResult
      cases result
      exact starts
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have starts := fallbackStarts input fallbackValue afterFallback
            fallbackResult
          cases result
          exact starts

/-- The compositional boundary needed by the complete statement dispatch. -/
structure StatementParserContract (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) : Prop where
  validFor : parser.ValidFor valueValid
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

namespace StatementParserContract

theorem preservesTokensOnSuccess
    {valueValid : SourceFile → Statement → Prop} {parser : Parser Statement}
    (contract : StatementParserContract valueValid parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

end StatementParserContract

/-- Both branch contracts compose through recognized fallback. -/
theorem recognizedStatementOrFallback_contract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryContract : StatementParserContract valueValid primary)
    (fallbackContract : StatementParserContract valueValid fallback) :
    StatementParserContract valueValid
      (recognizedStatementOrFallback primary fallback) := {
  validFor := recognizedStatementOrFallback_validFor primary fallback
    primaryContract.validFor fallbackContract.validFor
  preservesTokenWindow :=
    recognizedStatementOrFallback_preservesTokenWindow primary fallback
      primaryContract.preservesTokenWindow fallbackContract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    recognizedStatementOrFallback_cursorMonotoneOnSuccess primary fallback
      primaryContract.cursorMonotoneOnSuccess
      fallbackContract.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess primary fallback
      primaryContract.startsAtCurrentTokenOnSuccess
      fallbackContract.startsAtCurrentTokenOnSuccess
}

/-- Recursive parser contracts needed by one canonical statement layer. -/
structure StatementLayerInputs
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (nested : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) : Prop where
  nestedContract : StatementParserContract
    (Statement.ValidFor expressionValueValid patternValueValid YulStmt.ValidFor)
    nested
  expressionValid : expression.ValidFor expressionValueValid
  expressionSpanValid : ∀ file value,
    expressionValueValid file value → value.span.ValidFor file
  expressionWindow : Parser.PreservesTokenWindow expression
  expressionCursorLt : ∀ {input next : State} {value : Expr},
    expression input = .ok value next → input.cursor < next.cursor
  expressionStarts :
    Parser.StartsAtCurrentTokenOnSuccess expression (·.span)
  patternValid : pattern.ValidFor patternValueValid
  patternWindow : Parser.PreservesTokenWindow pattern
  patternCursor : Parser.CursorMonotoneOnSuccess pattern

private theorem stateChoice_contract
    {valueValid : SourceFile → Statement → Prop}
    (condition : State → Bool) {first second : Parser Statement}
    (firstContract : StatementParserContract valueValid first)
    (secondContract : StatementParserContract valueValid second) :
    StatementParserContract valueValid (fun input =>
      if condition input then first input else second input) := {
  validFor := by
    intro input inputValid
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.validFor input inputValid
    · simpa [selected] using secondContract.validFor input inputValid
  preservesTokenWindow := by
    intro input
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.preservesTokenWindow input
    · simpa [selected] using secondContract.preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using result)
    · exact secondContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using result)
  startsAtCurrentTokenOnSuccess := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using result)
    · exact secondContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using result)
}

/-- Every branch of canonical statement dispatch composes from its recursive
statement, expression, and pattern boundaries. -/
theorem statementLayer_contract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (nested : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (inputs : StatementLayerInputs expressionValueValid patternValueValid
      nested expression pattern) :
    StatementParserContract
      (Statement.ValidFor expressionValueValid patternValueValid
        YulStmt.ValidFor)
      (statementLayer nested expression pattern) := by
  let targetValid := Statement.ValidFor expressionValueValid patternValueValid
    YulStmt.ValidFor
  let fallback := assignmentOrExpressionStatement expression
  have expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ parsed => Nat.le_of_lt (inputs.expressionCursorLt parsed)
  have expressionTokens : Parser.PreservesTokensOnSuccess expression :=
    inputs.expressionWindow.preservesTokensOnSuccess
  have nestedTokens : Parser.PreservesTokensOnSuccess nested :=
    inputs.nestedContract.preservesTokensOnSuccess
  have fallbackContract : StatementParserContract targetValid fallback := {
    validFor := assignmentOrExpressionStatement_validFor expression
      expressionValueValid patternValueValid YulStmt.ValidFor
      inputs.expressionValid inputs.expressionSpanValid inputs.expressionWindow
      inputs.expressionCursorLt inputs.expressionStarts
    preservesTokenWindow :=
      assignmentOrExpressionStatement_preservesTokenWindow expression
        inputs.expressionWindow
    cursorMonotoneOnSuccess :=
      assignmentOrExpressionStatement_cursorMonotoneOnSuccess expression
        expressionCursor
    startsAtCurrentTokenOnSuccess :=
      assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess expression
        inputs.expressionStarts
  }
  have letContract : StatementParserContract targetValid
      (letStatement expression) := {
    validFor := letStatement_validFor expression expressionValueValid
      patternValueValid YulStmt.ValidFor inputs.expressionValid
      inputs.expressionWindow expressionCursor
    preservesTokenWindow := letStatement_preservesTokenWindow expression
      inputs.expressionWindow
    cursorMonotoneOnSuccess := letStatement_cursorMonotoneOnSuccess expression
      expressionCursor
    startsAtCurrentTokenOnSuccess :=
      letStatement_startsAtCurrentTokenOnSuccess expression
  }
  have returnContract : StatementParserContract targetValid
      (returnStatement expression) := {
    validFor := returnStatement_validFor expression expressionValueValid
      patternValueValid YulStmt.ValidFor inputs.expressionValid
      inputs.expressionWindow expressionCursor
    preservesTokenWindow := returnStatement_preservesTokenWindow expression
      inputs.expressionWindow
    cursorMonotoneOnSuccess := returnStatement_cursorMonotoneOnSuccess expression
      expressionCursor
    startsAtCurrentTokenOnSuccess :=
      returnStatement_startsAtCurrentTokenOnSuccess expression
  }
  have matchContract : StatementParserContract targetValid
      (matchStatement nested expression pattern) := {
    validFor := matchStatement_validFor expressionValueValid patternValueValid
      YulStmt.ValidFor nested expression pattern inputs.nestedContract.validFor
      inputs.nestedContract.preservesTokenWindow inputs.expressionValid
      expressionTokens inputs.patternValid inputs.patternWindow
      inputs.patternCursor
    preservesTokenWindow := matchStatement_preservesTokenWindow nested expression
      pattern inputs.nestedContract.preservesTokenWindow inputs.expressionWindow
      inputs.patternWindow
    cursorMonotoneOnSuccess :=
      matchStatement_cursorMonotoneOnSuccess nested expression pattern
    startsAtCurrentTokenOnSuccess :=
      matchStatement_startsAtCurrentTokenOnSuccess nested expression pattern
  }
  have forContract : StatementParserContract targetValid
      (forStatement nested expression) := {
    validFor := forStatement_validFor expressionValueValid patternValueValid
      YulStmt.ValidFor nested expression inputs.nestedContract.validFor
      nestedTokens inputs.expressionValid inputs.expressionSpanValid
      inputs.expressionWindow inputs.expressionCursorLt inputs.expressionStarts
    preservesTokenWindow := forStatement_preservesTokenWindow nested expression
      inputs.nestedContract.preservesTokenWindow inputs.expressionWindow
    cursorMonotoneOnSuccess := forStatement_cursorMonotoneOnSuccess nested
      expression expressionCursor
    startsAtCurrentTokenOnSuccess :=
      forStatement_startsAtCurrentTokenOnSuccess nested expression
  }
  have whileContract : StatementParserContract targetValid
      (whileStatement nested expression) := {
    validFor := whileStatement_validFor expressionValueValid patternValueValid
      YulStmt.ValidFor nested expression inputs.nestedContract.validFor
      nestedTokens inputs.expressionValid expressionTokens expressionCursor
    preservesTokenWindow := whileStatement_preservesTokenWindow nested expression
      inputs.nestedContract.preservesTokenWindow inputs.expressionWindow
    cursorMonotoneOnSuccess := whileStatement_cursorMonotoneOnSuccess nested
      expression expressionCursor
    startsAtCurrentTokenOnSuccess :=
      whileStatement_startsAtCurrentTokenOnSuccess nested expression
  }
  have ifContract : StatementParserContract targetValid
      (ifStatement nested expression) := {
    validFor := ifStatement_validFor expressionValueValid patternValueValid
      YulStmt.ValidFor nested expression inputs.nestedContract.validFor
      nestedTokens inputs.expressionValid expressionTokens expressionCursor
    preservesTokenWindow := ifStatement_preservesTokenWindow nested expression
      inputs.nestedContract.preservesTokenWindow inputs.expressionWindow
    cursorMonotoneOnSuccess := ifStatement_cursorMonotoneOnSuccess nested
      expression expressionCursor
    startsAtCurrentTokenOnSuccess :=
      ifStatement_startsAtCurrentTokenOnSuccess nested expression
  }
  have assemblyContract : StatementParserContract targetValid
      assemblyStatement := {
    validFor := assemblyStatement_validFor expressionValueValid
      patternValueValid YulStmt.ValidFor (fun _ _ valid => valid)
    preservesTokenWindow := assemblyStatement_preservesTokenWindow
    cursorMonotoneOnSuccess := assemblyStatement_cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assemblyStatement_startsAtCurrentTokenOnSuccess
  }
  have blockContract : StatementParserContract targetValid
      (blockStatement nested) := {
    validFor := blockStatement_validFor nested expressionValueValid
      patternValueValid YulStmt.ValidFor inputs.nestedContract.validFor
      nestedTokens
    preservesTokenWindow := blockStatement_preservesTokenWindow nested
      inputs.nestedContract.preservesTokenWindow
    cursorMonotoneOnSuccess := blockStatement_cursorMonotoneOnSuccess nested
    startsAtCurrentTokenOnSuccess :=
      blockStatement_startsAtCurrentTokenOnSuccess nested
  }
  have breakContract : StatementParserContract targetValid breakStatement := {
    validFor := breakStatement_validFor expressionValueValid patternValueValid
      YulStmt.ValidFor
    preservesTokenWindow := breakStatement_preservesTokenWindow
    cursorMonotoneOnSuccess := breakStatement_cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      breakStatement_startsAtCurrentTokenOnSuccess
  }
  have continueContract : StatementParserContract targetValid
      continueStatement := {
    validFor := continueStatement_validFor expressionValueValid
      patternValueValid YulStmt.ValidFor
    preservesTokenWindow := continueStatement_preservesTokenWindow
    cursorMonotoneOnSuccess := continueStatement_cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      continueStatement_startsAtCurrentTokenOnSuccess
  }
  let recovered := fun (primary : Parser Statement)
      (contract : StatementParserContract targetValid primary) =>
    recognizedStatementOrFallback_contract primary fallback contract
      fallbackContract
  have tail := stateChoice_contract (fun state =>
    isKeyword state .continueKw) (recovered continueStatement continueContract)
    fallbackContract
  have tail := stateChoice_contract (fun state => isKeyword state .breakKw)
    (recovered breakStatement breakContract) tail
  have tail := stateChoice_contract (fun state => isSymbol state .leftBrace)
    (recovered (blockStatement nested) blockContract) tail
  have tail := stateChoice_contract (fun state =>
    isKeyword state .assemblyKw) (recovered assemblyStatement assemblyContract) tail
  have tail := stateChoice_contract (fun state => isKeyword state .ifKw)
    (recovered (ifStatement nested expression) ifContract) tail
  have tail := stateChoice_contract (fun state => isContextual state .while)
    (recovered (whileStatement nested expression) whileContract) tail
  have tail := stateChoice_contract (fun state => isKeyword state .forKw)
    (recovered (forStatement nested expression) forContract) tail
  have tail := stateChoice_contract (fun state => isKeyword state .matchKw)
    (recovered (matchStatement nested expression pattern) matchContract) tail
  have tail := stateChoice_contract (fun state => isKeyword state .returnKw)
    (recovered (returnStatement expression) returnContract) tail
  have complete := stateChoice_contract (fun state => isKeyword state .letKw)
    (recovered (letStatement expression) letContract) tail
  unfold statementLayer
  exact complete

end Solcore.Syntax.Parser.TermInternals
