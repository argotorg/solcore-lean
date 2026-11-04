import Solcore.Syntax.Parser.Terms
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser.Internal.MatchSoundness
import Solcore.Syntax.Grammar.TermLevels
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Declarations
import Solcore.Syntax.Parser.Internal.ParameterSoundness

/-!
Proofs about the parsers of the fuel-indexed term parsers: token-window and cursor laws,
source validity, soundness against the declarative grammar, and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TermStatementProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelOrdinaryOutcomeSoundnessContract
/-! Executable reflection contracts for one mutual Core recursion fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Success and exact rejection reflection for all three mutually recursive
Core parsers at one shared fuel. -/
structure CoreTermFuelOrdinaryOutcomeSoundness (fuel : Nat) : Prop where
  expression :
    (∀ {input output : State} {value : Expr},
      coreExpressionWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreExpressionWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)
  pattern :
    (∀ {input output : State} {value : Pattern},
      corePatternWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      corePatternWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CorePatternRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)
  statement :
    (∀ {input output : State} {value : Statement},
      coreStatementWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreStatementWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreStatementRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermExpressionProperties
/-! Fuel-inductive contracts for the public canonical Core expression parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- The statement-side assumptions needed by recursive expression blocks. -/
structure CoreStatementFuelContract
    (statementValid : SourceFile → Statement → Prop) : Prop where
  validFor : ∀ fuel,
    (coreStatementWithFuel fuel).ValidFor statementValid
  preservesTokenWindow : ∀ fuel,
    Parser.PreservesTokenWindow (coreStatementWithFuel fuel)
  spanValid : ∀ (file : SourceFile) (statement : Statement),
    statementValid file statement → statement.span.ValidFor file

/-- Every fuel-bounded Core expression parser satisfies the complete
expression contract when its same-fuel statement parser satisfies the block
boundary. -/
theorem coreExpressionWithFuel_contract
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid) :
    ∀ fuel, ExpressionInternals.ExpressionContract statementValid
      (coreExpressionWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      refine {
        validFor := ?_
        preservesTokenWindow := ?_
        cursorLtOnSuccess := ?_
        startsAtCurrentTokenOnSuccess := ?_
      }
      · intro input inputValid
        trivial
      · intro input
        trivial
      · intro input next value parsed
        simp [coreExpressionWithFuel] at parsed
      · intro input value next parsed
        simp [coreExpressionWithFuel] at parsed
  | succ fuel inductionHypothesis =>
      let statement := coreStatementWithFuel fuel
      let rawBlock := coreBlock statement .require
      let block := isolateBlock rawBlock
      have rawBlockValid : rawBlock.ValidFor
          (Block.ValidFor statementValid) :=
        coreBlock_validFor statementValid statement .require
          (statementContract.validFor fuel)
          (statementContract.preservesTokenWindow fuel).preservesTokensOnSuccess
          statementContract.spanValid
      have blockValid : block.ValidFor (Block.ValidFor statementValid) :=
        isolateBlock_validFor statementValid rawBlock rawBlockValid
      have rawBlockWindow : Parser.PreservesTokenWindow rawBlock :=
        coreBlock_preservesTokenWindow statement .require
          (statementContract.preservesTokenWindow fuel)
      have blockWindow : Parser.PreservesTokenWindow block :=
        isolateBlock_preservesTokenWindow rawBlock rawBlockWindow
      have blockCursor : Parser.CursorMonotoneOnSuccess block :=
        isolateBlock_cursorMonotoneOnSuccess rawBlock
          (coreBlock_cursorMonotoneOnSuccess statement .require)
      have blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span) :=
        isolateBlock_startsAtCurrentTokenOnSuccess rawBlock
          (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
      simpa only [coreExpressionWithFuel, statement, rawBlock, block] using
        ExpressionInternals.expressionLayer_concrete_contract
          (coreExpressionWithFuel fuel) block statementValid
          inductionHypothesis blockValid blockWindow blockCursor blockStarts

/-- Fuel-bounded Core expression parsing preserves source provenance. -/
theorem coreExpressionWithFuel_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    (coreExpressionWithFuel fuel).ValidFor
      (Expr.ValidFor statementValid) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).validFor

/-- Fuel-bounded Core expression parsing preserves ordinary token windows. -/
theorem coreExpressionWithFuel_preservesTokenWindow
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.PreservesTokenWindow (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).preservesTokenWindow

/-- Fuel-bounded Core expression success retains its token carrier. -/
theorem coreExpressionWithFuel_preservesTokensOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).preservesTokensOnSuccess

/-- Fuel-bounded Core expression success strictly advances. -/
theorem coreExpressionWithFuel_cursor_lt_onSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) {input next : State} {value : Expr}
    (parsed : coreExpressionWithFuel fuel input = .ok value next) :
    input.cursor < next.cursor :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).cursorLtOnSuccess parsed

/-- Fuel-bounded Core expression success is cursor-monotone. -/
theorem coreExpressionWithFuel_cursorMonotoneOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).cursorMonotoneOnSuccess

/-- Fuel-bounded Core expression success begins at its current token. -/
theorem coreExpressionWithFuel_startsAtCurrentTokenOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (coreExpressionWithFuel fuel) (·.span) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).startsAtCurrentTokenOnSuccess

end TermInternals

/-- Lift the fuel-indexed proof to the public state-sized expression parser. -/
theorem expression_contract_of_coreStatement
    (statementValid : SourceFile → Statement → Prop)
    (statementContract :
      TermInternals.CoreStatementFuelContract statementValid) :
    ExpressionInternals.ExpressionContract statementValid expression := {
  validFor := by
    intro input inputValid
    unfold expression
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold expression
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).preservesTokenWindow input
  cursorLtOnSuccess := by
    intro input next value parsed
    unfold expression at parsed
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).cursorLtOnSuccess parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold expression at parsed
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermPatternProperties
/-! Fuel-inductive contracts for the public canonical pattern parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- Every fuel-bounded pattern parser preserves ordinary token windows. -/
theorem corePatternWithFuel_preservesTokenWindow
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.PreservesTokenWindow (corePatternWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_preservesTokenWindow
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        inductionHypothesis (expressionPreserves fuel)

/-- Every successful fuel-bounded pattern parse retains its token carrier. -/
theorem corePatternWithFuel_preservesTokensOnSuccess
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel))
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (corePatternWithFuel fuel) :=
  (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel).preservesTokensOnSuccess

/-- Fuel-bounded pattern successes never rewind their caller. -/
theorem corePatternWithFuel_cursorMonotoneOnSuccess
    (expressionMonotone : ∀ fuel,
      Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.CursorMonotoneOnSuccess (corePatternWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input pattern next result
      simp [corePatternWithFuel] at result
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_cursorMonotoneOnSuccess
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        inductionHypothesis (expressionMonotone fuel)

/-- Fuel-bounded pattern successes start at their current input token. -/
theorem corePatternWithFuel_startsAtCurrentTokenOnSuccess
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.StartsAtCurrentTokenOnSuccess
      (corePatternWithFuel fuel) (·.span) := by
  intro fuel
  cases fuel with
  | zero =>
      intro input pattern next result
      simp [corePatternWithFuel] at result
  | succ fuel =>
      exact PatternInternals.patternLayer_startsAtCurrentTokenOnSuccess
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel)
        (expressionPreserves fuel)

/-- Every fuel-bounded pattern parser retains recursive source provenance. -/
theorem corePatternWithFuel_validFor
    (expressionValid : SourceFile → Expr → Prop)
    (expressionParserValid : ∀ fuel,
      (coreExpressionWithFuel fuel).ValidFor expressionValid)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (coreExpressionWithFuel fuel) (·.span))
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, (corePatternWithFuel fuel).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro fuel
  induction fuel with
  | zero => intro input inputValid; trivial
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_validFor
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        expressionValid inductionHypothesis
        (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel)
        (expressionParserValid fuel) expressionSpanValid
        (expressionStarts fuel) (expressionPreserves fuel)

end TermInternals

/-- Public pattern parsing preserves ordinary token windows when Core
expression parsing does so at every fuel. -/
theorem pattern_preservesTokenWindow_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.PreservesTokenWindow pattern := by
  intro input
  unfold pattern
  exact TermInternals.corePatternWithFuel_preservesTokenWindow
    expressionPreserves (input.remainingCount + 1) input

/-- Public pattern success retains the token carrier under the same
compositional expression contract. -/
theorem pattern_preservesTokensOnSuccess_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.PreservesTokensOnSuccess pattern :=
  (pattern_preservesTokenWindow_of_coreExpression expressionPreserves).preservesTokensOnSuccess

/-- Public pattern success is cursor-monotone whenever fuel-bounded Core
expression success is cursor-monotone. -/
theorem pattern_cursorMonotoneOnSuccess_of_coreExpression
    (expressionMonotone : ∀ fuel,
      Parser.CursorMonotoneOnSuccess
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.CursorMonotoneOnSuccess pattern := by
  intro input value next result
  unfold pattern at result
  exact TermInternals.corePatternWithFuel_cursorMonotoneOnSuccess
    expressionMonotone (input.remainingCount + 1) input value next result

/-- Public pattern success starts at the current token whenever fuel-bounded
Core expression parsing preserves token windows. -/
theorem pattern_startsAtCurrentTokenOnSuccess_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.StartsAtCurrentTokenOnSuccess pattern (·.span) := by
  intro input value next result
  unfold pattern at result
  exact TermInternals.corePatternWithFuel_startsAtCurrentTokenOnSuccess
    expressionPreserves (input.remainingCount + 1) input value next result

/-- Public pattern parsing retains recursive source provenance under the
fuel-indexed Core expression contracts required by comptime patterns. -/
theorem pattern_validFor_of_coreExpression
    (expressionValid : SourceFile → Expr → Prop)
    (expressionParserValid : ∀ fuel,
      (TermInternals.coreExpressionWithFuel fuel).ValidFor expressionValid)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (TermInternals.coreExpressionWithFuel fuel) (·.span))
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    pattern.ValidFor (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold pattern
  exact TermInternals.corePatternWithFuel_validFor expressionValid
    expressionParserValid expressionSpanValid expressionStarts
    expressionPreserves (input.remainingCount + 1) input inputValid

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermRecursiveProperties
/-! Simultaneous fuel contracts for canonical Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- The syntax validity produced by one canonical statement layer. -/
abbrev RecursiveStatementValid
    (statementValid : SourceFile → Statement → Prop) :
    SourceFile → Statement → Prop :=
  Statement.ValidFor (Expr.ValidFor statementValid)
    (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor

/-- Explicitly close canonical syntax validity into a client statement
predicate.  This post-fixed-point assumption is intentionally not implicit. -/
structure RecursiveStatementClosure
    (statementValid : SourceFile → Statement → Prop) : Prop where
  close : ∀ file statement,
    RecursiveStatementValid statementValid file statement →
      statementValid file statement

/-- Complete contracts for one fuel-bounded recursive pattern parser. -/
structure PatternParserContract
    (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Pattern) : Prop where
  validFor : parser.ValidFor
    (Pattern.ValidFor (Expr.ValidFor statementValid))
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

namespace PatternParserContract

theorem preservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop}
    {parser : Parser Pattern}
    (contract : PatternParserContract statementValid parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

end PatternParserContract

/-- Expression, pattern, and statement contracts at one identical fuel. -/
structure RecursiveFuelContract
    (statementValid : SourceFile → Statement → Prop)
    (fuel : Nat) : Prop where
  expression : ExpressionInternals.ExpressionContract statementValid
    (coreExpressionWithFuel fuel)
  pattern : PatternParserContract statementValid (corePatternWithFuel fuel)
  statement : StatementParserContract
    (RecursiveStatementValid statementValid) (coreStatementWithFuel fuel)

namespace RecursiveFuelContract

theorem expressionPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (coreExpressionWithFuel fuel) :=
  contract.expression.preservesTokensOnSuccess

theorem expressionCursorMonotoneOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel) :=
  contract.expression.cursorMonotoneOnSuccess

theorem patternPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (corePatternWithFuel fuel) :=
  contract.pattern.preservesTokensOnSuccess

theorem statementPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (coreStatementWithFuel fuel) :=
  contract.statement.preservesTokensOnSuccess

theorem statementValidFor
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel)
    (closure : RecursiveStatementClosure statementValid) :
    (coreStatementWithFuel fuel).ValidFor statementValid :=
  contract.statement.validFor.mono closure.close

end RecursiveFuelContract

/-- The three mutually recursive Core parsers satisfy their complete contracts
at every common fuel, conditional on the explicit statement-validity closure. -/
theorem coreRecursiveWithFuel_contract
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) :
    ∀ fuel, RecursiveFuelContract statementValid fuel := by
  intro fuel
  induction fuel with
  | zero =>
      have expressionZero : ExpressionInternals.ExpressionContract
          statementValid (coreExpressionWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorLtOnSuccess := by
          intro input next value parsed
          simp [coreExpressionWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [coreExpressionWithFuel] at parsed
      }
      have patternZero : PatternParserContract statementValid
          (corePatternWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorMonotoneOnSuccess := by
          intro input value next parsed
          simp [corePatternWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [corePatternWithFuel] at parsed
      }
      have statementZero : StatementParserContract
          (RecursiveStatementValid statementValid)
          (coreStatementWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorMonotoneOnSuccess := by
          intro input value next parsed
          simp [coreStatementWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [coreStatementWithFuel] at parsed
      }
      exact {
        expression := expressionZero
        pattern := patternZero
        statement := statementZero
      }
  | succ fuel inductionHypothesis =>
      let statement := coreStatementWithFuel fuel
      let rawBlock := coreBlock statement .require
      let block := isolateBlock rawBlock
      have rawBlockCanonical : rawBlock.ValidFor
          (Block.ValidFor (RecursiveStatementValid statementValid)) :=
        coreBlock_validFor (RecursiveStatementValid statementValid)
          statement .require
          inductionHypothesis.statement.validFor
          inductionHypothesis.statement.preservesTokensOnSuccess
          (fun _ _ valid => valid.span_valid)
      have rawBlockValid : rawBlock.ValidFor (Block.ValidFor statementValid) :=
        rawBlockCanonical.mono (fun file body valid =>
          ⟨valid.1, fun retained member =>
            closure.close file retained (valid.2 retained member)⟩)
      have blockValid : block.ValidFor (Block.ValidFor statementValid) :=
        isolateBlock_validFor statementValid rawBlock rawBlockValid
      have rawBlockWindow : Parser.PreservesTokenWindow rawBlock :=
        coreBlock_preservesTokenWindow statement .require
          inductionHypothesis.statement.preservesTokenWindow
      have blockWindow : Parser.PreservesTokenWindow block :=
        isolateBlock_preservesTokenWindow rawBlock rawBlockWindow
      have blockCursor : Parser.CursorMonotoneOnSuccess block :=
        isolateBlock_cursorMonotoneOnSuccess rawBlock
          (coreBlock_cursorMonotoneOnSuccess statement .require)
      have blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span) :=
        isolateBlock_startsAtCurrentTokenOnSuccess rawBlock
          (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
      have expressionLayerContract :=
        ExpressionInternals.expressionLayer_concrete_contract
          (coreExpressionWithFuel fuel) block statementValid
          inductionHypothesis.expression blockValid blockWindow blockCursor
          blockStarts
      have expressionContract : ExpressionInternals.ExpressionContract
          statementValid (coreExpressionWithFuel (fuel + 1)) := by
        simpa only [coreExpressionWithFuel, statement, rawBlock, block] using
          expressionLayerContract
      have patternLayerContract : PatternParserContract statementValid
          (patternLayer (corePatternWithFuel fuel)
            (coreExpressionWithFuel fuel)) := {
        validFor := PatternInternals.patternLayer_validFor
          (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
          (Expr.ValidFor statementValid) inductionHypothesis.pattern.validFor
          inductionHypothesis.pattern.preservesTokenWindow
          inductionHypothesis.expression.validFor
          (fun valid => valid.span_valid)
          inductionHypothesis.expression.startsAtCurrentTokenOnSuccess
          inductionHypothesis.expression.preservesTokenWindow
        preservesTokenWindow := PatternInternals.patternLayer_preservesTokenWindow
          (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
          inductionHypothesis.pattern.preservesTokenWindow
          inductionHypothesis.expression.preservesTokenWindow
        cursorMonotoneOnSuccess :=
          PatternInternals.patternLayer_cursorMonotoneOnSuccess
            (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
            inductionHypothesis.pattern.cursorMonotoneOnSuccess
            inductionHypothesis.expression.cursorMonotoneOnSuccess
        startsAtCurrentTokenOnSuccess :=
          PatternInternals.patternLayer_startsAtCurrentTokenOnSuccess
            (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
            inductionHypothesis.pattern.preservesTokenWindow
            inductionHypothesis.expression.preservesTokenWindow
      }
      have patternContract : PatternParserContract statementValid
          (corePatternWithFuel (fuel + 1)) := by
        simpa only [corePatternWithFuel] using patternLayerContract
      have layerInputs : StatementLayerInputs
          (Expr.ValidFor statementValid)
          (Pattern.ValidFor (Expr.ValidFor statementValid))
          (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
          (corePatternWithFuel fuel) := {
        nestedContract := inductionHypothesis.statement
        expressionValid := inductionHypothesis.expression.validFor
        expressionSpanValid := fun _ _ valid => valid.span_valid
        expressionWindow := inductionHypothesis.expression.preservesTokenWindow
        expressionCursorLt := inductionHypothesis.expression.cursorLtOnSuccess
        expressionStarts :=
          inductionHypothesis.expression.startsAtCurrentTokenOnSuccess
        patternValid := inductionHypothesis.pattern.validFor
        patternWindow := inductionHypothesis.pattern.preservesTokenWindow
        patternCursor := inductionHypothesis.pattern.cursorMonotoneOnSuccess
      }
      have statementLayerContract := statementLayer_contract
        (Expr.ValidFor statementValid)
        (Pattern.ValidFor (Expr.ValidFor statementValid))
        (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
        (corePatternWithFuel fuel) layerInputs
      have statementSyntax : StatementParserContract
          (RecursiveStatementValid statementValid)
          (coreStatementWithFuel (fuel + 1)) := by
        simpa only [coreStatementWithFuel, RecursiveStatementValid] using
          statementLayerContract
      exact {
        expression := expressionContract
        pattern := patternContract
        statement := statementSyntax
      }

/-- Reassemble the pattern half from the established all-fuel expression
family through the public lifts in `TermPatternProperties`. -/
theorem corePatternWithFuel_contract_of_recursive
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) (fuel : Nat) :
    PatternParserContract statementValid (corePatternWithFuel fuel) := {
  validFor := corePatternWithFuel_validFor (Expr.ValidFor statementValid)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.validFor)
    (fun valid => valid.span_valid)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.startsAtCurrentTokenOnSuccess)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.preservesTokenWindow)
    fuel
  preservesTokenWindow := corePatternWithFuel_preservesTokenWindow
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.preservesTokenWindow)
    fuel
  cursorMonotoneOnSuccess := corePatternWithFuel_cursorMonotoneOnSuccess
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.cursorMonotoneOnSuccess)
    fuel
  startsAtCurrentTokenOnSuccess :=
    corePatternWithFuel_startsAtCurrentTokenOnSuccess
      (fun fuel =>
        let contract := coreRecursiveWithFuel_contract statementValid closure fuel
        contract.expression.preservesTokenWindow)
      fuel
}

end TermInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TermCanonicalProperties
/-! Unconditional canonical contracts for the public Core term parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- Canonical recursive statement validity closes one constructed layer. -/
theorem canonicalStatementClosure :
    RecursiveStatementClosure CoreStatement.ValidFor := {
  close := fun _ _ valid => CoreStatement.ValidFor.ofStatement valid
}

/-- The simultaneous fuel theorem instantiated with canonical validity. -/
theorem coreRecursiveWithFuel_canonical_contract (fuel : Nat) :
    RecursiveFuelContract CoreStatement.ValidFor fuel :=
  coreRecursiveWithFuel_contract CoreStatement.ValidFor
    canonicalStatementClosure fuel

/-- The statement family required by the earlier expression-only lift. -/
theorem canonicalStatementFuelContract :
    CoreStatementFuelContract CoreStatement.ValidFor := {
  validFor := fun fuel =>
    (coreRecursiveWithFuel_canonical_contract fuel).statementValidFor
      canonicalStatementClosure
  preservesTokenWindow := fun fuel =>
    (coreRecursiveWithFuel_canonical_contract fuel).statement.preservesTokenWindow
  spanValid := fun _ _ valid => valid.span_valid
}

/-- Canonical fuel-bounded expression parsing has its complete contract. -/
theorem coreExpressionWithFuel_canonical_contract (fuel : Nat) :
    ExpressionInternals.ExpressionContract CoreStatement.ValidFor
      (coreExpressionWithFuel fuel) :=
  (coreRecursiveWithFuel_canonical_contract fuel).expression

/-- Canonical fuel-bounded pattern parsing has its complete contract. -/
theorem corePatternWithFuel_canonical_contract (fuel : Nat) :
    PatternParserContract CoreStatement.ValidFor (corePatternWithFuel fuel) :=
  (coreRecursiveWithFuel_canonical_contract fuel).pattern

/-- Canonical fuel-bounded statement parsing has its complete contract. -/
theorem coreStatementWithFuel_canonical_contract (fuel : Nat) :
    StatementParserContract CoreStatement.ValidFor
      (coreStatementWithFuel fuel) := by
  let syntaxContract :=
    (coreRecursiveWithFuel_canonical_contract fuel).statement
  exact {
    validFor := syntaxContract.validFor.mono canonicalStatementClosure.close
    preservesTokenWindow := syntaxContract.preservesTokenWindow
    cursorMonotoneOnSuccess := syntaxContract.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      syntaxContract.startsAtCurrentTokenOnSuccess
  }

end TermInternals

/-- The public expression parser preserves canonical recursive validity. -/
theorem expression_canonical_contract :
    ExpressionInternals.ExpressionContract CoreStatement.ValidFor expression :=
  expression_contract_of_coreStatement CoreStatement.ValidFor
    TermInternals.canonicalStatementFuelContract

/-- The public pattern parser preserves canonical recursive validity. -/
theorem pattern_canonical_contract :
    TermInternals.PatternParserContract CoreStatement.ValidFor pattern := {
  validFor := by
    intro input inputValid
    unfold pattern
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold pattern
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold pattern at parsed
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).cursorMonotoneOnSuccess
        input value next parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold pattern at parsed
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

/-- The public statement parser preserves canonical recursive validity. -/
theorem statement_canonical_contract :
    TermInternals.StatementParserContract CoreStatement.ValidFor statement := {
  validFor := by
    intro input inputValid
    unfold statement
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 2)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold statement
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 2)).preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold statement at parsed
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 2)).cursorMonotoneOnSuccess
        input value next parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold statement at parsed
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 2)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

/-- Public Core blocks retain canonical statement provenance. -/
theorem block_canonical_validFor (policy : TailExpressionPolicy) :
    (block policy).ValidFor (Block.ValidFor CoreStatement.ValidFor) := by
  intro input inputValid
  unfold block
  let statementContract :=
    TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)
  exact coreBlock_validFor CoreStatement.ValidFor
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    statementContract.validFor statementContract.preservesTokensOnSuccess
    (fun _ _ valid => valid.span_valid) input inputValid

/-- Public Core blocks preserve their complete token window. -/
theorem block_canonical_preservesTokenWindow (policy : TailExpressionPolicy) :
    Parser.PreservesTokenWindow (block policy) := by
  intro input
  unfold block
  exact coreBlock_preservesTokenWindow
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).preservesTokenWindow input

/-- Public Core-block success never rewinds its caller. -/
theorem block_canonical_cursorMonotoneOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.CursorMonotoneOnSuccess (block policy) := by
  intro input value next parsed
  unfold block at parsed
  exact coreBlock_cursorMonotoneOnSuccess
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    input value next parsed

/-- Public Core-block success starts at its opening brace. -/
theorem block_canonical_startsAtCurrentTokenOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.StartsAtCurrentTokenOnSuccess (block policy) (·.span) := by
  intro input value next parsed
  unfold block at parsed
  exact coreBlock_startsAtCurrentTokenOnSuccess
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    input value next parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelOrdinaryShapeProperties
/-! Unconditional parser shapes for ordinary mutual-fuel soundness proofs. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Trivial statement validity is closed under one recursive statement layer. -/
theorem ordinaryShapeStatementClosure :
    RecursiveStatementClosure (fun _ _ => True) := {
  close := by
    intro _ _ _
    trivial
}

/-- The mutual recursive parser contract with syntax validity erased. -/
theorem coreTermFuel_ordinaryShape_contract (fuel : Nat) :
    RecursiveFuelContract (fun _ _ => True) fuel :=
  coreRecursiveWithFuel_contract (fun _ _ => True)
    ordinaryShapeStatementClosure fuel

/-- Every fuel-bounded Core expression preserves its token window. -/
theorem coreExpressionWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (coreExpressionWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).expression.preservesTokenWindow

/-- Every successful fuel-bounded Core expression strictly advances. -/
theorem coreExpressionWithFuel_ordinary_cursor_lt_onSuccess (fuel : Nat)
    {input output : State} {value : Expr}
    (result : coreExpressionWithFuel fuel input = .ok value output) :
    input.cursor < output.cursor :=
  (coreTermFuel_ordinaryShape_contract fuel).expression.cursorLtOnSuccess
    result

/-- Every fuel-bounded Core pattern preserves its token window. -/
theorem corePatternWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (corePatternWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).pattern.preservesTokenWindow

/-- Every fuel-bounded Core statement preserves its token window. -/
theorem coreStatementWithFuel_ordinary_preservesTokenWindow (fuel : Nat) :
    Parser.PreservesTokenWindow (coreStatementWithFuel fuel) :=
  (coreTermFuel_ordinaryShape_contract fuel).statement.preservesTokenWindow

end Solcore.Syntax.Parser.TermInternals
end
