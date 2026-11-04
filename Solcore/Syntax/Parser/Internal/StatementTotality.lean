import Solcore.Syntax.Parser.Internal.TermTotality
import Solcore.Syntax.Parser.Internal.YulTotality
import Solcore.Syntax.Parser.Internal.TypeTotality
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.MatchSoundness
import Solcore.Syntax.Parser.Internal.BlockSoundness
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
Totality of the parsers of statements and blocks: on valid input they make progress and
end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ChoiceFuelTotalityProperties
/-! Fuel-total fallback and state-selected Core statement choices. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem adequate_left {left right count : Nat}
    (adequate : count < Nat.min left right) : count < left :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_left left right)

private theorem adequate_right {left right count : Nat}
    (adequate : count < Nat.min left right) : count < right :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_right left right)

namespace FuelStatementTotalityContract

/-- An unconditionally total branch is fuel-total at any chosen bound. -/
theorem ofTotality
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement}
    (contract : StatementTotalityContract valueValid parser) (fuel : Nat) :
    FuelStatementTotalityContract valueValid parser fuel := {
  toStatementParserContract := contract.toStatementParserContract
  ordinary := fun input inputValid _ => contract.invariantFree input inputValid
}

end FuelStatementTotalityContract

/-- Recognized fallback is ordinary below both branch fuel bounds. -/
theorem recognizedStatementOrFallback_ordinary_of_fuels
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelStatementTotalityContract valueValid primary primaryFuel)
    (fallbackContract :
      FuelStatementTotalityContract valueValid fallback fallbackFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < Nat.min primaryFuel fallbackFuel) :
    (∃ value next,
      recognizedStatementOrFallback primary fallback input = .ok value next) ∨
    (∃ failure next,
      recognizedStatementOrFallback primary fallback input =
        .reject failure next) := by
  rcases primaryContract.ordinary input inputValid (adequate_left adequate) with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedStatementOrFallback, primaryResult]⟩
  · rcases fallbackContract.ordinary input inputValid
        (adequate_right adequate) with
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

theorem recognizedStatementOrFallback_fuelTotalityContract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelStatementTotalityContract valueValid primary primaryFuel)
    (fallbackContract :
      FuelStatementTotalityContract valueValid fallback fallbackFuel) :
    FuelStatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback)
      (Nat.min primaryFuel fallbackFuel) := {
  toStatementParserContract := recognizedStatementOrFallback_contract
    primary fallback primaryContract.toStatementParserContract
      fallbackContract.toStatementParserContract
  ordinary := recognizedStatementOrFallback_ordinary_of_fuels primary fallback
    primaryFuel fallbackFuel primaryContract fallbackContract
}

theorem recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
    (primary fallback : Parser Statement)
    (primaryStrict : ∀ {input next : State} {value : Statement},
      primary input = .ok value next → input.cursor < next.cursor)
    (fallbackStrict : ∀ {input next : State} {value : Statement},
      fallback input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : Statement}
    (parsed : recognizedStatementOrFallback primary fallback input =
      .ok value final) :
    input.cursor < final.cursor := by
  unfold recognizedStatementOrFallback at parsed
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at parsed
  | ok primaryValue next =>
      simp only [primaryResult] at parsed
      cases parsed
      exact primaryStrict primaryResult
  | reject failure rejected =>
      simp only [primaryResult] at parsed
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at parsed
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at parsed
      | ok fallbackValue next =>
          simp only [fallbackResult] at parsed
          cases parsed
          have progress : input.cursor < next.cursor :=
            fallbackStrict fallbackResult
          change input.cursor < next.cursor
          exact progress

/-- State-selected dispatch preserves both branch contracts and fuel bounds. -/
theorem stateChoice_fuelTotalityContract
    {valueValid : SourceFile → Statement → Prop}
    (condition : State → Bool) (first second : Parser Statement)
    (firstFuel secondFuel : Nat)
    (firstContract :
      FuelStatementTotalityContract valueValid first firstFuel)
    (secondContract :
      FuelStatementTotalityContract valueValid second secondFuel) :
    FuelStatementTotalityContract valueValid
      (fun input => if condition input then first input else second input)
      (Nat.min firstFuel secondFuel) := {
  toStatementParserContract := {
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
  ordinary := by
    intro input inputValid adequate
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.ordinary input inputValid
        (adequate_left adequate)
    · simpa [selected] using secondContract.ordinary input inputValid
        (adequate_right adequate)
}

theorem stateChoice_cursor_lt_onSuccess_of_strict
    (condition : State → Bool) (first second : Parser Statement)
    (firstStrict : ∀ {input next : State} {value : Statement},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : Statement},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : Statement}
    (parsed : (fun state => if condition state then first state
      else second state) input = .ok value final) :
    input.cursor < final.cursor := by
  by_cases selected : condition input = true
  · exact firstStrict (by simpa [selected] using parsed)
  · exact secondStrict (by simpa [selected] using parsed)

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.AssemblyTotalityProperties
/-! Valid-input totality for Core inline-assembly statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Inline assembly has only ordinary outcomes on every valid parser state. -/
theorem assemblyStatement_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ statement final, assemblyStatement input = .ok statement final) ∨
      (∃ failure final,
        assemblyStatement input = .reject failure final) := by
  rcases (keyword_ordinary .assemblyKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .assemblyKw .statement input
      inputValid
    rw [markerResult] at markerReply
    have bodyFree : Parser.InvariantFreeOnValid yulBody :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulBody_elementTotalityContract.invariantFree
    rcases bodyFree afterMarker markerReply.2.1 with
      ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span body.span
          value := .assembly body.body
        }, final, by
          simp only [assemblyStatement, bind, markerResult, bodyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [assemblyStatement, bind, markerResult, bodyResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [assemblyStatement, bind, markerResult]⟩

theorem assemblyStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid assemblyStatement :=
  assemblyStatement_ordinary

theorem assemblyStatement_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assemblyStatement input ≠ .invariant error :=
  assemblyStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- The public assembly parser is also a strict reusable parser element. -/
theorem assemblyStatement_elementTotalityContract :
    ElementTotalityContract assemblyStatement := {
  validFor := (assemblyStatement_validFor
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ _ => trivial)).mono (fun _ _ _ => trivial)
  preservesTokenWindow := assemblyStatement_preservesTokenWindow
  cursorLtOnSuccess := assemblyStatement_cursor_lt_onSuccess
  invariantFree := assemblyStatement_ne_invariant
}

/-- Strict assembly element totality is fuel-valid at every chosen bound. -/
theorem assemblyStatement_fuelElementTotalityContract (fuel : Nat) :
    FuelElementTotalityContract assemblyStatement fuel := {
  validFor := assemblyStatement_elementTotalityContract.validFor
  preservesTokenWindow :=
    assemblyStatement_elementTotalityContract.preservesTokenWindow
  cursorLtOnSuccess :=
    assemblyStatement_elementTotalityContract.cursorLtOnSuccess
  ordinary := fun input inputValid _ =>
    assemblyStatement_ordinary input inputValid
}

/-- Complete semantic-value, state-window, and totality laws for assembly. -/
theorem assemblyStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (yulValid : ∀ file statement,
      YulStmt.ValidFor file statement → yulValueValid file statement) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      assemblyStatement := {
  toStatementParserContract := {
    validFor := assemblyStatement_validFor expressionValueValid
      patternValueValid yulValueValid yulValid
    preservesTokenWindow := assemblyStatement_preservesTokenWindow
    cursorMonotoneOnSuccess := assemblyStatement_cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assemblyStatement_startsAtCurrentTokenOnSuccess
  }
  invariantFree := assemblyStatement_invariantFreeOnValid
}

/-- The unconditional assembly proof is fuel-total at every chosen bound. -/
theorem assemblyStatement_fuelTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (yulValid : ∀ file statement,
      YulStmt.ValidFor file statement → yulValueValid file statement)
    (fuel : Nat) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      assemblyStatement fuel := {
  toStatementParserContract :=
    (assemblyStatement_totalityContract expressionValueValid
      patternValueValid yulValueValid yulValid).toStatementParserContract
  ordinary := fun input inputValid _ =>
    assemblyStatement_ordinary input inputValid
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ControlLeafTotalityProperties
/-! Totality for semicolon-terminated control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ControlInternals

theorem terminatedControl_invariantFreeOnValid
    (keywordValue : HardKeyword) (value : StatementValue) :
    Parser.InvariantFreeOnValid (terminatedControl keywordValue value) := by
  unfold terminatedControl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor keywordValue .statement)
    (keyword_ordinary keywordValue .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value
  } : Statement)

end ControlInternals

theorem breakStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid breakStatement := by
  simpa only [breakStatement] using
    ControlInternals.terminatedControl_invariantFreeOnValid
      .breakKw .breakStmt

theorem continueStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid continueStatement := by
  simpa only [continueStatement] using
    ControlInternals.terminatedControl_invariantFreeOnValid
      .continueKw .continueStmt

theorem breakStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      breakStatement := {
  validFor := breakStatement_validFor expressionValueValid patternValueValid
    yulValueValid
  preservesTokenWindow := breakStatement_preservesTokenWindow
  cursorMonotoneOnSuccess := breakStatement_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    breakStatement_startsAtCurrentTokenOnSuccess
  invariantFree := breakStatement_invariantFreeOnValid
}

theorem continueStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      continueStatement := {
  validFor := continueStatement_validFor expressionValueValid
    patternValueValid yulValueValid
  preservesTokenWindow := continueStatement_preservesTokenWindow
  cursorMonotoneOnSuccess := continueStatement_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    continueStatement_startsAtCurrentTokenOnSuccess
  invariantFree := continueStatement_invariantFreeOnValid
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.SimpleBranchTotalityProperties
/-! Totality for the non-recovering `let` and `return` statement branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem optionalLetType_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalLetType := by
  unfold optionalLetType
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .colon .statement)
      (symbol_ordinary .colon .statement).invariantFreeOnValid
    intro colon
    apply Parser.bind_invariantFreeOnValid typeExpr_validFor
      typeExpr_invariantFreeOnValid
    intro type
    exact Parser.pure_invariantFreeOnValid (some type)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalLetInitializer_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalLetInitializer expression) := by
  unfold optionalLetInitializer
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .equal .statement)
      (symbol_ordinary .equal .statement).invariantFreeOnValid
    intro equal
    apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
    intro value
    exact Parser.pure_invariantFreeOnValid (some value)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalReturnValue_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalReturnValue expression) := by
  unfold optionalReturnValue
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · exact Parser.pure_invariantFreeOnValid none
  · apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
    intro value
    exact Parser.pure_invariantFreeOnValid (some value)

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem letStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (letStatement expression) := by
  unfold letStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .letKw .statement)
    (keyword_ordinary .letKw .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid (identifier_validFor .statement)
    (identifier_ordinary .statement).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    StatementSimpleInternals.optionalLetType_validFor
    StatementSimpleInternals.optionalLetType_invariantFreeOnValid
  intro type
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalLetInitializer_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalLetInitializer_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro initializer
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value := .letDecl name type initializer
  } : Statement)

theorem returnStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (returnStatement expression) := by
  unfold returnStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .returnKw .statement)
    (keyword_ordinary .returnKw .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalReturnValue_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalReturnValue_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro value
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value := .returnStmt value
  } : Statement)

theorem letStatement_totalityContract
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        YulStmt.ValidFor)
      (letStatement expression) := {
  validFor := letStatement_validFor expression expressionValueValid
    patternValueValid YulStmt.ValidFor expressionValid expressionWindow
      expressionCursor
  preservesTokenWindow := letStatement_preservesTokenWindow expression
    expressionWindow
  cursorMonotoneOnSuccess := letStatement_cursorMonotoneOnSuccess expression
    expressionCursor
  startsAtCurrentTokenOnSuccess :=
    letStatement_startsAtCurrentTokenOnSuccess expression
  invariantFree := letStatement_invariantFreeOnValid expression
    (expressionValid.mono (fun _ _ _ => trivial)) expressionFree
}

theorem returnStatement_totalityContract
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        YulStmt.ValidFor)
      (returnStatement expression) := {
  validFor := returnStatement_validFor expression expressionValueValid
    patternValueValid YulStmt.ValidFor expressionValid expressionWindow
      expressionCursor
  preservesTokenWindow := returnStatement_preservesTokenWindow expression
    expressionWindow
  cursorMonotoneOnSuccess := returnStatement_cursorMonotoneOnSuccess
    expression expressionCursor
  startsAtCurrentTokenOnSuccess :=
    returnStatement_startsAtCurrentTokenOnSuccess expression
  invariantFree := returnStatement_invariantFreeOnValid expression
    (expressionValid.mono (fun _ _ _ => trivial)) expressionFree
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.SimpleBranchFuelTotalityProperties
/-! Recursive-fuel totality for Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem optionalLetInitializer_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ value next, optionalLetInitializer expression input = .ok value next) ∨
    (∃ failure next,
      optionalLetInitializer expression input = .reject failure next) := by
  by_cases present : isSymbol input .equal
  · rcases (symbol_ordinary .equal .statement) input with
      ⟨equal, afterEqual, equalResult⟩ |
      ⟨failure, rejected, equalResult⟩
    · have equalReply := symbol_validFor .equal .statement input inputValid
      rw [equalResult] at equalReply
      have equalWindow := symbol_preservesTokenWindow .equal .statement input
      rw [equalResult] at equalWindow
      have expressionAdequate : afterEqual.remainingCount < expressionFuel :=
        remainingCount_lt_of_cursor_le equalWindow.2
          (symbol_cursorMonotoneOnSuccess .equal .statement input equal
            afterEqual equalResult) adequate
      rcases contract.ordinary afterEqual equalReply.2.1
          expressionAdequate with
        ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
      · exact Or.inl ⟨some value, next, by
          simp only [optionalLetInitializer, getState, bind, present,
            ↓reduceIte, equalResult, valueResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [optionalLetInitializer, getState, bind, present,
            ↓reduceIte, equalResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalLetInitializer, getState, bind, present,
          ↓reduceIte, equalResult]⟩
  · have absent : isSymbol input .equal = false := by
      cases found : isSymbol input .equal with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalLetInitializer, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalReturnValue_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ value next, optionalReturnValue expression input = .ok value next) ∨
    (∃ failure next,
      optionalReturnValue expression input = .reject failure next) := by
  by_cases empty : isSymbol input .semicolon
  · exact Or.inl ⟨none, input, by
      simp only [optionalReturnValue, getState, bind, empty, ↓reduceIte, pure]⟩
  · have nonempty : isSymbol input .semicolon = false := by
      cases found : isSymbol input .semicolon with
      | false => rfl
      | true => exact False.elim (empty found)
    rcases contract.ordinary input inputValid adequate with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨some value, next, by
        simp only [optionalReturnValue, getState, bind, nonempty,
          Bool.false_eq_true, ↓reduceIte, valueResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalReturnValue, getState, bind, nonempty,
          Bool.false_eq_true, ↓reduceIte, valueResult]⟩

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem letStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ statement next, letStatement expression input = .ok statement next) ∨
    (∃ failure next, letStatement expression input = .reject failure next) := by
  rcases (keyword_ordinary .letKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .letKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .letKw .statement input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate : afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .letKw) .statement
          (· == .keyword .letKw) markerResult) adequate
    rcases (identifier_ordinary .statement) afterMarker with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameReply := identifier_validFor .statement afterMarker
        markerReply.2.1
      rw [nameResult] at nameReply
      have nameWindow := identifier_preservesTokenWindow .statement afterMarker
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < expressionFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (identifier_cursorMonotoneOnSuccess .statement afterMarker name
            afterName nameResult) afterMarkerAdequate
      rcases StatementSimpleInternals.optionalLetType_invariantFreeOnValid
          afterName nameReply.2.1 with
        ⟨type, afterType, typeResult⟩ | ⟨failure, rejected, typeResult⟩
      · have typeReply := StatementSimpleInternals.optionalLetType_validFor
          afterName nameReply.2.1
        rw [typeResult] at typeReply
        have typeWindow :=
          StatementSimpleInternals.optionalLetType_preservesTokenWindow afterName
        rw [typeResult] at typeWindow
        have afterTypeAdequate : afterType.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le typeWindow.2
            (StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
              afterName type afterType typeResult) afterNameAdequate
        rcases StatementSimpleInternals.optionalLetInitializer_ordinary_of_expressionFuel
            expression expressionFuel contract afterType typeReply.2.1
              afterTypeAdequate with
          ⟨initializer, afterInitializer, initializerResult⟩ |
          ⟨failure, rejected, initializerResult⟩
        · have initializerReply :=
            StatementSimpleInternals.optionalLetInitializer_validFor expression
              (fun _ _ => True) contract.validFor afterType typeReply.2.1
          rw [initializerResult] at initializerReply
          rcases (symbol_ordinary .semicolon .statement) afterInitializer with
            ⟨semicolon, final, semicolonResult⟩ |
            ⟨failure, rejected, semicolonResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span semicolon.span
                value := .letDecl name type initializer
              }, final, by
                simp only [letStatement, bind, markerResult, nameResult,
                  typeResult, initializerResult, semicolonResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [letStatement, bind, markerResult, nameResult,
                typeResult, initializerResult, semicolonResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [letStatement, bind, markerResult, nameResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [letStatement, bind, markerResult, nameResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [letStatement, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [letStatement, bind, markerResult]⟩

theorem returnStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ statement next,
      returnStatement expression input = .ok statement next) ∨
    (∃ failure next,
      returnStatement expression input = .reject failure next) := by
  rcases (keyword_ordinary .returnKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .returnKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .returnKw .statement input
    rw [markerResult] at markerWindow
    have valueAdequate : afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .returnKw) .statement
          (· == .keyword .returnKw) markerResult) adequate
    rcases StatementSimpleInternals.optionalReturnValue_ordinary_of_expressionFuel
        expression expressionFuel contract afterMarker markerReply.2.1
          valueAdequate with
      ⟨value, afterValue, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · have valueReply := StatementSimpleInternals.optionalReturnValue_validFor
        expression (fun _ _ => True) contract.validFor afterMarker
          markerReply.2.1
      rw [valueResult] at valueReply
      rcases (symbol_ordinary .semicolon .statement) afterValue with
        ⟨semicolon, final, semicolonResult⟩ |
        ⟨failure, rejected, semicolonResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span semicolon.span
            value := .returnStmt value
          }, final, by
            simp only [returnStatement, bind, markerResult, valueResult,
              semicolonResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [returnStatement, bind, markerResult, valueResult,
            semicolonResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [returnStatement, bind, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [returnStatement, bind, markerResult]⟩

theorem letStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    letStatement expression input ≠ .invariant error := by
  intro failed
  rcases letStatement_ordinary_of_expressionFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem returnStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    returnStatement expression input ≠ .invariant error := by
  intro failed
  rcases returnStatement_ordinary_of_expressionFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem letStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (letStatement expression) (expressionFuel + 1) := {
  validFor := letStatement_validFor expression (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor expressionSyntax.validFor
      expressionSyntax.preservesTokenWindow
        expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := letStatement_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := letStatement_cursorMonotoneOnSuccess expression
    expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    letStatement_startsAtCurrentTokenOnSuccess expression
  ordinary := letStatement_ordinary_of_expressionFuel expression
    expressionFuel totality
}

theorem returnStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (returnStatement expression) (expressionFuel + 1) := {
  validFor := returnStatement_validFor expression (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor expressionSyntax.validFor
      expressionSyntax.preservesTokenWindow
        expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := returnStatement_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := returnStatement_cursorMonotoneOnSuccess expression
    expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    returnStatement_startsAtCurrentTokenOnSuccess expression
  ordinary := returnStatement_ordinary_of_expressionFuel expression
    expressionFuel totality
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ForItemFuelTotalityProperties
/-! Fuel-aware totality for one canonical Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

private theorem bind_cursor_lt_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

theorem forLetItem_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ item next, forLetItem expression input = .ok item next) ∨
    (∃ failure next,
      forLetItem expression input = .reject failure next) := by
  rcases (keyword_ordinary .letKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .letKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .letKw .statement input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate :
        afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .letKw) .statement
          (· == .keyword .letKw) markerResult) adequate
    rcases (identifier_ordinary .statement) afterMarker with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameReply := identifier_validFor .statement afterMarker
        markerReply.2.1
      rw [nameResult] at nameReply
      have nameWindow := identifier_preservesTokenWindow .statement afterMarker
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < expressionFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (identifier_cursorMonotoneOnSuccess .statement afterMarker name
            afterName nameResult) afterMarkerAdequate
      rcases optionalLetType_invariantFreeOnValid afterName nameReply.2.1 with
        ⟨type, afterType, typeResult⟩ | ⟨failure, rejected, typeResult⟩
      · have typeReply := optionalLetType_validFor afterName nameReply.2.1
        rw [typeResult] at typeReply
        have typeWindow := optionalLetType_preservesTokenWindow afterName
        rw [typeResult] at typeWindow
        have afterTypeAdequate :
            afterType.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le typeWindow.2
            (optionalLetType_cursorMonotoneOnSuccess afterName type afterType
              typeResult) afterNameAdequate
        rcases optionalLetInitializer_ordinary_of_expressionFuel expression
            expressionFuel contract afterType typeReply.2.1 afterTypeAdequate
          with ⟨initializer, final, initializerResult⟩ |
            ⟨failure, rejected, initializerResult⟩
        · let endSpan := forLetEnd name type initializer
          exact Or.inl ⟨{
              span := SourceSpan.cover marker.span endSpan
              value := .letDecl name type initializer
            }, final, by
              simp only [forLetItem, bind, markerResult, nameResult,
                typeResult, initializerResult, pure, endSpan]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [forLetItem, bind, markerResult, nameResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [forLetItem, bind, markerResult, nameResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forLetItem, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forLetItem, bind, markerResult]⟩

theorem forAssignmentOrExpression_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ item next,
      forAssignmentOrExpression expression input = .ok item next) ∨
    (∃ failure next,
      forAssignmentOrExpression expression input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, afterLeft, leftResult⟩ | ⟨failure, rejected, leftResult⟩
  · have leftReply := contract.validFor input inputValid
    rw [leftResult] at leftReply
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have tailAdequate : afterLeft.remainingCount < expressionFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    rcases optionalAssignmentTail_ordinary_of_expressionFuel expression
        expressionFuel contract afterLeft leftReply.2.1 tailAdequate with
      ⟨tail, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · cases tail with
      | none =>
          exact Or.inl ⟨{ span := left.span, value := .expression left },
            final, by
              simp only [forAssignmentOrExpression, bind, leftResult,
                tailResult, pure]⟩
      | some tail =>
          cases tail with
          | value operator right =>
              exact Or.inl ⟨{
                  span := SourceSpan.cover left.span right.span
                  value := .assignValue left operator right
                }, final, by
                  simp only [forAssignmentOrExpression, bind, leftResult,
                    tailResult, pure]⟩
          | bitNot operator =>
              exact Or.inl ⟨{
                  span := SourceSpan.cover left.span operator
                  value := .assignBitNot left operator
                }, final, by
                  simp only [forAssignmentOrExpression, bind, leftResult,
                    tailResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forAssignmentOrExpression, bind, leftResult, tailResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forAssignmentOrExpression, bind, leftResult]⟩

theorem forLetItem_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : ForItem}
    (parsed : forLetItem expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forLetItem at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw) result) (parsed := parsed)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalLetType_cursorMonotoneOnSuccess
  intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalLetInitializer_cursorMonotoneOnSuccess expression
      expressionCursor)
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem forAssignmentOrExpression_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : ForItem}
    (parsed : forAssignmentOrExpression expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forAssignmentOrExpression at parsed
  apply bind_cursor_lt_of_first expressionStrict (parsed := parsed)
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalAssignmentTail_cursorMonotoneOnSuccess expression
      (fun _ _ _ result => Nat.le_of_lt (expressionStrict result)))
  intro tail
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail <;> exact Parser.pure_cursorMonotoneOnSuccess _

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ item next, forItem expression input = .ok item next) ∨
    (∃ failure next, forItem expression input = .reject failure next) := by
  unfold forItem
  split
  · exact StatementSimpleInternals.forLetItem_ordinary_of_expressionFuel
      expression expressionFuel contract input inputValid (by omega)
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_ordinary_of_expressionFuel
        expression expressionFuel contract input inputValid adequate

theorem forItem_cursor_lt_onSuccess
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    {input final : State} {value : ForItem}
    (parsed : forItem expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forItem at parsed
  split at parsed
  · exact StatementSimpleInternals.forLetItem_cursor_lt_onSuccess expression
      expressionSyntax.cursorMonotoneOnSuccess parsed
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
        expression expressionSyntax.cursorLtOnSuccess parsed

theorem forItem_fuelElementTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    FuelElementTotalityContract (forItem expression) expressionFuel := {
  validFor := (forItem_validFor expression (Expr.ValidFor statementValid)
    expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
      expressionSyntax.preservesTokenWindow expressionSyntax.cursorLtOnSuccess
        expressionSyntax.startsAtCurrentTokenOnSuccess).mono
          (fun _ _ _ => trivial)
  preservesTokenWindow := forItem_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorLtOnSuccess := forItem_cursor_lt_onSuccess expression expressionSyntax
  ordinary := forItem_ordinary_of_expressionFuel expression expressionFuel
    totality
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ForItemsFuelTotalityProperties
/-! Fuel-aware totality for comma-separated Core `for` header items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/--
Validity, window, monotonicity, and fuel-bounded ordinary control for a
possibly empty `for` item list. No strict field is required for empty lists.
-/
structure ForItemsFuelTotalityContract
    (itemValid : SourceFile → ForItem → Prop)
    (parser : Parser (List ForItem)) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (List.ValidFor itemValid)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ items next, parser input = .ok items next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace ForItemsFuelTotalityContract

theorem ne_invariant
    {itemValid : SourceFile → ForItem → Prop}
    {parser : Parser (List ForItem)} {fuel : Nat}
    (contract : ForItemsFuelTotalityContract itemValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end ForItemsFuelTotalityContract

/--
The loop fuel decreases independently of the fixed fuel required by every
`forItem` invocation.
-/
theorem forItemsTail_ordinary_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel) :
    ∀ loopFuel itemsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < itemFuel →
      (∃ items next,
        forItemsTail expression stop loopFuel itemsRev input =
          .ok items next) ∨
      (∃ failure next,
        forItemsTail expression stop loopFuel itemsRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro itemsRev input inputValid loopAdequate itemAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro itemsRev input inputValid loopAdequate itemAdequate
      unfold forItemsTail
      split
      · cases commaResult : symbol .comma .statement input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .statement input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .statement input
              inputValid
            rw [commaResult] at commaReply
            have commaWindow :=
              symbol_preservesTokenWindow .comma .statement input
            rw [commaResult] at commaWindow
            have commaProgress : input.cursor < afterComma.cursor :=
              acceptToken_cursor_lt_onSuccess (.symbol .comma) .statement
                (· == .symbol .comma) commaResult
            have commaLoopAdequate :
                afterComma.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress commaReply.2.1
                commaWindow.2 commaProgress loopAdequate
            have commaItemAdequate :
                afterComma.remainingCount < itemFuel :=
              remainingCount_lt_of_cursor_le commaWindow.2
                (Nat.le_of_lt commaProgress) itemAdequate
            dsimp only
            split
            · exact Or.inr ⟨{
                  span := afterComma.currentSpan
                  found := afterComma.peekKind?
                  expected := { head := .expression, tail := [] }
                  context := .statement
                }, afterComma, rfl⟩
            · cases itemResult : forItem expression afterComma with
              | invariant error =>
                  exact False.elim (itemContract.ne_invariant afterComma
                    commaReply.2.1 commaItemAdequate error itemResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok item next =>
                  have itemReply := itemContract.validFor afterComma
                    commaReply.2.1
                  rw [itemResult] at itemReply
                  have itemWindow := itemContract.preservesTokenWindow
                    afterComma
                  rw [itemResult] at itemWindow
                  have itemProgress :=
                    itemContract.cursorLtOnSuccess itemResult
                  have nextLoopAdequate :
                      next.remainingCount < loopFuel :=
                    remainingCount_lt_of_cursor_le itemWindow.2
                      (Nat.le_of_lt itemProgress) commaLoopAdequate
                  have nextItemAdequate :
                      next.remainingCount < itemFuel :=
                    remainingCount_lt_of_cursor_le itemWindow.2
                      (Nat.le_of_lt itemProgress) commaItemAdequate
                  dsimp only
                  split
                  · exact inductionHypothesis (item :: itemsRev) next
                      itemReply.2.1 nextLoopAdequate nextItemAdequate
                  · omega
      · exact Or.inl ⟨itemsRev.reverse, input, rfl⟩

theorem forItemsTail_ne_invariant_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (loopFuel : Nat) (itemsRev : List ForItem)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (itemAdequate : input.remainingCount < itemFuel)
    (error : ParserInvariantError) :
    forItemsTail expression stop loopFuel itemsRev input ≠
      .invariant error := by
  intro failed
  rcases forItemsTail_ordinary_of_itemFuel expression stop itemFuel
      itemContract loopFuel itemsRev input inputValid loopAdequate
        itemAdequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- A complete list is ordinary below the fixed item-parser fuel bound. -/
theorem forItems_ordinary_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < itemFuel) :
    (∃ items next, forItems expression stop input = .ok items next) ∨
      (∃ failure next,
        forItems expression stop input = .reject failure next) := by
  unfold forItems
  split
  · exact Or.inl ⟨[], input, rfl⟩
  · cases itemResult : forItem expression input with
    | invariant error =>
        exact False.elim
          (itemContract.ne_invariant input inputValid adequate error itemResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok item next =>
        have itemReply := itemContract.validFor input inputValid
        rw [itemResult] at itemReply
        have itemWindow := itemContract.preservesTokenWindow input
        rw [itemResult] at itemWindow
        have progress := itemContract.cursorLtOnSuccess itemResult
        have nextItemAdequate : next.remainingCount < itemFuel :=
          remainingCount_lt_of_cursor_le itemWindow.2
            (Nat.le_of_lt progress) adequate
        exact forItemsTail_ordinary_of_itemFuel expression stop itemFuel
          itemContract (next.remainingCount + 1) [item] next itemReply.2.1
            (by omega) nextItemAdequate

theorem forItems_ne_invariant_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < itemFuel)
    (error : ParserInvariantError) :
    forItems expression stop input ≠ .invariant error := by
  intro failed
  rcases forItems_ordinary_of_itemFuel expression stop itemFuel itemContract
      input inputValid adequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Build the non-strict list contract from the strict canonical item parser. -/
theorem forItems_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr) (stop : Symbol) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    ForItemsFuelTotalityContract
      (ForItem.ValidFor (Expr.ValidFor statementValid))
      (forItems expression stop) expressionFuel := by
  let itemContract := forItem_fuelElementTotalityContract expression
    expressionFuel expressionSyntax expressionTotality
  exact {
    validFor := forItems_validFor expression stop
      (Expr.ValidFor statementValid)
      (forItem_validFor expression (Expr.ValidFor statementValid)
        expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
          expressionSyntax.preservesTokenWindow
            expressionSyntax.cursorLtOnSuccess
              expressionSyntax.startsAtCurrentTokenOnSuccess)
    preservesTokenWindow := forItems_preservesTokenWindow expression stop
      itemContract.preservesTokenWindow
    cursorMonotoneOnSuccess := forItems_cursorMonotoneOnSuccess expression stop
      expressionSyntax.cursorMonotoneOnSuccess
    ordinary := forItems_ordinary_of_itemFuel expression stop expressionFuel
      itemContract
  }

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchScrutineeTotalityProperties
/-! Totality for the nonempty Core-match scrutinee conversion. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Scrutinee conversion either retains a nonempty list or rejects empty input. -/
theorem requireScrutinees_ordinary (values : DelimitedList Expr) :
    Parser.Ordinary (requireScrutinees values) := by
  intro input
  unfold requireScrutinees
  cases values.elements with
  | nil => exact Or.inr ⟨_, input, rfl⟩
  | cons head tail => exact Or.inl ⟨_, input, rfl⟩

/-- Scrutinee conversion exposes no internal invariant on valid input. -/
theorem requireScrutinees_invariantFreeOnValid
    (values : DelimitedList Expr) :
    Parser.InvariantFreeOnValid (requireScrutinees values) :=
  (requireScrutinees_ordinary values).invariantFreeOnValid

/-- Empty or nonempty scrutinee conversion can never return an invariant. -/
theorem requireScrutinees_ne_invariant (values : DelimitedList Expr)
    (input : State) (error : ParserInvariantError) :
    requireScrutinees values input ≠ .invariant error :=
  (requireScrutinees_ordinary values).ne_invariant input error

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchValidationTotalityProperties
/-! Totality for the diagnostic-only Core-match arity validation pass. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- One arity check either returns directly or emits one diagnostic. -/
theorem validateMatchCaseArity_ordinary
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.Ordinary
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  intro input
  unfold validateMatchCaseArity
  split
  · exact Or.inl ⟨(), input, rfl⟩
  · exact Or.inl ⟨(), input.emit _, rfl⟩

/-- The finite arity-validation pass has no internal failure outcome. -/
theorem validateMatchArities_ordinary (scrutineeCount : Nat) :
    ∀ cases, Parser.Ordinary (validateMatchArities scrutineeCount cases)
  | [] => fun input => Or.inl ⟨(), input, rfl⟩
  | retainedCase :: rest => by
      intro input
      rcases validateMatchCaseArity_ordinary scrutineeCount retainedCase
          input with
        ⟨checked, afterCheck, checkResult⟩ |
        ⟨failure, rejected, checkResult⟩
      · rcases validateMatchArities_ordinary scrutineeCount rest afterCheck with
          ⟨value, final, restResult⟩ |
          ⟨failure, rejected, restResult⟩
        · exact Or.inl ⟨value, final, by
            simp only [validateMatchArities, bind, checkResult, restResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [validateMatchArities, bind, checkResult, restResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [validateMatchArities, bind, checkResult]⟩

theorem validateMatchArities_invariantFreeOnValid
    (scrutineeCount : Nat) (cases : List MatchCase) :
    Parser.InvariantFreeOnValid
      (validateMatchArities scrutineeCount cases) :=
  (validateMatchArities_ordinary scrutineeCount cases).invariantFreeOnValid

theorem validateMatchArities_ne_invariant
    (scrutineeCount : Nat) (cases : List MatchCase)
    (input : State) (error : ParserInvariantError) :
    validateMatchArities scrutineeCount cases input ≠ .invariant error :=
  (validateMatchArities_ordinary scrutineeCount cases).ne_invariant input error

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.BlockTotalityProperties
/-! Valid-input totality for Core block loops and captured blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing a block can only succeed or reject at its closing brace. -/
theorem closeCoreBlock_ne_invariant (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement)
    (input : State) (error : ParserInvariantError) :
    closeCoreBlock opening policy bodyRev input ≠ .invariant error := by
  intro invariantResult
  unfold closeCoreBlock at invariantResult
  simp only [bind] at invariantResult
  cases closingResult : symbol .rightBrace .statement input with
  | ok closing afterClosing =>
      simp [closingResult, modifyState, pure] at invariantResult
  | reject failure rejected =>
      simp [closingResult] at invariantResult
  | invariant closingError =>
      exact (symbol_ne_invariant .rightBrace .statement input closingError)
        closingResult

private theorem symbol_ne_ok_of_atEnd (value : Symbol)
    (context : ParseContext) {input next : State} {token : Token}
    (atEnd : input.atEnd = true)
    (result : symbol value context input = .ok token next) : False := by
  have found := (symbol_ok_state_shape value context result).1
  have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
  have ended : input.window.endIndex <= input.cursor := by
    simpa [State.atEnd] using atEnd
  omega

/--
Adequate token fuel excludes all defensive block-loop invariants. Each
successful statement must preserve the active window and consume a token.
-/
theorem coreBlockItems_ne_invariant_of_remainingCount_lt
    (statement : Parser Statement)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    forall fuel bodyRev input,
      input.ValidFor -> input.remainingCount < fuel ->
      forall error,
        coreBlockItems statement opening policy fuel bodyRev input ≠
          .invariant error := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input inputValid adequate error
      omega
  | succ fuel inductionHypothesis =>
      intro bodyRev input inputValid adequate error invariantResult
      unfold coreBlockItems at invariantResult
      split at invariantResult
      · exact closeCoreBlock_ne_invariant opening policy bodyRev input error
          invariantResult
      · split at invariantResult
        · have atEnd : input.atEnd = true := by assumption
          cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing =>
              exact symbol_ne_ok_of_atEnd .rightBrace .statement atEnd
                closingResult
          | reject failure rejected =>
              simp [closingResult] at invariantResult
          | invariant closingError =>
              exact (symbol_ne_invariant .rightBrace .statement input
                closingError) closingResult
        · cases statementResult : statement input with
          | reject failure rejected =>
              simp [statementResult] at invariantResult
          | invariant statementError =>
              exact statementFree.ne_invariant input inputValid
                statementError statementResult
          | ok value afterStatement =>
              have replyValid := statementValid input inputValid
              rw [statementResult] at replyValid
              have replyWindow := statementWindow input
              rw [statementResult] at replyWindow
              have progress := statementStrict statementResult
              simp only [statementResult] at invariantResult
              split at invariantResult
              · have nextAdequate : afterStatement.remainingCount < fuel :=
                  remainingCount_lt_after_strict_progress replyValid.2.1
                    replyWindow.2 progress adequate
                exact inductionHypothesis (value :: bodyRev) afterStatement
                  replyValid.2.1 nextAdequate error invariantResult
              · omega

/-- A Core block cannot expose loop invariants on valid parser states. -/
theorem coreBlock_ne_invariant (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    coreBlock statement policy input ≠ .invariant error := by
  intro invariantResult
  unfold coreBlock at invariantResult
  cases openingResult : symbol .leftBrace .statement input with
  | reject failure rejected =>
      simp [openingResult] at invariantResult
  | invariant openingError =>
      exact (symbol_ne_invariant .leftBrace .statement input openingError)
        openingResult
  | ok opening afterOpening =>
      have openingReply :=
        symbol_validFor .leftBrace .statement input inputValid
      rw [openingResult] at openingReply
      exact coreBlockItems_ne_invariant_of_remainingCount_lt statement
        statementValid statementWindow statementStrict statementFree opening
          policy (afterOpening.remainingCount + 1) [] afterOpening
          openingReply.2.1 (by omega) error (by
            simpa only [openingResult] using invariantResult)

/-- Valid inputs always receive an ordinary Core-block reply. -/
theorem coreBlock_invariantFreeOnValid (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement) :
    Parser.InvariantFreeOnValid (coreBlock statement policy) :=
  Parser.invariantFreeOnValid_of_ne_invariant
    (coreBlock_ne_invariant statement policy statementValid statementWindow
      statementStrict statementFree)

/-- Isolation preserves invariant freedom, including its recovery path. -/
theorem BlockInternals.isolateBlock_invariantFreeOnValid
    (parser : Parser Block)
    (parserFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (isolateBlock parser) := by
  apply Parser.invariantFreeOnValid_of_ne_invariant
  intro input inputValid error invariantResult
  unfold isolateBlock at invariantResult
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      exact parserFree.ne_invariant input inputValid error (by
        simpa only [captureResult] using invariantResult)
  | some captured =>
      have childValid :=
        (BlockInternals.captureBlock?_validFor inputValid captureResult).entered
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok body childAfter =>
          simp [captureResult, childResult] at invariantResult
      | reject failure childAfter =>
          simp [captureResult, childResult] at invariantResult
      | invariant childError =>
          exact parserFree.ne_invariant _ childValid childError childResult

/-- Isolation is strict when its uncaptured parser is strict. -/
theorem BlockInternals.isolateBlock_cursor_lt_onSuccess
    (parser : Parser Block)
    (parserStrict : forall {input next : State} {body : Block},
      parser input = .ok body next -> input.cursor < next.cursor)
    {input next : State} {body : Block}
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor := by
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      have parserResult : parser input = .ok body next := by
        simpa only [isolateBlock, captureResult] using result
      exact parserStrict parserResult
  | some captured =>
      apply isolateBlock_cursor_lt_onSuccess_of_balancedCapture parser
        (input := input) (next := next) (body := body)
      · simp [hasBalancedBlockCapture, captureResult]
      · exact result

/-- Package the complete Core-block boundary for recursive expression use. -/
theorem isolatedCoreBlock_elementTotalityContract
    (statementValueValid : SourceFile -> Statement -> Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor statementValueValid)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (statementSpan : forall file value,
      statementValueValid file value -> value.span.ValidFor file) :
    ElementTotalityContract
      (isolateBlock (coreBlock statement policy)) := {
  validFor := (isolatedCoreBlock_validFor statementValueValid statement policy
    statementValid statementWindow.preservesTokensOnSuccess statementSpan).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := isolatedCoreBlock_preservesTokenWindow statement
    policy statementWindow
  cursorLtOnSuccess := BlockInternals.isolateBlock_cursor_lt_onSuccess _
    (coreBlock_cursor_lt_onSuccess statement policy)
  invariantFree :=
    (BlockInternals.isolateBlock_invariantFreeOnValid _
      (coreBlock_invariantFreeOnValid statement policy
        (statementValid.mono (fun _ _ _ => trivial)) statementWindow
          statementStrict statementFree)).ne_invariant
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.BlockFuelTotalityProperties
/-! Recursive-fuel totality for Core blocks and isolated Core blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeCoreBlock_ordinary (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser.Ordinary (closeCoreBlock opening policy bodyRev) := by
  intro input
  cases result : closeCoreBlock opening policy bodyRev input with
  | ok body next => exact Or.inl ⟨body, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      exact False.elim
        (closeCoreBlock_ne_invariant opening policy bodyRev input error result)

/--
The block-item loop stays ordinary while both its decreasing loop fuel and
the fixed recursive statement fuel are adequate.
-/
theorem coreBlockItems_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ loopFuel bodyRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel →
      (∃ body final,
        coreBlockItems statement opening policy loopFuel bodyRev input =
          .ok body final) ∨
      (∃ failure final,
        coreBlockItems statement opening policy loopFuel bodyRev input =
          .reject failure final) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      unfold coreBlockItems
      split
      · exact closeCoreBlock_ordinary opening policy bodyRev input
      · split
        · have atEnd : input.atEnd = true := by assumption
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          cases closingResult : symbol .rightBrace .statement input with
          | ok closing next =>
              simp [symbol, acceptToken, peekNone, rejectAt] at closingResult
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | invariant error =>
              exact False.elim
                ((symbol_ordinary .rightBrace .statement).ne_invariant
                  input error closingResult)
        · cases statementResult : statement input with
          | invariant error =>
              exact False.elim
                (contract.ne_invariant input inputValid statementAdequate
                  error statementResult)
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok value next =>
            have replyValid := contract.validFor input inputValid
            rw [statementResult] at replyValid
            have replyWindow := contract.preservesTokenWindow input
            rw [statementResult] at replyWindow
            have progress := statementStrict statementResult
            have nextLoopAdequate : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress replyValid.2.1
                replyWindow.2 progress loopAdequate
            have nextStatementAdequate :
                next.remainingCount < statementFuel :=
              remainingCount_lt_of_cursor_le replyWindow.2
                (Nat.le_of_lt progress) statementAdequate
            dsimp only
            split
            · exact inductionHypothesis (value :: bodyRev) next
                replyValid.2.1 nextLoopAdequate nextStatementAdequate
            · omega

/-- One opening-brace token supplies the extra unit needed by statement fuel. -/
theorem coreBlock_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final, coreBlock statement policy input = .ok body final) ∨
      (∃ failure final,
        coreBlock statement policy input = .reject failure final) := by
  rcases (symbol_ordinary .leftBrace .statement) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .statement input
      inputValid
    rw [openingResult] at openingReply
    have openingWindow :=
      symbol_preservesTokenWindow .leftBrace .statement input
    rw [openingResult] at openingWindow
    have openingProgress : input.cursor < afterOpening.cursor :=
      acceptToken_cursor_lt_onSuccess (.symbol .leftBrace) .statement
        (· == .symbol .leftBrace) openingResult
    have statementAdequate :
        afterOpening.remainingCount < statementFuel :=
      remainingCount_lt_after_strict_progress openingReply.2.1
        openingWindow.2 openingProgress adequate
    simpa only [coreBlock, openingResult] using
      coreBlockItems_ordinary_of_statementFuel statement statementFuel
        contract statementStrict opening policy
          (afterOpening.remainingCount + 1) [] afterOpening openingReply.2.1
          (by omega) statementAdequate
  · exact Or.inr ⟨failure, rejected, by
      simp only [coreBlock, openingResult]⟩

/-- Adequate statement fuel excludes every Core-block invariant. -/
theorem coreBlock_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    coreBlock statement policy input ≠ .invariant error := by
  intro failed
  rcases coreBlock_ordinary_of_statementFuel statement policy statementFuel
      contract statementStrict input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Isolation preserves fuel adequacy because its child window only shrinks. -/
theorem isolatedCoreBlock_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final,
      isolateBlock (coreBlock statement policy) input = .ok body final) ∨
    (∃ failure final,
      isolateBlock (coreBlock statement policy) input =
        .reject failure final) := by
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simpa only [isolateBlock, captureResult] using
        coreBlock_ordinary_of_statementFuel statement policy statementFuel
          contract statementStrict input inputValid adequate
  | some captured =>
      have capturedValid :=
        BlockInternals.captureBlock?_validFor inputValid captureResult
      let child := input.enterWindow input.cursor captured.window
      have childAdequate : child.remainingCount < statementFuel + 1 := by
        simp only [child, State.remainingCount, State.enterWindow]
        have endLe := capturedValid.endIndex_le_window
        simp only [State.remainingCount] at adequate
        omega
      rcases coreBlock_ordinary_of_statementFuel statement policy
          statementFuel contract statementStrict child capturedValid.entered
            childAdequate with
        ⟨body, childAfter, childResult⟩ |
        ⟨failure, childAfter, childResult⟩
      · exact Or.inl ⟨body,
          State.mergeDiagnostics
            ({ input with cursor := captured.window.endIndex }) childAfter, by
          simp only [isolateBlock, captureResult, childResult, child]⟩
      · exact Or.inl ⟨{ span := captured.span, value := [] },
          State.emit (State.mergeDiagnostics
            ({ input with cursor := captured.window.endIndex }) childAfter)
              failure.toDiagnostic, by
          simp only [isolateBlock, captureResult, childResult, child]⟩

/-- Adequate statement fuel also excludes isolated-block invariants. -/
theorem isolatedCoreBlock_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    isolateBlock (coreBlock statement policy) input ≠ .invariant error := by
  intro failed
  rcases isolatedCoreBlock_ordinary_of_statementFuel statement policy
      statementFuel contract statementStrict input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package a recursive-fuel Core block for expression-layer recursion. -/
theorem coreBlock_fuelTotalityContract
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (statementSpan : ∀ file value,
      statementValueValid file value → value.span.ValidFor file) :
    FuelElementTotalityContract
      (coreBlock statement policy) (statementFuel + 1) := {
  validFor := (coreBlock_validFor statementValueValid statement policy
    contract.validFor contract.preservesTokenWindow.preservesTokensOnSuccess
      statementSpan).mono (fun _ _ _ => trivial)
  preservesTokenWindow := coreBlock_preservesTokenWindow statement policy
    contract.preservesTokenWindow
  cursorLtOnSuccess := coreBlock_cursor_lt_onSuccess statement policy
  ordinary := coreBlock_ordinary_of_statementFuel statement policy
    statementFuel contract statementStrict
}

/-- Package the derive-safe captured Core block at the same recursive fuel. -/
theorem isolatedCoreBlock_fuelTotalityContract
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (statementSpan : ∀ file value,
      statementValueValid file value → value.span.ValidFor file) :
    FuelElementTotalityContract
      (isolateBlock (coreBlock statement policy)) (statementFuel + 1) := {
  validFor := (isolatedCoreBlock_validFor statementValueValid statement policy
    contract.validFor contract.preservesTokenWindow.preservesTokensOnSuccess
      statementSpan).mono (fun _ _ _ => trivial)
  preservesTokenWindow := isolatedCoreBlock_preservesTokenWindow statement
    policy contract.preservesTokenWindow
  cursorLtOnSuccess := BlockInternals.isolateBlock_cursor_lt_onSuccess _
    (coreBlock_cursor_lt_onSuccess statement policy)
  ordinary := isolatedCoreBlock_ordinary_of_statementFuel statement policy
    statementFuel contract statementStrict
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchDefaultFuelTotalityProperties
/-! Fuel-aware totality for the optional Core-match `default` body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
A present `default` spends one keyword token before entering its recursive
block; an absent default succeeds without consuming input.
-/
theorem optionalDefaultBody_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ body next, optionalDefaultBody statement input = .ok body next) ∨
      (∃ failure next,
        optionalDefaultBody statement input = .reject failure next) := by
  unfold optionalDefaultBody
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .defaultKw .statement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .defaultKw .statement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow := keyword_preservesTokenWindow .defaultKw
        .statement input
      rw [markerResult] at markerWindow
      have bodyBudget :
          afterMarker.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress markerReply.2.1
          markerWindow.2
          (acceptToken_cursor_lt_onSuccess (.keyword .defaultKw)
            .statement (· == .keyword .defaultKw) markerResult)
          adequate
      rcases coreBlock_ordinary_of_statementFuel statement .require
          statementFuel statementContract statementStrict afterMarker
            markerReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ |
        ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

/-- Adequate recursive-statement fuel excludes every helper invariant. -/
theorem optionalDefaultBody_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    optionalDefaultBody statement input ≠ .invariant error := by
  intro failed
  rcases optionalDefaultBody_ordinary_of_statementFuel statement
      statementFuel statementContract statementStrict input inputValid
        adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ControlBlockFuelTotalityProperties
/-! Fuel-aware totality for braced and `while` Core statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A braced statement has the same ordinary outcomes as its Core block. -/
theorem blockStatement_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ value next, blockStatement statement input = .ok value next) ∨
      (∃ failure next,
        blockStatement statement input = .reject failure next) := by
  rcases coreBlock_ordinary_of_statementFuel statement .require statementFuel
      contract statementStrict input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := body.span, value := .block body.value }, next, by
      simp only [blockStatement, bind, result, pure]⟩
  · exact Or.inr ⟨failure, next, by
      simp only [blockStatement, bind, result]⟩

/-- Adequate recursive statement fuel excludes block-wrapper invariants. -/
theorem blockStatement_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    blockStatement statement input ≠ .invariant error := by
  intro failed
  rcases blockStatement_ordinary_of_statementFuel statement statementFuel
      contract statementStrict input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package a braced statement at one unit above recursive statement fuel. -/
theorem blockStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (blockStatement statement) (statementFuel + 1) := {
  validFor := blockStatement_validFor statement (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor contract.validFor
      contract.preservesTokenWindow.preservesTokensOnSuccess
  preservesTokenWindow := blockStatement_preservesTokenWindow statement
    contract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    blockStatement_cursorMonotoneOnSuccess statement
  startsAtCurrentTokenOnSuccess :=
    blockStatement_startsAtCurrentTokenOnSuccess statement
  ordinary := blockStatement_ordinary_of_statementFuel statement statementFuel
    contract statementStrict
}

/--
`while` needs two leading tokens before its expression and four strict prefix
steps before the recursive block. The smaller adequate budget serves both.
-/
theorem whileStatement_ordinary_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5)) :
    (∃ value next,
      whileStatement statement expression input = .ok value next) ∨
    (∃ failure next,
      whileStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 5))
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 5))
  rcases (contextual_ordinary .while .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := contextual_validFor .while .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := contextual_preservesTokenWindow .while .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.contextual .while) .statement
        (·.isContextual .while) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 4 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    rcases (symbol_ordinary .leftParen .statement) afterMarker with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .statement afterMarker
      rw [openingResult] at openingWindow
      have openingProgress : afterMarker.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .statement
          (· == .symbol .leftParen) openingResult
      have expressionAdequate :
          afterOpening.remainingCount < expressionFuel :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      have statementAfterOpening :
          afterOpening.remainingCount < statementFuel + 3 :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      rcases expressionContract.ordinary afterOpening openingReply.2.1
          expressionAdequate with
        ⟨condition, afterCondition, conditionResult⟩ |
        ⟨failure, rejected, conditionResult⟩
      · have conditionReply := expressionContract.validFor afterOpening
          openingReply.2.1
        rw [conditionResult] at conditionReply
        have conditionWindow := expressionContract.preservesTokenWindow
          afterOpening
        rw [conditionResult] at conditionWindow
        have conditionProgress :=
          expressionContract.cursorLtOnSuccess conditionResult
        have statementAfterCondition :
            afterCondition.remainingCount < statementFuel + 2 :=
          remainingCount_lt_after_strict_progress conditionReply.2.1
            conditionWindow.2 conditionProgress (by omega)
        rcases (symbol_ordinary .rightParen .statement) afterCondition with
          ⟨closing, afterClosing, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · have closingReply := symbol_validFor .rightParen .statement
            afterCondition conditionReply.2.1
          rw [closingResult] at closingReply
          have closingWindow :=
            symbol_preservesTokenWindow .rightParen .statement afterCondition
          rw [closingResult] at closingWindow
          have closingProgress : afterCondition.cursor < afterClosing.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .rightParen) .statement
              (· == .symbol .rightParen) closingResult
          have blockAdequate :
              afterClosing.remainingCount < statementFuel + 1 :=
            remainingCount_lt_after_strict_progress closingReply.2.1
              closingWindow.2 closingProgress (by omega)
          rcases coreBlock_ordinary_of_statementFuel statement .require
              statementFuel statementContract statementStrict afterClosing
                closingReply.2.1 blockAdequate with
            ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .whileLoop condition body
              }, final, by
                simp only [whileStatement, bind, markerResult, openingResult,
                  conditionResult, closingResult, bodyResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [whileStatement, bind, markerResult, openingResult,
                conditionResult, closingResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [whileStatement, bind, markerResult, openingResult,
              conditionResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [whileStatement, bind, markerResult, openingResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [whileStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [whileStatement, bind, markerResult]⟩

/-- Adequacy for both recursive parsers excludes every `while` invariant. -/
theorem whileStatement_ne_invariant_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5))
    (error : ParserInvariantError) :
    whileStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases whileStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel statementContract statementStrict expressionContract
        input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package canonical `while` syntax under both recursive fuel bounds. -/
theorem whileStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (whileStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 5)) := {
  validFor := whileStatement_validFor (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor statement expression
      statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      expressionSyntax.validFor expressionSyntax.preservesTokensOnSuccess
      expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := whileStatement_preservesTokenWindow statement
    expression statementContract.preservesTokenWindow
      expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := whileStatement_cursorMonotoneOnSuccess statement
    expression expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    whileStatement_startsAtCurrentTokenOnSuccess statement expression
  ordinary := whileStatement_ordinary_of_fuels statement expression
    statementFuel expressionFuel statementContract statementStrict
      expressionTotality
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ControlIfFuelTotalityProperties
/-! Fuel-aware totality for Core `if` statements and optional `else` bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ControlInternals

/-- Optional `else` parsing reuses the already fuel-bounded Core block. -/
theorem optionalElseBody_ordinary_of_blockFuel
    (statement : Parser Statement) (statementFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body next, optionalElseBody statement input = .ok body next) ∨
      (∃ failure next,
        optionalElseBody statement input = .reject failure next) := by
  unfold optionalElseBody
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .elseKw .statement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .elseKw .statement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow :=
        keyword_preservesTokenWindow .elseKw .statement input
      rw [markerResult] at markerWindow
      have bodyAdequate :
          afterMarker.remainingCount < statementFuel + 1 := by
        have spent : afterMarker.remainingCount < statementFuel :=
          remainingCount_lt_after_strict_progress markerReply.2.1
            markerWindow.2
            (acceptToken_cursor_lt_onSuccess (.keyword .elseKw) .statement
              (· == .keyword .elseKw) markerResult) adequate
        omega
      rcases blockContract.ordinary afterMarker markerReply.2.1 bodyAdequate
          with ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

end ControlInternals

/--
The same prefix budget used by `while` reaches the condition and then block;
strict then-block progress leaves enough fuel for a present `else` block.
-/
theorem ifStatement_ordinary_of_fuels
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5)) :
    (∃ value next, ifStatement statement expression input = .ok value next) ∨
      (∃ failure next,
        ifStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 5))
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 5))
  rcases (keyword_ordinary .ifKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .ifKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .ifKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .statement
        (· == .keyword .ifKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 4 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    rcases (symbol_ordinary .leftParen .statement) afterMarker with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .statement afterMarker
      rw [openingResult] at openingWindow
      have openingProgress : afterMarker.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .statement
          (· == .symbol .leftParen) openingResult
      have expressionAdequate :
          afterOpening.remainingCount < expressionFuel :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      have statementAfterOpening :
          afterOpening.remainingCount < statementFuel + 3 :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      rcases expressionContract.ordinary afterOpening openingReply.2.1
          expressionAdequate with
        ⟨condition, afterCondition, conditionResult⟩ |
        ⟨failure, rejected, conditionResult⟩
      · have conditionReply := expressionContract.validFor afterOpening
          openingReply.2.1
        rw [conditionResult] at conditionReply
        have conditionWindow := expressionContract.preservesTokenWindow
          afterOpening
        rw [conditionResult] at conditionWindow
        have conditionProgress :=
          expressionContract.cursorLtOnSuccess conditionResult
        have statementAfterCondition :
            afterCondition.remainingCount < statementFuel + 2 :=
          remainingCount_lt_after_strict_progress conditionReply.2.1
            conditionWindow.2 conditionProgress (by omega)
        rcases (symbol_ordinary .rightParen .statement) afterCondition with
          ⟨closing, afterClosing, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · have closingReply := symbol_validFor .rightParen .statement
            afterCondition conditionReply.2.1
          rw [closingResult] at closingReply
          have closingWindow :=
            symbol_preservesTokenWindow .rightParen .statement afterCondition
          rw [closingResult] at closingWindow
          have closingProgress : afterCondition.cursor < afterClosing.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .rightParen) .statement
              (· == .symbol .rightParen) closingResult
          have blockAdequate :
              afterClosing.remainingCount < statementFuel + 1 :=
            remainingCount_lt_after_strict_progress closingReply.2.1
              closingWindow.2 closingProgress (by omega)
          rcases blockContract.ordinary afterClosing closingReply.2.1
              blockAdequate with
            ⟨thenBody, afterThen, thenResult⟩ |
            ⟨failure, rejected, thenResult⟩
          · have thenReply := blockContract.validFor afterClosing
              closingReply.2.1
            rw [thenResult] at thenReply
            have thenWindow := blockContract.preservesTokenWindow afterClosing
            rw [thenResult] at thenWindow
            have thenProgress := blockContract.cursorLtOnSuccess thenResult
            have elseAdequate :
                afterThen.remainingCount < statementFuel + 1 := by
              have spent : afterThen.remainingCount < statementFuel :=
                remainingCount_lt_after_strict_progress thenReply.2.1
                  thenWindow.2 thenProgress blockAdequate
              omega
            rcases ControlInternals.optionalElseBody_ordinary_of_blockFuel
                statement statementFuel blockContract afterThen thenReply.2.1
                  elseAdequate with
              ⟨elseBody, final, elseResult⟩ |
              ⟨failure, rejected, elseResult⟩
            · let endSpan := elseBody.map (fun body => body.span)
                  |>.getD thenBody.span
              exact Or.inl ⟨{
                  span := SourceSpan.cover marker.span endSpan
                  value := .ifThen condition thenBody elseBody
                }, final, by
                  simp only [ifStatement, bind, markerResult, openingResult,
                    conditionResult, closingResult, thenResult, elseResult,
                    pure, endSpan]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [ifStatement, bind, markerResult, openingResult,
                  conditionResult, closingResult, thenResult, elseResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [ifStatement, bind, markerResult, openingResult,
                conditionResult, closingResult, thenResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [ifStatement, bind, markerResult, openingResult,
              conditionResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [ifStatement, bind, markerResult, openingResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [ifStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [ifStatement, bind, markerResult]⟩

/-- Adequate expression and recursive statement fuel exclude invariants. -/
theorem ifStatement_ne_invariant_of_fuels
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5))
    (error : ParserInvariantError) :
    ifStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases ifStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel blockContract expressionContract input inputValid
        adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package canonical `if` syntax under both recursive fuel bounds. -/
theorem ifStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (ifStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 5)) := by
  let blockContract := coreBlock_fuelTotalityContract statement .require
    statementFuel statementContract statementStrict
      (fun _ _ valid => valid.span_valid)
  exact {
    validFor := ifStatement_validFor (Expr.ValidFor statementValid)
      patternValueValid YulStmt.ValidFor statement expression
        statementContract.validFor
        statementContract.preservesTokenWindow.preservesTokensOnSuccess
        expressionSyntax.validFor expressionSyntax.preservesTokensOnSuccess
        expressionSyntax.cursorMonotoneOnSuccess
    preservesTokenWindow := ifStatement_preservesTokenWindow statement
      expression statementContract.preservesTokenWindow
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess := ifStatement_cursorMonotoneOnSuccess statement
      expression expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      ifStatement_startsAtCurrentTokenOnSuccess statement expression
    ordinary := ifStatement_ordinary_of_fuels statement expression
      statementFuel expressionFuel blockContract expressionTotality
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchCaseFuelTotalityProperties
/-! Fuel-aware totality for one canonical Core `case` arm. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
One `case` marker reaches its pattern after one strict token step; a successful
pattern supplies the second strict step needed to enter the recursive block.
-/
theorem matchCase_ordinary_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (patternFuel + 1) (statementFuel + 3)) :
    (∃ value next, matchCase statement patternParser input = .ok value next) ∨
      (∃ failure next,
        matchCase statement patternParser input = .reject failure next) := by
  have patternBudget : input.remainingCount < patternFuel + 1 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (patternFuel + 1) (statementFuel + 3))
  have statementBudget : input.remainingCount < statementFuel + 3 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (patternFuel + 1) (statementFuel + 3))
  rcases (keyword_ordinary .caseKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .caseKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow :=
      keyword_preservesTokenWindow .caseKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .statement
        (· == .keyword .caseKw) markerResult
    have patternAdequate : afterMarker.remainingCount < patternFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1
        markerWindow.2 markerProgress patternBudget
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1
        markerWindow.2 markerProgress statementBudget
    rcases patternContract.ordinary afterMarker markerReply.2.1
        patternAdequate with
      ⟨retainedPattern, afterPattern, patternResult⟩ |
      ⟨failure, rejected, patternResult⟩
    · have patternReply := patternContract.validFor afterMarker
        markerReply.2.1
      rw [patternResult] at patternReply
      have patternWindow := patternContract.preservesTokenWindow afterMarker
      rw [patternResult] at patternWindow
      have bodyAdequate :
          afterPattern.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress patternReply.2.1
          patternWindow.2
          (patternContract.cursorLtOnSuccess patternResult)
          statementAfterMarker
      rcases coreBlock_ordinary_of_statementFuel statement .require
          statementFuel statementContract statementStrict afterPattern
            patternReply.2.1 bodyAdequate with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := { pattern := retainedPattern, body }
          }, final, by
            simp only [matchCase, bind, markerResult, patternResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [matchCase, bind, markerResult, patternResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [matchCase, bind, markerResult, patternResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [matchCase, bind, markerResult]⟩

/-- Adequate pattern and recursive-statement fuels exclude every invariant. -/
theorem matchCase_ne_invariant_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (patternFuel + 1) (statementFuel + 3))
    (error : ParserInvariantError) :
    matchCase statement patternParser input ≠ .invariant error := by
  intro failed
  rcases matchCase_ordinary_of_fuels statement patternParser statementFuel
      patternFuel statementContract statementStrict patternContract input
        inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful `case` strictly consumes its leading marker. -/
theorem matchCase_cursor_lt_onSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser)
    {input final : State} {value : MatchCase}
    (parsed : matchCase statement patternParser input = .ok value final) :
    input.cursor < final.cursor := by
  unfold matchCase at parsed
  cases markerResult : keyword .caseKw .statement input with
  | reject failure rejected => simp [bind, markerResult] at parsed
  | invariant error => simp [bind, markerResult] at parsed
  | ok marker afterMarker =>
      simp only [bind, markerResult] at parsed
      cases patternResult : patternParser afterMarker with
      | reject failure rejected => simp [patternResult] at parsed
      | invariant error => simp [patternResult] at parsed
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at parsed
          cases bodyResult : coreBlock statement .require afterPattern with
          | reject failure rejected => simp [bodyResult] at parsed
          | invariant error => simp [bodyResult] at parsed
          | ok body afterBody =>
              simp only [bodyResult, pure] at parsed
              have progress : input.cursor < afterBody.cursor :=
                Nat.lt_of_lt_of_le
                  (acceptToken_cursor_lt_onSuccess (.keyword .caseKw)
                    .statement (· == .keyword .caseKw) markerResult)
                  (Nat.le_trans
                    (patternCursor afterMarker retainedPattern afterPattern
                      patternResult)
                    (coreBlock_cursorMonotoneOnSuccess statement .require
                      afterPattern body afterBody bodyResult))
              cases parsed
              exact progress

/-- Package one Core case arm under its two independent recursive bounds. -/
theorem matchCase_fuelElementTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel) :
    FuelElementTotalityContract (matchCase statement patternParser)
      (Nat.min (patternFuel + 1) (statementFuel + 3)) := {
  validFor := (matchCase_validFor expressionValueValid patternValueValid
    yulValueValid statement patternParser statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      patternValid
      patternContract.preservesTokenWindow.preservesTokensOnSuccess
      (fun {_input _value _next} parsed =>
        Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))).mono
          (fun _ _ _ => trivial)
  preservesTokenWindow := matchCase_preservesTokenWindow statement
    patternParser statementContract.preservesTokenWindow
      patternContract.preservesTokenWindow
  cursorLtOnSuccess := matchCase_cursor_lt_onSuccess statement patternParser
    (fun {_input _value _next} parsed =>
      Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))
  ordinary := matchCase_ordinary_of_fuels statement patternParser
    statementFuel patternFuel statementContract statementStrict
      patternContract
}

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchCasesFuelTotalityProperties
/-! Fuel-aware totality for canonical Core match-case iteration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
Fuel-bounded totality for a case-list parser which may succeed without
consuming when no `case` marker is present.
-/
structure FuelCaseListTotalityContract
    (caseValid : SourceFile → MatchCase → Prop)
    (parser : Parser (List MatchCase)) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (List.ValidFor caseValid)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelCaseListTotalityContract

/-- Adequate arm fuel excludes every invariant from a packaged case list. -/
theorem ne_invariant
    {caseValid : SourceFile → MatchCase → Prop}
    {parser : Parser (List MatchCase)} {fuel : Nat}
    (contract : FuelCaseListTotalityContract caseValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelCaseListTotalityContract

/-- Loop fuel and recursive arm fuel remain independent during iteration. -/
theorem matchCases_ordinary_of_fuels
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseFuel : Nat)
    (caseContract : FuelElementTotalityContract
      (matchCase statement patternParser) caseFuel) :
    ∀ loopFuel casesRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < caseFuel →
      (∃ cases next,
        matchCases statement patternParser loopFuel casesRev input =
          .ok cases next) ∨
      (∃ failure next,
        matchCases statement patternParser loopFuel casesRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intros; omega
  | succ loopFuel inductionHypothesis =>
      intro casesRev input inputValid loopAdequate caseAdequate
      unfold matchCases
      split
      · cases caseResult : matchCase statement patternParser input with
        | invariant error =>
            exact False.elim (caseContract.ne_invariant input inputValid
              caseAdequate error caseResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok retainedCase next =>
            have caseReply := caseContract.validFor input inputValid
            rw [caseResult] at caseReply
            have caseWindow := caseContract.preservesTokenWindow input
            rw [caseResult] at caseWindow
            have progress := caseContract.cursorLtOnSuccess caseResult
            have nextLoop : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress caseReply.2.1
                caseWindow.2 progress loopAdequate
            have nextCase : next.remainingCount < caseFuel :=
              remainingCount_lt_of_cursor_le caseWindow.2
                (Nat.le_of_lt progress) caseAdequate
            change
              (∃ cases final,
                (if next.cursor > input.cursor then
                  matchCases statement patternParser loopFuel
                    (retainedCase :: casesRev) next
                else
                  .invariant (.noProgress .statement next.currentSpan)) =
                    .ok cases final) ∨
              (∃ failure final,
                (if next.cursor > input.cursor then
                  matchCases statement patternParser loopFuel
                    (retainedCase :: casesRev) next
                else
                  .invariant (.noProgress .statement next.currentSpan)) =
                    .reject failure final)
            rw [if_pos progress]
            exact inductionHypothesis (retainedCase :: casesRev) next
              caseReply.2.1 nextLoop nextCase
      · exact Or.inl ⟨casesRev.reverse, input, rfl⟩

/-- Adequate loop and arm fuels rule out every case-list invariant. -/
theorem matchCases_ne_invariant_of_fuels
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseFuel loopFuel : Nat)
    (caseContract : FuelElementTotalityContract
      (matchCase statement patternParser) caseFuel)
    (casesRev : List MatchCase) (input : State)
    (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (caseAdequate : input.remainingCount < caseFuel)
    (error : ParserInvariantError) :
    matchCases statement patternParser loopFuel casesRev input ≠
      .invariant error := by
  intro failed
  rcases matchCases_ordinary_of_fuels statement patternParser caseFuel
      caseContract loopFuel casesRev input inputValid loopAdequate
        caseAdequate with
    ⟨cases, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
Package the production wrapper whose loop fuel is chosen dynamically from the
current token window while recursive arm fuel remains an explicit bound.
-/
theorem matchCases_production_fuelTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel) :
    FuelCaseListTotalityContract
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid)
      (fun input => matchCases statement patternParser
        (input.remainingCount + 1) [] input)
      (Nat.min (patternFuel + 1) (statementFuel + 3)) := by
  let caseContract := matchCase_fuelElementTotalityContract
    expressionValueValid patternValueValid yulValueValid statement
      patternParser statementFuel patternFuel statementContract
      statementStrict patternValid patternContract
  let caseValid := matchCase_validFor expressionValueValid patternValueValid
    yulValueValid statement patternParser statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      patternValid
      patternContract.preservesTokenWindow.preservesTokensOnSuccess
      (fun {_input _value _next} parsed =>
        Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))
  exact {
    validFor := fun input inputValid =>
      matchCases_validFor expressionValueValid patternValueValid
        yulValueValid statement patternParser caseValid
          (input.remainingCount + 1) [] input inputValid (by
            intro item member
            simp at member)
    preservesTokenWindow := fun input =>
      matchCases_preservesTokenWindow statement patternParser
        caseContract.preservesTokenWindow (input.remainingCount + 1) [] input
    cursorMonotoneOnSuccess := fun input value next result =>
      matchCases_cursorMonotoneOnSuccess statement patternParser
        (input.remainingCount + 1) [] input value next result
    ordinary := fun input inputValid adequate =>
      matchCases_ordinary_of_fuels statement patternParser
        (Nat.min (patternFuel + 1) (statementFuel + 3)) caseContract
        (input.remainingCount + 1) [] input inputValid (by omega) adequate
  }

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchStatementFuelTotalityProperties
/-! Fuel-aware ordinary control for a complete Core `match` statement. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace MatchInternals

/-- The outer budget shared by scrutinees, case arms, and default bodies. -/
def matchStatementFuel (expressionFuel caseFuel statementFuel : Nat) : Nat :=
  Nat.min (expressionFuel + 2)
    (Nat.min (caseFuel + 3) (statementFuel + 5))

private def finishMatchStatement (marker : Token)
    (scrutinees : NonemptyDelimitedList Expr) (opening : Token)
    (cases : List MatchCase) (defaultBody : Option Block)
    (closing : Token) : Parser Statement := do
  let armsSpan := SourceSpan.cover opening.span closing.span
  let _ ← validateMatchArities scrutinees.elements.toList.length cases
  if cases.isEmpty && defaultBody.isNone then
    let _ ← emitDiagnostic {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
  else
    pure ()
  pure {
    span := SourceSpan.cover marker.span closing.span
    value := .matchWith scrutinees {
      span := armsSpan
      value := { cases, defaultBody }
    }
  }

private theorem finishMatchStatement_ordinary (marker : Token)
    (scrutinees : NonemptyDelimitedList Expr) (opening : Token)
    (cases : List MatchCase) (defaultBody : Option Block)
    (closing : Token) :
    Parser.Ordinary
      (finishMatchStatement marker scrutinees opening cases defaultBody
        closing) := by
  intro input
  rcases validateMatchArities_ordinary scrutinees.elements.toList.length
      cases input with
    ⟨validated, afterValidation, validationResult⟩ |
    ⟨failure, rejected, validationResult⟩
  · cases validated
    let diagnostic : ParseDiagnostic := {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
    let retained : Statement := {
      span := SourceSpan.cover marker.span closing.span
      value := .matchWith scrutinees {
        span := SourceSpan.cover opening.span closing.span
        value := { cases, defaultBody }
      }
    }
    by_cases missing : cases.isEmpty && defaultBody.isNone
    · exact Or.inl ⟨retained, afterValidation.emit diagnostic, by
        unfold finishMatchStatement
        simp only [bind, validationResult]
        simp [missing, emitDiagnostic, modifyState, pure, diagnostic,
          retained]⟩
    · exact Or.inl ⟨retained, afterValidation, by
        unfold finishMatchStatement
        simp only [bind, validationResult]
        simp [missing, pure, retained]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [finishMatchStatement, bind, validationResult]⟩

end MatchInternals

/--
The complete match parser is ordinary below independent expression, case-arm,
and recursive-statement bounds.
-/
theorem matchStatement_ordinary_of_fuels
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    {caseValueValid : SourceFile → MatchCase → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel caseFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract : FuelElementTotalityContract
      expression expressionFuel)
    (caseContract : MatchInternals.FuelCaseListTotalityContract caseValueValid
      (fun input => MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) caseFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      MatchInternals.matchStatementFuel expressionFuel caseFuel
        statementFuel) :
    (∃ value next,
      matchStatement statement expression pattern input = .ok value next) ∨
    (∃ failure next,
      matchStatement statement expression pattern input =
        .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_left _ _)
  have tailBudget := Nat.lt_of_lt_of_le adequate (Nat.min_le_right _ _)
  have caseBudget : input.remainingCount < caseFuel + 3 :=
    Nat.lt_of_lt_of_le tailBudget (Nat.min_le_left _ _)
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le tailBudget (Nat.min_le_right _ _)
  rcases (keyword_ordinary .matchKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .matchKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .matchKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress := acceptToken_cursor_lt_onSuccess
      (.keyword .matchKw) .statement (· == .keyword .matchKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress expressionBudget
    have caseAfterMarker : afterMarker.remainingCount < caseFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress caseBudget
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 4 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress statementBudget
    rcases delimited_ordinary_of_elementFuel .leftParen .rightParen false
        expression .expression .statement expressionFuel expressionContract
          afterMarker markerReply.2.1 expressionAfterMarker with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · have valuesReply := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen false expression .expression .statement
          expressionContract.validFor
          expressionContract.preservesTokenWindow.preservesTokensOnSuccess
          afterMarker markerReply.2.1
      rw [valuesResult] at valuesReply
      have valuesWindow := delimited_preservesTokenWindow .leftParen
        .rightParen false expression .expression .statement
          expressionContract.preservesTokenWindow afterMarker
      rw [valuesResult] at valuesWindow
      have valuesProgress := delimitedWithPolicy_cursor_lt_onSuccess
        .leftParen .rightParen false true expression .expression .statement
          valuesResult
      have caseAfterValues : afterValues.remainingCount < caseFuel + 1 :=
        remainingCount_lt_after_strict_progress valuesReply.2.1
          valuesWindow.2 valuesProgress caseAfterMarker
      have statementAfterValues :
          afterValues.remainingCount < statementFuel + 3 :=
        remainingCount_lt_after_strict_progress valuesReply.2.1
          valuesWindow.2 valuesProgress statementAfterMarker
      rcases MatchInternals.requireScrutinees_ordinary values afterValues with
        ⟨scrutinees, afterScrutinees, requiredResult⟩ |
        ⟨failure, rejected, requiredResult⟩
      · have requiredReply := MatchInternals.requireScrutinees_validFor
          (fun _ _ => True) values afterValues valuesReply.2.1 (by
            simpa [valuesReply.2.2] using valuesReply.1)
        rw [requiredResult] at requiredReply
        have requiredWindow :=
          MatchInternals.requireScrutinees_preservesTokenWindow values
            afterValues
        rw [requiredResult] at requiredWindow
        have requiredCursor :=
          MatchInternals.requireScrutinees_cursorMonotoneOnSuccess values
            afterValues scrutinees afterScrutinees requiredResult
        have caseAfterRequired :
            afterScrutinees.remainingCount < caseFuel + 1 :=
          remainingCount_lt_of_cursor_le requiredWindow.2 requiredCursor
            caseAfterValues
        have statementAfterRequired :
            afterScrutinees.remainingCount < statementFuel + 3 :=
          remainingCount_lt_of_cursor_le requiredWindow.2 requiredCursor
            statementAfterValues
        rcases (symbol_ordinary .leftBrace .statement) afterScrutinees with
          ⟨opening, afterOpening, openingResult⟩ |
          ⟨failure, rejected, openingResult⟩
        · have openingReply := symbol_validFor .leftBrace .statement
            afterScrutinees requiredReply.2.1
          rw [openingResult] at openingReply
          have openingWindow := symbol_preservesTokenWindow .leftBrace
            .statement afterScrutinees
          rw [openingResult] at openingWindow
          have openingProgress := acceptToken_cursor_lt_onSuccess
            (.symbol .leftBrace) .statement (· == .symbol .leftBrace)
              openingResult
          have casesAdequate : afterOpening.remainingCount < caseFuel :=
            remainingCount_lt_after_strict_progress openingReply.2.1
              openingWindow.2 openingProgress caseAfterRequired
          have statementAfterOpening :
              afterOpening.remainingCount < statementFuel + 2 :=
            remainingCount_lt_after_strict_progress openingReply.2.1
              openingWindow.2 openingProgress statementAfterRequired
          rcases caseContract.ordinary afterOpening openingReply.2.1
              casesAdequate with
            ⟨cases, afterCases, casesResult⟩ |
            ⟨failure, rejected, casesResult⟩
          · have casesReply := caseContract.validFor afterOpening
              openingReply.2.1
            rw [casesResult] at casesReply
            have casesWindow := caseContract.preservesTokenWindow afterOpening
            rw [casesResult] at casesWindow
            have casesCursor := caseContract.cursorMonotoneOnSuccess
              afterOpening cases afterCases casesResult
            have defaultAdequate :
                afterCases.remainingCount < statementFuel + 2 :=
              remainingCount_lt_of_cursor_le casesWindow.2 casesCursor
                statementAfterOpening
            rcases MatchInternals.optionalDefaultBody_ordinary_of_statementFuel
                statement statementFuel statementContract statementStrict
                  afterCases casesReply.2.1 defaultAdequate with
              ⟨defaultBody, afterDefault, defaultResult⟩ |
              ⟨failure, rejected, defaultResult⟩
            · have defaultReply := MatchInternals.optionalDefaultBody_validFor
                expressionValueValid patternValueValid yulValueValid statement
                  statementContract.validFor
                  statementContract.preservesTokenWindow.preservesTokensOnSuccess
                  afterCases casesReply.2.1
              rw [defaultResult] at defaultReply
              rcases (symbol_ordinary .rightBrace .statement) afterDefault with
                ⟨closing, afterClosing, closingResult⟩ |
                ⟨failure, rejected, closingResult⟩
              · rcases MatchInternals.finishMatchStatement_ordinary marker
                    scrutinees opening cases defaultBody closing afterClosing with
                  ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
                · exact Or.inl ⟨value, final, by
                    simp only [matchStatement, bind, markerResult, valuesResult,
                      requiredResult, openingResult, casesResult, defaultResult,
                      closingResult]
                    simpa only [MatchInternals.finishMatchStatement, bind] using
                      finished⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [matchStatement, bind, markerResult, valuesResult,
                      requiredResult, openingResult, casesResult, defaultResult,
                      closingResult]
                    simpa only [MatchInternals.finishMatchStatement, bind] using
                      finished⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [matchStatement, bind, markerResult, valuesResult,
                    requiredResult, openingResult, casesResult, defaultResult,
                    closingResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [matchStatement, bind, markerResult, valuesResult,
                  requiredResult, openingResult, casesResult, defaultResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [matchStatement, bind, markerResult, valuesResult,
                requiredResult, openingResult, casesResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [matchStatement, bind, markerResult, valuesResult,
              requiredResult, openingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [matchStatement, bind, markerResult, valuesResult,
            requiredResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [matchStatement, bind, markerResult, valuesResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [matchStatement, bind, markerResult]⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchStatementFuelContractProperties
/-! Complete fuel contract for canonical Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Adequate outer fuel excludes every complete-match invariant. -/
theorem matchStatement_ne_invariant_of_fuels
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    {caseValueValid : SourceFile → MatchCase → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel caseFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract : FuelElementTotalityContract
      expression expressionFuel)
    (caseContract : MatchInternals.FuelCaseListTotalityContract caseValueValid
      (fun input => MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) caseFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      MatchInternals.matchStatementFuel expressionFuel caseFuel
        statementFuel)
    (error : ParserInvariantError) :
    matchStatement statement expression pattern input ≠ .invariant error := by
  intro failed
  rcases matchStatement_ordinary_of_fuels expressionValueValid
      patternValueValid yulValueValid statement expression pattern
      statementFuel expressionFuel caseFuel statementContract
      statementStrict expressionContract caseContract input inputValid
      adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
Package production `match` syntax, including its dynamically fueled case
loop, under the independent expression, pattern, and statement bounds.
-/
theorem matchStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (TermInternals.RecursiveStatementValid statementValid)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality : FuelElementTotalityContract
      expression expressionFuel)
    (patternSyntax :
      TermInternals.PatternParserContract statementValid pattern)
    (patternTotality : FuelElementTotalityContract pattern patternFuel) :
    TermInternals.FuelStatementTotalityContract
      (TermInternals.RecursiveStatementValid statementValid)
      (matchStatement statement expression pattern)
      (MatchInternals.matchStatementFuel expressionFuel
        (Nat.min (patternFuel + 1) (statementFuel + 3))
        statementFuel) := by
  let caseContract :=
    MatchInternals.matchCases_production_fuelTotalityContract
      (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement pattern statementFuel patternFuel statementContract
      statementStrict patternSyntax.validFor patternTotality
  exact {
    validFor := matchStatement_validFor (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement expression pattern statementContract.validFor
      statementContract.preservesTokenWindow expressionSyntax.validFor
      expressionSyntax.preservesTokensOnSuccess patternSyntax.validFor
      patternSyntax.preservesTokenWindow
      patternSyntax.cursorMonotoneOnSuccess
    preservesTokenWindow := matchStatement_preservesTokenWindow statement
      expression pattern statementContract.preservesTokenWindow
      expressionSyntax.preservesTokenWindow patternSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess :=
      matchStatement_cursorMonotoneOnSuccess statement expression pattern
    startsAtCurrentTokenOnSuccess :=
      matchStatement_startsAtCurrentTokenOnSuccess statement expression pattern
    ordinary := matchStatement_ordinary_of_fuels
      (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement expression pattern statementFuel expressionFuel
      (Nat.min (patternFuel + 1) (statementFuel + 3)) statementContract
      statementStrict expressionTotality caseContract
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ControlForFuelTotalityProperties
/-! Fuel-aware totality for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
All `for` header components remain ordinary below their fixed expression
fuel. Six guaranteed strict prefix steps reach the recursive body.
-/
theorem forStatement_ordinary_of_fuels
    {itemValid : SourceFile → ForItem → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (initializerContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .semicolon)
        expressionFuel)
    (postContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .rightParen)
        expressionFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 7)) :
    (∃ value next,
      forStatement statement expression input = .ok value next) ∨
    (∃ failure next,
      forStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 7))
  have statementBudget : input.remainingCount < statementFuel + 7 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 7))
  rcases (keyword_ordinary .forKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .forKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .forKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .forKw) .statement
        (· == .keyword .forKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 6 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    rcases (symbol_ordinary .leftParen .statement) afterMarker with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .statement afterMarker
      rw [openingResult] at openingWindow
      have openingProgress : afterMarker.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .statement
          (· == .symbol .leftParen) openingResult
      have expressionAfterOpening :
          afterOpening.remainingCount < expressionFuel :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      have statementAfterOpening :
          afterOpening.remainingCount < statementFuel + 5 :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      rcases initializerContract.ordinary afterOpening openingReply.2.1
          expressionAfterOpening with
        ⟨initializer, afterInitializer, initializerResult⟩ |
        ⟨failure, rejected, initializerResult⟩
      · have initializerReply := initializerContract.validFor afterOpening
          openingReply.2.1
        rw [initializerResult] at initializerReply
        have initializerWindow := initializerContract.preservesTokenWindow
          afterOpening
        rw [initializerResult] at initializerWindow
        have initializerCursor := initializerContract.cursorMonotoneOnSuccess
          afterOpening initializer afterInitializer initializerResult
        have expressionAfterInitializer :
            afterInitializer.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le initializerWindow.2
            initializerCursor expressionAfterOpening
        have statementAfterInitializer :
            afterInitializer.remainingCount < statementFuel + 5 :=
          remainingCount_lt_of_cursor_le initializerWindow.2
            initializerCursor statementAfterOpening
        rcases (symbol_ordinary .semicolon .statement) afterInitializer with
          ⟨sep1, afterSep1, sep1Result⟩ |
          ⟨failure, rejected, sep1Result⟩
        · have sep1Reply := symbol_validFor .semicolon .statement
            afterInitializer initializerReply.2.1
          rw [sep1Result] at sep1Reply
          have sep1Window := symbol_preservesTokenWindow .semicolon .statement
            afterInitializer
          rw [sep1Result] at sep1Window
          have sep1Progress : afterInitializer.cursor < afterSep1.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .semicolon) .statement
              (· == .symbol .semicolon) sep1Result
          have expressionAfterSep1 :
              afterSep1.remainingCount < expressionFuel :=
            remainingCount_lt_of_cursor_le sep1Window.2
              (Nat.le_of_lt sep1Progress) expressionAfterInitializer
          have statementAfterSep1 :
              afterSep1.remainingCount < statementFuel + 4 :=
            remainingCount_lt_after_strict_progress sep1Reply.2.1
              sep1Window.2 sep1Progress statementAfterInitializer
          rcases expressionContract.ordinary afterSep1 sep1Reply.2.1
              expressionAfterSep1 with
            ⟨condition, afterCondition, conditionResult⟩ |
            ⟨failure, rejected, conditionResult⟩
          · have conditionReply := expressionContract.validFor afterSep1
              sep1Reply.2.1
            rw [conditionResult] at conditionReply
            have conditionWindow := expressionContract.preservesTokenWindow
              afterSep1
            rw [conditionResult] at conditionWindow
            have conditionProgress :=
              expressionContract.cursorLtOnSuccess conditionResult
            have expressionAfterCondition :
                afterCondition.remainingCount < expressionFuel :=
              remainingCount_lt_of_cursor_le conditionWindow.2
                (Nat.le_of_lt conditionProgress) expressionAfterSep1
            have statementAfterCondition :
                afterCondition.remainingCount < statementFuel + 3 :=
              remainingCount_lt_after_strict_progress conditionReply.2.1
                conditionWindow.2 conditionProgress statementAfterSep1
            rcases (symbol_ordinary .semicolon .statement) afterCondition with
              ⟨sep2, afterSep2, sep2Result⟩ |
              ⟨failure, rejected, sep2Result⟩
            · have sep2Reply := symbol_validFor .semicolon .statement
                afterCondition conditionReply.2.1
              rw [sep2Result] at sep2Reply
              have sep2Window := symbol_preservesTokenWindow .semicolon
                .statement afterCondition
              rw [sep2Result] at sep2Window
              have sep2Progress : afterCondition.cursor < afterSep2.cursor :=
                acceptToken_cursor_lt_onSuccess (.symbol .semicolon)
                  .statement (· == .symbol .semicolon) sep2Result
              have expressionAfterSep2 :
                  afterSep2.remainingCount < expressionFuel :=
                remainingCount_lt_of_cursor_le sep2Window.2
                  (Nat.le_of_lt sep2Progress) expressionAfterCondition
              have statementAfterSep2 :
                  afterSep2.remainingCount < statementFuel + 2 :=
                remainingCount_lt_after_strict_progress sep2Reply.2.1
                  sep2Window.2 sep2Progress statementAfterCondition
              rcases postContract.ordinary afterSep2 sep2Reply.2.1
                  expressionAfterSep2 with
                ⟨post, afterPost, postResult⟩ |
                ⟨failure, rejected, postResult⟩
              · have postReply := postContract.validFor afterSep2
                    sep2Reply.2.1
                rw [postResult] at postReply
                have postWindow := postContract.preservesTokenWindow afterSep2
                rw [postResult] at postWindow
                have postCursor := postContract.cursorMonotoneOnSuccess
                  afterSep2 post afterPost postResult
                have statementAfterPost :
                    afterPost.remainingCount < statementFuel + 2 :=
                  remainingCount_lt_of_cursor_le postWindow.2 postCursor
                    statementAfterSep2
                rcases (symbol_ordinary .rightParen .statement) afterPost with
                  ⟨closing, afterClosing, closingResult⟩ |
                  ⟨failure, rejected, closingResult⟩
                · have closingReply := symbol_validFor .rightParen .statement
                      afterPost postReply.2.1
                  rw [closingResult] at closingReply
                  have closingWindow := symbol_preservesTokenWindow
                    .rightParen .statement afterPost
                  rw [closingResult] at closingWindow
                  have closingProgress :
                      afterPost.cursor < afterClosing.cursor :=
                    acceptToken_cursor_lt_onSuccess (.symbol .rightParen)
                      .statement (· == .symbol .rightParen) closingResult
                  have blockAdequate :
                      afterClosing.remainingCount < statementFuel + 1 :=
                    remainingCount_lt_after_strict_progress closingReply.2.1
                      closingWindow.2 closingProgress statementAfterPost
                  rcases blockContract.ordinary afterClosing closingReply.2.1
                      blockAdequate with
                    ⟨body, final, bodyResult⟩ |
                    ⟨failure, rejected, bodyResult⟩
                  · exact Or.inl ⟨{
                        span := SourceSpan.cover marker.span body.span
                        value := .forLoop
                          (SourceSpan.cover opening.span closing.span)
                          initializer condition post body
                      }, final, by
                        simp only [forStatement, bind, markerResult,
                          openingResult, initializerResult, sep1Result,
                          conditionResult, sep2Result, postResult,
                          closingResult, bodyResult, pure]⟩
                  · exact Or.inr ⟨failure, rejected, by
                      simp only [forStatement, bind, markerResult,
                        openingResult, initializerResult, sep1Result,
                        conditionResult, sep2Result, postResult,
                        closingResult, bodyResult]⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [forStatement, bind, markerResult,
                      openingResult, initializerResult, sep1Result,
                      conditionResult, sep2Result, postResult, closingResult]⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [forStatement, bind, markerResult, openingResult,
                    initializerResult, sep1Result, conditionResult,
                    sep2Result, postResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [forStatement, bind, markerResult, openingResult,
                  initializerResult, sep1Result, conditionResult, sep2Result]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [forStatement, bind, markerResult, openingResult,
                initializerResult, sep1Result, conditionResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [forStatement, bind, markerResult, openingResult,
              initializerResult, sep1Result]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [forStatement, bind, markerResult, openingResult,
            initializerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forStatement, bind, markerResult]⟩

/-- Adequate header and body fuel exclude every `for` invariant. -/
theorem forStatement_ne_invariant_of_fuels
    {itemValid : SourceFile → ForItem → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (initializerContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .semicolon)
        expressionFuel)
    (postContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .rightParen)
        expressionFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 7))
    (error : ParserInvariantError) :
    forStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases forStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel initializerContract postContract expressionContract
        blockContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.ControlForFuelContractProperties
/-! Complete recursive-fuel contract for canonical Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem forStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (forStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 7)) := by
  let initializerContract :=
    ControlInternals.forItems_fuelTotalityContract expression .semicolon
      expressionFuel expressionSyntax expressionTotality
  let postContract :=
    ControlInternals.forItems_fuelTotalityContract expression .rightParen
      expressionFuel expressionSyntax expressionTotality
  let blockContract := coreBlock_fuelTotalityContract statement .require
    statementFuel statementContract statementStrict
      (fun _ _ valid => valid.span_valid)
  exact {
    validFor := forStatement_validFor (Expr.ValidFor statementValid)
      patternValueValid YulStmt.ValidFor statement expression
        statementContract.validFor statementContract.preservesTokensOnSuccess
        expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
          expressionSyntax.preservesTokenWindow
            expressionSyntax.cursorLtOnSuccess
              expressionSyntax.startsAtCurrentTokenOnSuccess
    preservesTokenWindow := forStatement_preservesTokenWindow statement
      expression statementContract.preservesTokenWindow
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess := forStatement_cursorMonotoneOnSuccess statement
      expression expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      forStatement_startsAtCurrentTokenOnSuccess statement expression
    ordinary := forStatement_ordinary_of_fuels statement expression
      statementFuel expressionFuel initializerContract postContract
        expressionTotality blockContract
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.StatementLayerFuelTotalityProperties
/-! Fuel totality for the complete ordered Core statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/--
The fallback, complete `match`, and recursive block are the three tight
constraints on the ordered statement layer. All other branches support this
common smaller bound.
-/
def statementLayerFuel
    (statementFuel expressionFuel patternFuel : Nat) : Nat :=
  Nat.min expressionFuel
    (Nat.min
      (MatchInternals.matchStatementFuel expressionFuel
        (Nat.min (patternFuel + 1) (statementFuel + 3)) statementFuel)
      (statementFuel + 1))

private theorem recognized_sameFuel_contract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (fuel : Nat)
    (primaryContract : FuelStatementTotalityContract
      valueValid primary fuel)
    (fallbackContract : FuelStatementTotalityContract
      valueValid fallback fuel) :
    FuelStatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback) fuel := by
  simpa using recognizedStatementOrFallback_fuelTotalityContract
    primary fallback fuel fuel primaryContract fallbackContract

private theorem stateChoice_sameFuel_contract
    {valueValid : SourceFile → Statement → Prop}
    (condition : State → Bool) (first second : Parser Statement) (fuel : Nat)
    (firstContract : FuelStatementTotalityContract valueValid first fuel)
    (secondContract : FuelStatementTotalityContract valueValid second fuel) :
    FuelStatementTotalityContract valueValid
      (fun input => if condition input then first input else second input)
      fuel := by
  simpa using stateChoice_fuelTotalityContract condition first second fuel fuel
    firstContract secondContract

/-- Every branch of `statementLayer` is ordinary at one reusable fuel bound. -/
theorem statementLayer_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementFuel expressionFuel patternFuel : Nat)
    (statementContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      nestedStatement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      nestedStatement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel)
    (patternSyntax : PatternParserContract statementValid pattern)
    (patternTotality : FuelElementTotalityContract pattern patternFuel) :
    FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (statementLayer nestedStatement expression pattern)
      (statementLayerFuel statementFuel expressionFuel patternFuel) := by
  let patternValid := Pattern.ValidFor (Expr.ValidFor statementValid)
  let commonFuel := statementLayerFuel statementFuel expressionFuel patternFuel
  let matchFuel := MatchInternals.matchStatementFuel expressionFuel
    (Nat.min (patternFuel + 1) (statementFuel + 3)) statementFuel
  have commonLeExpression : commonFuel ≤ expressionFuel := by
    dsimp only [commonFuel]
    exact Nat.min_le_left _ _
  have commonLeMatch : commonFuel ≤ matchFuel := by
    dsimp only [commonFuel, matchFuel]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have commonLeStatement : commonFuel ≤ statementFuel + 1 := by
    dsimp only [commonFuel]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
  have commonLeControl :
      commonFuel ≤ Nat.min (expressionFuel + 2) (statementFuel + 5) := by
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have commonLeFor :
      commonFuel ≤ Nat.min (expressionFuel + 2) (statementFuel + 7) := by
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have fallbackContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (assignmentOrExpressionStatement expression) commonFuel :=
    (assignmentOrExpressionStatement_fuelTotalityContract patternValid
      YulStmt.ValidFor expression expressionFuel expressionSyntax
      expressionTotality).weaken commonLeExpression
  have letContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (letStatement expression) commonFuel :=
    (letStatement_fuelTotalityContract patternValid expression expressionFuel
      expressionSyntax expressionTotality).weaken (by omega)
  have returnContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (returnStatement expression) commonFuel :=
    (returnStatement_fuelTotalityContract patternValid expression
      expressionFuel expressionSyntax expressionTotality).weaken (by omega)
  have matchContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (matchStatement nestedStatement expression pattern) commonFuel :=
    (matchStatement_fuelTotalityContract nestedStatement expression pattern
      statementFuel expressionFuel patternFuel statementContract
      statementStrict expressionSyntax expressionTotality patternSyntax
      patternTotality).weaken commonLeMatch
  have forContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (forStatement nestedStatement expression) commonFuel :=
    (forStatement_fuelTotalityContract patternValid nestedStatement expression
      statementFuel expressionFuel statementContract statementStrict
      expressionSyntax expressionTotality).weaken commonLeFor
  have whileContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (whileStatement nestedStatement expression) commonFuel :=
    (whileStatement_fuelTotalityContract patternValid nestedStatement
      expression statementFuel expressionFuel statementContract
      statementStrict expressionSyntax expressionTotality).weaken
        commonLeControl
  have ifContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (ifStatement nestedStatement expression) commonFuel :=
    (ifStatement_fuelTotalityContract patternValid nestedStatement expression
      statementFuel expressionFuel statementContract statementStrict
      expressionSyntax expressionTotality).weaken commonLeControl
  have assemblyContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) assemblyStatement commonFuel :=
    assemblyStatement_fuelTotalityContract (Expr.ValidFor statementValid)
      patternValid YulStmt.ValidFor (fun _ _ valid => valid) commonFuel
  have blockContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (blockStatement nestedStatement) commonFuel :=
    (blockStatement_fuelTotalityContract patternValid nestedStatement
      statementFuel statementContract statementStrict).weaken
        commonLeStatement
  have breakContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) breakStatement commonFuel :=
    FuelStatementTotalityContract.ofTotality
      (breakStatement_totalityContract (Expr.ValidFor statementValid)
        patternValid YulStmt.ValidFor) commonFuel
  have continueContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) continueStatement commonFuel :=
    FuelStatementTotalityContract.ofTotality
      (continueStatement_totalityContract (Expr.ValidFor statementValid)
        patternValid YulStmt.ValidFor) commonFuel
  change FuelStatementTotalityContract
    (RecursiveStatementValid statementValid)
    (statementLayer nestedStatement expression pattern) commonFuel
  unfold statementLayer
  apply stateChoice_sameFuel_contract
  · exact recognized_sameFuel_contract _ _ commonFuel letContract
      fallbackContract
  · apply stateChoice_sameFuel_contract
    · exact recognized_sameFuel_contract _ _ commonFuel returnContract
        fallbackContract
    · apply stateChoice_sameFuel_contract
      · exact recognized_sameFuel_contract _ _ commonFuel matchContract
          fallbackContract
      · apply stateChoice_sameFuel_contract
        · exact recognized_sameFuel_contract _ _ commonFuel forContract
            fallbackContract
        · apply stateChoice_sameFuel_contract
          · exact recognized_sameFuel_contract _ _ commonFuel whileContract
              fallbackContract
          · apply stateChoice_sameFuel_contract
            · exact recognized_sameFuel_contract _ _ commonFuel ifContract
                fallbackContract
            · apply stateChoice_sameFuel_contract
              · exact recognized_sameFuel_contract _ _ commonFuel
                  assemblyContract fallbackContract
              · apply stateChoice_sameFuel_contract
                · exact recognized_sameFuel_contract _ _ commonFuel
                    blockContract fallbackContract
                · apply stateChoice_sameFuel_contract
                  · exact recognized_sameFuel_contract _ _ commonFuel
                      breakContract fallbackContract
                  · apply stateChoice_sameFuel_contract
                    · exact recognized_sameFuel_contract _ _ commonFuel
                        continueContract fallbackContract
                    · exact fallbackContract

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.StatementLayerStrictProperties
/-! Strict cursor progress for the complete ordered Core statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem bind_cursor_lt_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

private theorem assignmentOrExpression_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionStrict : ∀ {input final : State} {value : Expr},
      expression input = .ok value final → input.cursor < final.cursor)
    {input final : State} {value : Statement}
    (parsed : assignmentOrExpressionStatement expression input =
      .ok value final) :
    input.cursor < final.cursor := by
  let expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ result => Nat.le_of_lt (expressionStrict result)
  unfold assignmentOrExpressionStatement at parsed
  apply bind_cursor_lt_of_first expressionStrict ?_ parsed
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
      expression expressionCursor)
  intro tail
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalSemicolon_cursorMonotoneOnSuccess
  intro semicolon
  dsimp only
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail <;> by_cases missing : semicolon.isNone
      · simp only [missing, if_true]
        apply Parser.bind_cursorMonotoneOnSuccess
          (emitDiagnostic_cursorMonotoneOnSuccess _)
        intro _
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, Bool.false_eq_true, ↓reduceIte]
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, if_true]
        apply Parser.bind_cursorMonotoneOnSuccess
          (emitDiagnostic_cursorMonotoneOnSuccess _)
        intro _
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, Bool.false_eq_true, ↓reduceIte]
        exact Parser.pure_cursorMonotoneOnSuccess _

private theorem let_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : letStatement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold letStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement); intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess; intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
      expression expressionCursor); intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem return_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : returnStatement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold returnStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .returnKw)
      .statement (· == .keyword .returnKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
      expression expressionCursor); intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem for_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : forStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .forKw)
      .statement (· == .keyword .forKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro opening
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .semicolon
      expressionCursor); intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .rightParen
      expressionCursor); intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem while_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : whileStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold whileStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.contextual .while)
      .statement (·.isContextual .while) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem if_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : ifStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold ifStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .ifKw)
      .statement (· == .keyword .ifKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro thenBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.optionalElseBody_cursorMonotoneOnSuccess statement)
  intro elseBody
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem block_cursor_lt_onSuccess
    (statement : Parser Statement) {input final : State} {value : Statement}
    (parsed : blockStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold blockStatement at parsed
  apply bind_cursor_lt_of_first (coreBlock_cursor_lt_onSuccess statement
    .require) (fun body => Parser.pure_cursorMonotoneOnSuccess _) parsed

/-- Every successful ordered Core statement branch consumes a token. -/
theorem statementLayer_cursor_lt_onSuccess
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (expressionStrict : ∀ {input final : State} {value : Expr},
      expression input = .ok value final → input.cursor < final.cursor)
    {input final : State} {value : Statement}
    (parsed : statementLayer nestedStatement expression pattern input =
      .ok value final) :
    input.cursor < final.cursor := by
  let expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ result => Nat.le_of_lt (expressionStrict result)
  have fallbackStrict : ∀ {start stop : State} {statement : Statement},
      assignmentOrExpressionStatement expression start = .ok statement stop →
        start.cursor < stop.cursor :=
    assignmentOrExpression_cursor_lt_onSuccess expression expressionStrict
  unfold statementLayer at parsed
  dsimp only at parsed
  split at parsed
  · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
      _ _ (let_cursor_lt_onSuccess expression expressionCursor)
        fallbackStrict parsed
  · split at parsed
    · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
        _ _ (return_cursor_lt_onSuccess expression expressionCursor)
          fallbackStrict parsed
    · split at parsed
      · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
          _ _ (matchStatement_cursor_lt_onSuccess nestedStatement expression
            pattern) fallbackStrict parsed
      · split at parsed
        · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
            _ _ (for_cursor_lt_onSuccess nestedStatement expression
              expressionCursor) fallbackStrict parsed
        · split at parsed
          · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
              _ _ (while_cursor_lt_onSuccess nestedStatement expression
                expressionCursor) fallbackStrict parsed
          · split at parsed
            · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                _ _ (if_cursor_lt_onSuccess nestedStatement expression
                  expressionCursor) fallbackStrict parsed
            · split at parsed
              · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                  _ _ assemblyStatement_cursor_lt_onSuccess fallbackStrict
                    parsed
              · split at parsed
                · exact
                    recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                      _ _ (block_cursor_lt_onSuccess nestedStatement)
                        fallbackStrict parsed
                · split at parsed
                  · exact
                      recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                        _ _ breakStatement_cursor_lt_onSuccess fallbackStrict
                          parsed
                  · split at parsed
                    · exact
                        recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                          _ _ continueStatement_cursor_lt_onSuccess
                            fallbackStrict parsed
                    · exact fallbackStrict parsed

end Solcore.Syntax.Parser.TermInternals
end
